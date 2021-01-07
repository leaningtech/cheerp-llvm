//===-- Cheerp/Writer.h - The Cheerp JavaScript generator -----------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2014 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#ifndef _CHEERP_WRITER_H
#define _CHEERP_WRITER_H

#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Cheerp/GlobalDepsAnalyzer.h"
#include "llvm/Cheerp/NameGenerator.h"
#include "llvm/Cheerp/PointerAnalyzer.h"
#include "llvm/Cheerp/Registerize.h"
#include "llvm/Cheerp/SourceMaps.h"
#include "llvm/Cheerp/Utility.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/FormattedStream.h"
#include <set>
#include <map>

namespace cheerp
{

class NewLineHandler
{
private:
	SourceMapGenerator* sourceMapGenerator;
public:
	NewLineHandler(SourceMapGenerator* s):sourceMapGenerator(s)
	{
	}

	friend llvm::raw_ostream& operator<<(llvm::raw_ostream& s, const NewLineHandler& handler)
	{
		s << '\n';
		if(handler.sourceMapGenerator)
			handler.sourceMapGenerator->finishLine();
		return s;
	}

};

/**
 * Black magic to conditionally enable indented output
 */
class ostream_proxy
{
public:
	ostream_proxy( llvm::raw_ostream & s, bool readableOutput = false ) :
		stream(s),
		readableOutput(readableOutput),
		newLine(true),
		indentLevel(0)
	{}

	friend ostream_proxy& operator<<( ostream_proxy & os, char c )
	{
		os.write_indent(c);
		return os;
	}

	friend ostream_proxy& operator<<( ostream_proxy & os, llvm::StringRef s )
	{
		os.write_indent(s);
		return os;
	}

	friend ostream_proxy& operator<<( ostream_proxy & os, const NewLineHandler& handler)
	{
		os.stream << handler;
		os.newLine = true;
		return os;
	}

	template<class T>
	friend typename std::enable_if<
		!std::is_convertible<T&&, llvm::StringRef>::value, // Use this only if T is not convertible to StringRef
		ostream_proxy&>::type operator<<( ostream_proxy & os, T && t )
	{
		if ( os.newLine && os.readableOutput )
			for ( int i = 0; i < os.indentLevel; i++ )
				os.stream << '\t';

		os.stream << std::forward<T>(t);
		os.newLine = false;
		return os;
	}

private:

	// Return true if we are closing a curly bracket, need to unindent by 1.
	bool updateIndent( char c ) {
		if ( c == '{') indentLevel++;
		else if ( c == '}') {indentLevel--; return true; }
		return false;
	}

	// Return true if we are closing a curly, need to unindent by 1.
	bool updateIndent( llvm::StringRef s) {
		if (s.empty() )
			return false;
		bool ans = updateIndent(s.front());
		for (auto it = s.begin()+1; it != s.end(); ++it)
			updateIndent(*it);
		return ans;
	}

	template<class T>
	void write_indent(T && t)
	{
		int oldIndent = indentLevel;
		if (updateIndent( std::forward<T>(t) ) )
			oldIndent--;

		if ( newLine && readableOutput )
			for ( int i = 0; i < oldIndent; i++ )
				stream << '\t';

		stream << std::forward<T>(t);
		newLine = false;
	}

	llvm::raw_ostream & stream;
	bool readableOutput;
	bool newLine;
	int indentLevel;
};

class CheerpWriter
{
private:

	llvm::Module& module;
	llvm::DataLayout targetData;
	const llvm::Function* currentFun;
	const PointerAnalyzer & PA;
	const Registerize & registerize;

	GlobalDepsAnalyzer & globalDeps;
	NameGenerator namegen;
	TypeSupport types;
	std::set<const llvm::GlobalVariable*> compiledGVars;

	// Support for source maps
	SourceMapGenerator* sourceMapGenerator;
	const NewLineHandler NewLine;

	/**
	 * \addtogroup MemFunction methods to handle memcpy, memmove, mallocs and free (and alike)
	 *
	 * @{
	 */

	/**
	 * Compile memcpy and memmove
	 */
	void compileMemFunc(const llvm::Value* dest,
	                    const llvm::Value* srcOrResetVal,
	                    const llvm::Value* size);

	/**
	 * Copy baseSrc into baseDest
	 */
	void compileCopyElement(const llvm::Value* baseDest,
	                        const llvm::Value* baseSrc,
	                        llvm::Type* currentType);

	void compileAllocation(const DynamicAllocInfo& info);
	void compileFree(const llvm::Value* obj);

	/** @} */

	// COMPILE_EMPTY is returned if there is no need to add a ;\n to end the line
	enum COMPILE_INSTRUCTION_FEEDBACK { COMPILE_OK = 0, COMPILE_UNSUPPORTED, COMPILE_EMPTY };

	void handleBuiltinNamespace(const char* identifier, llvm::ImmutableCallSite callV);
	COMPILE_INSTRUCTION_FEEDBACK handleBuiltinCall(llvm::ImmutableCallSite callV, const llvm::Function* f);

	void compilePredicate(llvm::CmpInst::Predicate p);
	void compileOperandForIntegerPredicate(const llvm::Value* v, llvm::CmpInst::Predicate p);

	/**
	 * \addtogroup Pointers Methods to compile pointers
	 * @{
	 */

	/**
	 * Compile an == or != pointer comparison
	 */
	void compileEqualPointersComparison(const llvm::Value* lhs, const llvm::Value* rhs, llvm::CmpInst::Predicate p);

	/**
	 * Writes an access expression (i.e. something like .a3.a1[n].a4, etc.. ) using the given indices
	 */
	void compileAccessToElement(llvm::Type* tp, llvm::ArrayRef< const llvm::Value* > indices);

	/**
	 * Write the offset part of a GEP as a literal or numerical offset
	 */
	void compileOffsetForGEP(llvm::Type* pointerOperandType, llvm::ArrayRef< const llvm::Value* > indices);

	/**
	 * Compile a COMPLETE_OBJECT.
	 * If the given value is a COMPLETE_OBJECT, just invoke compileOperand, otherwise do a promotion
	 */
	void compileCompleteObject(const llvm::Value*, const llvm::Value* offset = nullptr);

	/**
	 * Compile the pointer base.
	 */
	void compilePointerBase(const llvm::Value*, bool forEscapingPointer=false);

	/**
	 * Compile the pointer offset.
	 */
	void compilePointerOffset(const llvm::Value*);

	/**
	 * BYTE_LAYOUT_OFFSET_FULL: Compile the full offset in bytes till the element
	 * BYTE_LAYOUT_OFFSET_STOP_AT_ARRAY: Compile the offset in bytes till the array, if any, containing the element.
	 *                                   The offset into the array will be returned.
         * BYTE_LAYOUT_OFFSET_NO_PRINT: Like BYTE_LAYOUT_OFFSET_STOP_AT_ARRAY, but does not print any code.
	 */
	enum BYTE_LAYOUT_OFFSET_MODE { BYTE_LAYOUT_OFFSET_FULL = 0, BYTE_LAYOUT_OFFSET_STOP_AT_ARRAY, BYTE_LAYOUT_OFFSET_NO_PRINT };
	/**
	 * Compile the offset in bytes from the byte layout base found by recursively traversing BitCasts and GEPs.
	 * If a GEP from a byte layout pointer to an immutable type is contained in an ArrayType we want to construct the typed array
	 * starting from the array itself instead of from the value. This will make it possible to loop backward over the array.
	 */
	const llvm::Value* compileByteLayoutOffset(const llvm::Value* p, BYTE_LAYOUT_OFFSET_MODE offsetMode);

	/**
	 * Find out if a given member of a struct requires the wrapping array
	 */
	bool useWrapperArrayForMember(llvm::StructType* st, uint32_t memberIndex);

	/**
	 * Compile a pointer from a GEP expression, with the given pointer kind
	 */
	void compileGEP(const llvm::User* gepInst, POINTER_KIND kind);
	void compileGEPBase(const llvm::User* gep_inst, bool forEscapingPointer);
	void compileGEPOffset(const llvm::User* gep_inst);

	/**
	 * Compile a pointer with the specified kind
	 */
	void compilePointerAs(const llvm::Value* p, POINTER_KIND kind)
	{
		assert(p->getType()->isPointerTy());

		if(kind == COMPLETE_OBJECT)
		{
			compileCompleteObject(p);
		}
		else if (llvm::isa<llvm::ConstantPointerNull>(p))
		{
			stream << "nullObj";
		}
		else if (PA.getConstantOffsetForPointer(p))
		{
			stream << "{d:";
			compilePointerBase(p, true);
			stream << ",o:";
			compilePointerOffset(p);
			stream << "}";
		}
		else
		{
			assert(PA.getPointerKind(p) == REGULAR || PA.getPointerKind(p) == BYTE_LAYOUT);
			compileOperand(p);
		}
	}

	/**
	 * Compile a (possibly dynamic) downcast
	 */
	void compileDowncast(llvm::ImmutableCallSite callV);

	/** @} */

	void compileConstantExpr(const llvm::ConstantExpr* ce);
	void compileMethodArgs(llvm::User::const_op_iterator it, llvm::User::const_op_iterator itE, llvm::ImmutableCallSite);
	COMPILE_INSTRUCTION_FEEDBACK compileTerminatorInstruction(const llvm::TerminatorInst& I);
	COMPILE_INSTRUCTION_FEEDBACK compileNotInlineableInstruction(const llvm::Instruction& I);
	COMPILE_INSTRUCTION_FEEDBACK compileInlineableInstruction(const llvm::Instruction& I);

	void compileSignedInteger(const llvm::Value* v);
	void compileUnsignedInteger(const llvm::Value* v);

	void compileMethod(const llvm::Function& F);
	void compileGlobal(const llvm::GlobalVariable& G);
	void compileNullPtrs();
	void compileCreateClosure();
	void compileHandleVAArg();
	/**
	 * This method supports both ConstantArray and ConstantDataSequential
	 */
	void compileConstantArrayMembers(const llvm::Constant* C);

	/**
	 * Methods implemented in types.cpp
	 */
	enum COMPILE_TYPE_STYLE { LITERAL_OBJ=0, THIS_OBJ };
	void compileTypedArrayType(llvm::Type* t);
	void compileTypeImpl(llvm::Type* t, COMPILE_TYPE_STYLE style);
	void compileType(llvm::Type* t, COMPILE_TYPE_STYLE style);
	uint32_t compileClassTypeRecursive(const std::string& baseName, llvm::StructType* currentType, uint32_t baseCount);
	void compileClassType(llvm::StructType* T);
	void compileArrayClassType(llvm::StructType* T);
	void compileArrayPointerType();

	/**
	 * Methods implemented in opcodes.cpp
	 */
	void compileIntegerComparison(const llvm::Value* lhs, const llvm::Value* rhs, llvm::CmpInst::Predicate p);
	void compilePtrToInt(const llvm::Value* v);
	void compileSubtraction(const llvm::Value* lhs, const llvm::Value* rhs);

	static uint32_t getMaskForBitWidth(int width)
	{
		return (1 << width) - 1;
	}

	//JS interoperability support
	void compileClassesExportedToJs();
public:
	ostream_proxy stream;
	CheerpWriter(llvm::Module& m, llvm::raw_ostream& s, cheerp::PointerAnalyzer & PA, cheerp::Registerize & registerize,
	             cheerp::GlobalDepsAnalyzer & gda, SourceMapGenerator* sourceMapGenerator, bool ReadableOutput, bool NoRegisterize):
		module(m),targetData(&m),currentFun(NULL),PA(PA),registerize(registerize),globalDeps(gda),
		namegen(m, globalDeps, registerize, PA, ReadableOutput),types(m, globalDeps.classesWithBaseInfo()),
		sourceMapGenerator(sourceMapGenerator),NewLine(sourceMapGenerator),
		stream(s, ReadableOutput)
	{
	}
	void makeJS();
	void compileBB(const llvm::BasicBlock& BB, const std::map<const llvm::BasicBlock*, uint32_t>& blocksMap);
	void compileConstant(const llvm::Constant* c);
	void compileOperand(const llvm::Value* v);
	void compilePHIOfBlockFromOtherBlock(const llvm::BasicBlock* to, const llvm::BasicBlock* from);
};

}
#endif
