//===-- CheerpWriter.cpp - The Cheerp JavaScript generator -------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2019 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#include <cxxabi.h>
#include "Relooper.h"
#include "CFGStackifier.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Cheerp/Utility.h"
#include "llvm/Cheerp/Writer.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/Path.h"

using namespace llvm;
using namespace std;
using namespace cheerp;

//De-comment this to debug the pointer kind of every function
//#define CHEERP_DEBUG_POINTERS

//De-comment this to debug the source map generation
//#define CHEERP_DEBUG_SOURCE_MAP

class CheerpRenderInterface: public RenderInterface
{
private:
	CheerpWriter* writer;
	StringRef labelName;
	const NewLineHandler& NewLine;
	bool asmjs;
	void renderCondition(const BasicBlock* B, int branchId, CheerpWriter::PARENT_PRIORITY parentPrio, bool booleanInvert);
public:
	CheerpRenderInterface(CheerpWriter* w, StringRef labelName, const NewLineHandler& n, bool asmjs=false):writer(w),labelName(labelName),NewLine(n),asmjs(asmjs)
	{
	}
	void renderBlock(const BasicBlock* BB);
	void renderLabelForSwitch(int labelId);
	void renderSwitchOnLabel(IdShapeMap& idShapeMap);
	void renderCaseOnLabel(int labelId);
	void renderSwitchBlockBegin(const SwitchInst* switchInst, BlockBranchMap& branchesOut);
	void renderCaseBlockBegin(const BasicBlock* caseBlock, int branchId);
	void renderDefaultBlockBegin(bool empty = false);
	void renderIfBlockBegin(const BasicBlock* condBlock, int branchId, bool first, int labelId = 0);
	void renderIfBlockBegin(const BasicBlock* condBlock, const vector<int>& branchId, bool first, int labelId = 0);
	void renderElseBlockBegin();
	void renderIfBlockEnd(bool labelled = false);
	void renderBlockEnd(bool empty = false);
	void renderBlockPrologue(const BasicBlock* blockTo, const BasicBlock* blockFrom);
	void renderWhileBlockBegin();
	void renderWhileBlockBegin(int labelId);
	void renderDoBlockBegin();
	void renderDoBlockBegin(int labelId);
	void renderDoBlockEnd();
	void renderBlockBegin(int labelId);
	void renderBreak();
	void renderBreak(int labelId);
	void renderContinue();
	void renderContinue(int labelId);
	void renderLabel(int labelId);
	void renderIfOnLabel(int labelId, bool first);
};

std::pair<std::string, std::string> CheerpWriter::getBuiltinClassAndFunc(const char* identifier)
{
	int status =0;
	char* const demangledName = abi::__cxa_demangle(identifier, NULL, NULL, &status);
	// Find the opening parenthesis
	char* parenOpen = demangledName;
	while(*parenOpen != '(')
		parenOpen++;

	// Remove the template data
	auto skipTemplates = [](char* nameEnd) -> char*
	{
		nameEnd--;
		if(*nameEnd != '>')
			return nameEnd+1;
		uint32_t templateCount = 1;
		do
		{
			nameEnd--;
			if(*nameEnd == '>')
				templateCount++;
			else if(*nameEnd == '<')
				templateCount--;
		}
		while(templateCount);
		return nameEnd;
	};

	// We will have something like "{retType ,}client::(type{<>,}::)+"
	std::vector<std::string> scopes;
	char* cur = parenOpen;
	bool lastScope = false;
	while(!lastScope)
	{
		char* nameEnd = skipTemplates(cur);
		char* nameStart = nameEnd - 1;
		while(1)
		{
			if(nameStart == demangledName)
			{
				scopes.emplace_back(nameStart, nameEnd);
				lastScope = true;
				break;
			}
			else if(*nameStart == ' ')
			{
				scopes.emplace_back(nameStart+1, nameEnd);
				lastScope = true;
				break;
			}
			else if(*nameStart == ':')
			{
				scopes.emplace_back(nameStart+1, nameEnd);
				nameStart--;
				assert(*nameStart == ':');
				break;
			}
			nameStart--;
		}
		cur = nameStart;
	}

	free(demangledName);

	assert(scopes.back() == "client");
	assert(scopes.size() == 2 || scopes.size() == 3);

	if(scopes.size() == 2 || scopes[0] == scopes[1])
	{
		// No class is present
		return std::make_pair(std::string(), std::move(scopes[0]));
	}
	else
	{
		return std::make_pair(std::move(scopes[1]), std::move(scopes[0]));
	}
}
void CheerpWriter::handleBuiltinNamespace(const char* identifier, llvm::ImmutableCallSite callV)
{
	assert(callV.getCalledFunction());
	std::string classNameStr;
	std::string funcNameStr;
	std::tie(classNameStr, funcNameStr) = getBuiltinClassAndFunc(identifier);
	StringRef className(classNameStr);
	StringRef funcName(funcNameStr);

	bool isClientStatic = callV.getCalledFunction()->hasFnAttribute(Attribute::Static);

	//The first arg should be the object
	if(funcName.startswith("get_"))
	{
		//Getter
		assert(callV.arg_size()==1);
		if(className.empty())
		{
			llvm::report_fatal_error(Twine("Unexpected getter without class: ", StringRef(identifier)), false);
			return;
		}

		compileOperand(callV.getArgument(0), HIGHEST);
		stream << '.' << funcName.drop_front(4);
	}
	else if(funcName.startswith("set_"))
	{
		//Setter
		if(className.empty())
		{
			llvm::report_fatal_error(Twine("Unexpected setter without class: ", StringRef(identifier)), false);
			return;
		}

		compileOperand(callV.getArgument(0), HIGHEST);
		if(funcName.size() == 4)
		{
			// Generic setter
			assert(callV.arg_size()==3);
			stream << '[';
			compileOperand(callV.getArgument(1), LOWEST);
			stream << "]=";
			compileOperand(callV.getArgument(2), LOWEST);
		}
		else
		{
			assert(callV.arg_size()==2);
			stream << '.' << funcName.drop_front(4) <<  '=';
			compileOperand(callV.getArgument(1), LOWEST);
		}
	}
	else if(funcName == StringRef("operator[]"))
	{
		// operator[]
		if(className.empty())
		{
			llvm::report_fatal_error(Twine("Unexpected operator[] without class: ", StringRef(identifier)), false);
			return;
		}
		assert(callV.arg_size()==2);
		compileOperand(callV.getArgument(0), HIGHEST);
		stream << '[';
		compileOperand(callV.getArgument(1), LOWEST);
		stream << ']';
	}
	else
	{
		User::const_op_iterator it = callV.arg_begin();

		//Regular call
		if(!className.empty())
		{
			if(isClientStatic)
				stream << className;
			else if(callV.arg_empty())
			{
				llvm::report_fatal_error(Twine("At least 'this' parameter was expected: ",
					StringRef(identifier)), false);
				return;
			}
			else
			{
				compileOperand(*it, HIGHEST);
				++it;
			}
			stream << '.';
		}
		stream << funcName;
		compileMethodArgs(it,callV.arg_end(), callV, /*forceBoolean*/ true);
	}
}

void CheerpWriter::compileCopyElement(const Value* baseDest,
                                      const Value* baseSrc,
                                      Type* currentType)
{
	switch(currentType->getTypeID())
	{
		case Type::IntegerTyID:
		case Type::FloatTyID:
		case Type::DoubleTyID:
		case Type::PointerTyID:
		{
			compileCompleteObject(baseDest, nullptr);
			stream << '=';
			compileCompleteObject(baseSrc, nullptr);
			stream << ';' << NewLine;
			break;
		}
		case Type::ArrayTyID:
		case Type::StructTyID:
		{
			if(TypeSupport::hasByteLayout(currentType))
			{
				uint64_t typeSize = targetData.getTypeAllocSize(currentType);
				stream << "var __tmp__=new Int8Array(";
				compilePointerBase(baseDest);
				stream << ".buffer,";
				compilePointerOffset(baseDest, LOWEST);
				stream << ',' << typeSize << ");" << NewLine;
				stream << "__tmp__.set(";
				stream << "new Int8Array(";
				compilePointerBase(baseSrc);
				stream << ".buffer,";
				compilePointerOffset(baseSrc, LOWEST);
				stream << ',' << typeSize << "));" << NewLine;
				break;
			}
			// Fallthrough if not byte layout
		}
		default:
			llvm::errs() << "Support type in copy ";
			currentType->dump();
			llvm::errs() << '\n';
	}
}

void CheerpWriter::compileDowncast( ImmutableCallSite callV )
{
	assert( callV.arg_size() == 2 );
	assert( callV.getCalledFunction() && callV.getCalledFunction()->getIntrinsicID() == Intrinsic::cheerp_downcast);

	POINTER_KIND result_kind = PA.getPointerKind(callV.getInstruction());
	const Value * src = callV.getArgument(0);
	const Value * offset = callV.getArgument(1);

	Type* t=src->getType()->getPointerElementType();

	if(TypeSupport::isClientType(t) || (isa<ConstantInt>(offset) && cast<ConstantInt>(offset)->isNullValue()))
	{
		if(result_kind == SPLIT_REGULAR)
		{
			compilePointerBase(src);
			stream << ';' << NewLine;
			stream << namegen.getSecondaryName(callV.getInstruction()) << '=';
			compilePointerOffset(src, LOWEST);
		}
		else
			compilePointerAs(src, result_kind);
	}
	else
	{
		//Do a runtime downcast
		if(result_kind == SPLIT_REGULAR)
		{
			compileCompleteObject(src);
			stream << ".o-";
			compileOperand(offset, HIGHEST);
			stream << ";" << NewLine;
			stream << namegen.getName(callV.getInstruction()) << '=';
			compileCompleteObject(src);
			stream << ".a";
		}
		else if(result_kind == REGULAR)
		{
			stream << "{d:";
			compileCompleteObject(src);
			stream << ".a,o:";
			compileCompleteObject(src);

			stream << ".o-";
			compileOperand(offset, HIGHEST);
			stream << '}';
		}
		else if(result_kind == RAW)
		{
			stream << '(';
			compileOperand(src, ADD_SUB);
			stream  << '+';
			compileOperand(offset, ADD_SUB);
			stream << "|0)";
		}
		else
		{
			compileCompleteObject(src);
			stream << ".a[";
			compileCompleteObject(src);
			stream << ".o-";
			compileOperand(offset, HIGHEST);
			stream << ']';
		}
	}
}

void CheerpWriter::compileVirtualcast( ImmutableCallSite callV )
{
	assert( callV.arg_size() == 2 );
	assert( callV.getCalledFunction() && callV.getCalledFunction()->getIntrinsicID() == Intrinsic::cheerp_virtualcast);

	POINTER_KIND result_kind = PA.getPointerKind(callV.getInstruction());
	const Value * src = callV.getArgument(0);
	const Value * offset = callV.getArgument(1);

      if(result_kind == SPLIT_REGULAR)
      {
            compileCompleteObject(src);
            stream << ".a;" << NewLine;
            stream << namegen.getSecondaryName(callV.getInstruction()) << '=';
            compileOperand(offset, HIGHEST);
      }
      else if(result_kind == REGULAR)
      {
            stream << "{d:";
            compileCompleteObject(src);
            stream << ".a,o:";
            compileOperand(offset, HIGHEST);
            stream << '}';
      }
      else if(result_kind == RAW)
      {
            stream << '(';
            compileOperand(src, ADD_SUB);
            stream  << '+';
            compileOperand(offset, ADD_SUB);
            stream << "|0)";
      }
      else
      {
            compileCompleteObject(src);
            stream << ".a[";
            compileOperand(offset, HIGHEST);
            stream << ']';
      }
}

/* Method that handles memcpy and memmove.
 * Since only immutable types are handled in the backend and we use TypedArray.set to make the copy
 * there is not need to handle memmove in a special way
*/
void CheerpWriter::compileMemFunc(const Value* dest, const Value* src, const Value* size)
{
	Type* destType=dest->getType();
	Type* pointedType = cast<PointerType>(destType)->getElementType();
	if(!(TypeSupport::isTypedArrayType(pointedType, /* forceTypedArray*/ true) || TypeSupport::hasByteLayout(pointedType)))
		llvm::report_fatal_error("Unsupported memory intrinsic, please rebuild the code using an updated version of Cheerp", false);

	uint64_t typeSize = TypeSupport::hasByteLayout(pointedType) ? 1 : targetData.getTypeAllocSize(pointedType);

	bool constantNumElements = false;
	uint32_t numElem = 0;

	if(isa<ConstantInt>(size))
	{
		uint32_t allocatedSize = getIntFromValue(size);
		numElem = (allocatedSize+typeSize-1)/typeSize;
		constantNumElements = true;
	}
	else
	{
		//Compute number of elements at runtime
		stream << "var __numElem__=";
		compileOperand(size,MUL_DIV);
		stream << '/' << typeSize;
		//Make sure to close this if below
		stream << ';' << NewLine;
	}


	// Handle the case for multiple elements, it assumes that we can use TypedArray.set
	if(!constantNumElements)
		stream << "if(__numElem__>1)" << NewLine << '{';
	if(!constantNumElements || numElem>1)
	{
		bool byteLayout = PA.getPointerKind(dest) == BYTE_LAYOUT;
		// The semantics of TypedArray.set is memmove-like, no need to care about direction
		if(byteLayout)
			stream << "(new Int8Array(";
		compilePointerBase(dest);
		if(byteLayout)
			stream << ".buffer))";
		stream << ".set(";
		if(byteLayout)
			stream << "(new Int8Array(";
		compilePointerBase(src);
		if(byteLayout)
			stream << ".buffer))";

		//We need to get a subview of the source
		stream << ".subarray(";
		compilePointerOffset(src, LOWEST);
		stream << ',';
		compilePointerOffset(src, ADD_SUB);
		stream << '+';

		// Use the size
		if(constantNumElements)
			stream << numElem;
		else
			stream << "__numElem__";

		stream << "),";
		compilePointerOffset(dest, LOWEST);
		stream << ");" << NewLine;
	}
	// Handle the single element case, do not assume we have a typed array
	if(!constantNumElements)
		stream << NewLine << "}else if(__numElem__===1)" << NewLine << '{';
	if(!constantNumElements || numElem==1)
	{
		compileCopyElement(dest, src, pointedType);
	}
	if(!constantNumElements)
		stream << NewLine << '}';
}

uint32_t CheerpWriter::compileArraySize(const DynamicAllocInfo & info, bool shouldPrint, bool inBytes)
{
	// We assume parenthesis around this code
	Type * t = info.getCastedType()->getElementType();
	uint32_t typeSize = targetData.getTypeAllocSize(t);
	if(inBytes)
		typeSize = 1;

	bool closeMathImul = false;
	uint32_t numElem = 1;
	if(const Value* numberOfElements = info.getNumberOfElementsArg())
	{
		if(isa<ConstantInt>(numberOfElements))
			numElem = getIntFromValue(numberOfElements);
		else
		{
			assert(shouldPrint);
			if(useMathImul)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::IMUL) << '(';
				closeMathImul = true;
			}
			compileOperand(numberOfElements, LOWEST);
			if(useMathImul)
				stream << ',';
			else
				stream << '*';
		}
	}
	if( !info.sizeIsRuntime() )
	{
		uint32_t allocatedSize = getIntFromValue( info.getByteSizeArg() );
		numElem *= (allocatedSize+typeSize-1);
		if(closeMathImul)
		{
			assert(shouldPrint);
			// We need to multiply before we divide
			stream << numElem;
			stream << ")/" << typeSize << "|0";
		}
		else
		{
			if(shouldPrint)
				stream << (numElem / typeSize);
			else
				return numElem / typeSize;
		}
	}
	else
	{
		assert(shouldPrint);
		compileOperand( info.getByteSizeArg(), closeMathImul?LOWEST:MUL_DIV );
		if(closeMathImul)
			stream << ')';
		stream << '/' << typeSize << "|0";
	}
	assert(shouldPrint);
	return -1;
}

void CheerpWriter::compileAllocation(const DynamicAllocInfo & info)
{
	assert (info.isValidAlloc());

	Type * t = info.getCastedType()->getElementType();

	POINTER_KIND result = PA.getPointerKind(info.getInstruction());
	const ConstantInt* constantOffset = PA.getConstantOffsetForPointer(info.getInstruction());
	bool needsDowncastArray = isa<StructType>(t) && globalDeps.needsDowncastArray(cast<StructType>(t));
	bool needsRegular = result==REGULAR && !constantOffset && !needsDowncastArray;
	assert(result != SPLIT_REGULAR || constantOffset);

	if(needsRegular)
	{
		stream << "{d:";
	}

	// To implement cheerp_reallocate we need to strategies:
	// 1) Immutable types are stored in typed array which cannot be resized, we need to make a new one
	//    and copy the old data over
	// 2) Objects and pointers are stored in a regular array and we can just resize them
	if (info.getAllocType() == DynamicAllocInfo::cheerp_reallocate)
	{
		if (info.useTypedArray() || BYTE_LAYOUT == result)
		{
			stream << "(function(){";
			stream << "var __old__=";
			compilePointerBase(info.getMemoryArg());
			stream << ';' << NewLine;
			//Allocated the new array (created below) in a temporary var
			stream << "var __ret__=";
		}
	}

	
	if (info.useTypedArray())
	{
		stream << "new ";
		compileTypedArrayType(t);
		stream << '(';
		compileArraySize(info, /* shouldPrint */true);
		stream << ')';
	}
	else if(BYTE_LAYOUT == result)
	{
		stream << "new DataView(new ArrayBuffer(((";
		compileArraySize(info, /* shouldPrint */true, /* inBytes */true);
		// Round up the size to make sure that any typed array can be initialized from the buffer
		stream << ")+ 7) & (~7)))";
	}
	else if (info.useCreatePointerArrayFunc() )
	{
		stream << namegen.getBuiltinName(NameGenerator::Builtin::CREATE_POINTER_ARRAY) << "(";
		if (info.getAllocType() == DynamicAllocInfo::cheerp_reallocate)
		{
			compilePointerBase(info.getMemoryArg());
			stream << ',';
			compilePointerBase(info.getMemoryArg());
			stream << ".length,";
		}
		else
		{
			stream << "[],0,";
		}
		compileArraySize(info, /* shouldPrint */true);
		stream << ',';
		if(PA.getPointerKindForStoredType(info.getCastedType())==COMPLETE_OBJECT)
			stream << "null";
		else
			stream << "nullObj";
		stream << ')';
		assert( globalDeps.needCreatePointerArray() );
	}
	else if (info.useCreateArrayFunc() )
	{
		assert( globalDeps.dynAllocArrays().count(t) );

		stream << namegen.getArrayName(t) << '(';
		if (info.getAllocType() == DynamicAllocInfo::cheerp_reallocate)
		{
			compilePointerBase(info.getMemoryArg());
			stream << ',';
			compilePointerBase(info.getMemoryArg());
			stream << ".length,";
			compileArraySize(info, /* shouldPrint */true);
			stream << ')';
		}
		else
		{
			stream << "[],0,";
			compileArraySize(info, /* shouldPrint */true);
			stream << ')';
		}
	}
	else if (!info.sizeIsRuntime() )
	{
		assert( info.getAllocType() != DynamicAllocInfo::cheerp_reallocate );
		// Create a plain array
		
		uint32_t numElem = compileArraySize(info, /* shouldPrint */false);
		
		assert((REGULAR == result || SPLIT_REGULAR == result || BYTE_LAYOUT == result) || numElem <= 1);

		if((REGULAR == result || SPLIT_REGULAR == result) && !needsDowncastArray)
			stream << '[';

		for(uint32_t i = 0; i < numElem;i++)
		{
			compileType(t, LITERAL_OBJ, isInlineable(*info.getInstruction(), PA) || info.getInstruction()->use_empty() ? StringRef() : namegen.getName(info.getInstruction()));
			if((i+1) < numElem)
				stream << ',';
		}

		if(numElem == 0)
			stream << "null";

		if(REGULAR == result || SPLIT_REGULAR == result)
		{
			if(needsDowncastArray)
				stream << ".a";
			else
				stream << ']';
		}
	}
	else
	{
		llvm::errs() << "Allocating type " << *t << "\n";
		llvm::report_fatal_error("Unsupported type in allocation", false);
	}

	if (info.getAllocType() == DynamicAllocInfo::cheerp_reallocate)
	{
		if (info.useTypedArray() || result == BYTE_LAYOUT)
		{
			stream << ';' << NewLine;
			//__ret__ now contains the new array, we need to copy over the data
			if(result == BYTE_LAYOUT)
				stream << "(new Int8Array(__ret__.buffer)).set((new Int8Array(__old__.buffer)).subarray(0, Math.min(__ret__.byteLength,__old__.byteLength)));" << NewLine;
			else
			{
				//The amount of data to copy is limited by the shortest between the old and new array
				stream << "__ret__.set(__old__.subarray(0, Math.min(__ret__.length,__old__.length)));" << NewLine;
			}
			stream << "return __ret__;})()";
		}
	}

	if(needsRegular)
	{
		stream << ",o:0}";
	}
}

CheerpWriter::COMPILE_INSTRUCTION_FEEDBACK CheerpWriter::compileFree(const Value* obj)
{
	// Only arrays of primitives can be backed by the linear heap
	if(!TypeSupport::isTypedArrayType(obj->getType()->getPointerElementType(), /*forceTypedArray*/ true))
		return COMPILE_EMPTY;
	stream << "if(";
	compilePointerBase(obj);
	stream << ".buffer==__heap)__asm.";
	Function* Free = module.getFunction("free");
	if (Free)
		stream << namegen.getName(Free);
	else
		stream << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY);
	stream << '(';
	compilePointerOffset(obj, PARENT_PRIORITY::LOWEST);
	stream << ')';
	return COMPILE_OK;
}

void CheerpWriter::compileEscapedString(raw_ostream& stream, StringRef str, bool forJSON)
{
	for(uint8_t c: str)
	{
		if(c=='\b')
			stream << "\\b";
		else if(c=='\f')
			stream << "\\f";
		else if(c=='\n')
			stream << "\\n";
		else if(c=='\r')
			stream << "\\r";
		else if(c=='\t')
			stream << "\\t";
		else if(c=='\v')
			stream << "\\v";
		else if(c=='"')
			stream << "\\\"";
		else if(c=='\\')
			stream << "\\\\";
		else if(c>=' ' && c<='~')
		{
			// Printable ASCII after we exscluded the previous one
			stream << c;
		}
		else if(forJSON)
		{
			char buf[7];
			snprintf(buf, 7, "\\u%04x", c);
			stream << buf;
		}
		else
		{
			char buf[5];
			snprintf(buf, 5, "\\x%02x", c);
			stream << buf;
		}
	}
}

CheerpWriter::COMPILE_INSTRUCTION_FEEDBACK CheerpWriter::handleBuiltinCall(ImmutableCallSite callV, const Function * func)
{
	assert( callV.isCall() || callV.isInvoke() );
	assert( func );
	assert( (func == callV.getCalledFunction() ) || !(callV.getCalledFunction()) );
	
	bool userImplemented = !func->empty();
	
	ImmutableCallSite::arg_iterator it = callV.arg_begin(), itE = callV.arg_end();
	
	StringRef ident = func->getName();
	unsigned intrinsicId = func->getIntrinsicID();

	StringRef section  = currentFun->getSection();
	bool asmjs = section == StringRef("asmjs");
	const char* Math = "Math.";

	//First handle high priority builtins, they will be used even
	//if an implementation is available from the user
	if(intrinsicId==Intrinsic::memmove ||
		intrinsicId==Intrinsic::memcpy)
	{
		if (!asmjs)
		{
			compileMemFunc(*(it), *(it+1), *(it+2));
			return COMPILE_EMPTY;
		}
		else if (intrinsicId == Intrinsic::memcpy)
		{
			Function* memcpy = module.getFunction("memcpy");
			assert(memcpy);
			stream << namegen.getName(memcpy) << '(';
			compileOperand(*(it),LOWEST);
			stream << "|0,";
			compileOperand(*(it+1),LOWEST);
			stream << "|0,";
			compileOperand(*(it+2),LOWEST);
			stream << "|0)|0";
			return COMPILE_OK;
		}
		else
		{
			assert(intrinsicId == Intrinsic::memmove);
			Function* memmove = module.getFunction("memmove");
			assert(memmove);
			stream << namegen.getName(memmove) << '(';
			compileOperand(*(it),LOWEST);
			stream << "|0,";
			compileOperand(*(it+1),LOWEST);
			stream << "|0,";
			compileOperand(*(it+2),LOWEST);
			stream << "|0)|0";
			return COMPILE_OK;
		}
	}
	else if(intrinsicId==Intrinsic::memset)
	{
		if (asmjs) {
			Function* memset = module.getFunction("memset");
			assert(memset);
			stream << namegen.getName(memset) << '(';
			compileOperand(*(it),LOWEST);
			stream << "|0,";
			compileOperand(*(it+1),LOWEST);
			stream << "|0,";
			compileOperand(*(it+2),LOWEST);
			stream << "|0)|0";
			return COMPILE_OK;
		}
		llvm::report_fatal_error("Unsupported memory intrinsic, please rebuild the code using an updated version of Cheerp", false);
		return COMPILE_EMPTY;
	}
	else if(intrinsicId==Intrinsic::invariant_start)
	{
		//TODO: Try to optimize using this, for now just pass the second arg
		if(!callV.getInstruction()->use_empty())
		{
			compileOperand(*(it+1));
			return COMPILE_OK;
		}
		else
			return COMPILE_EMPTY;
	}
	else if(intrinsicId==Intrinsic::invariant_end)
		return COMPILE_EMPTY;
	else if(intrinsicId==Intrinsic::vastart)
	{
		assert(!asmjs && "vastart instructions in asmjs functions are removed in the AllocaLowering pass");
		compileCompleteObject(*it);
		stream << "={d:arguments,o:" << namegen.getName(currentFun) << ".length}";
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::vaend)
	{
		if (asmjs) return COMPILE_EMPTY;

		compileCompleteObject(*it);
		stream << "=null";
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::vacopy)
	{
		if (asmjs)
		{
			stream << heapNames[HEAP32] << '[';
			compileRawPointer(*it, PARENT_PRIORITY::SHIFT);
			stream << ">>2]=";
			stream << heapNames[HEAP32] << '[';
			compileRawPointer(*(it+1), PARENT_PRIORITY::SHIFT);
			stream << ">>2]|0";
			return COMPILE_OK;
		}
		else
		{
			compileCompleteObject(*it);
			stream << "={d:";
			compileCompleteObject(*(it+1));
			stream << ".d,o:";
			compileCompleteObject(*(it+1));
			stream << ".o}";
			return COMPILE_OK;
		}
	}
	else if(intrinsicId==Intrinsic::cheerp_get_array_len)
	{
		compilePointerBase(*it);
		stream << ".length";
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_virtualcast)
	{
		compileVirtualcast( callV );
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_downcast)
	{
		compileDowncast( callV );
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_downcast_current)
	{
		if (asmjs)
		{
			compileOperand(*it);
		}
		else
		{
			compileCompleteObject(*it);
			stream << ".o|0";
		}
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_upcast_collapsed)
	{
		compilePointerAs(*it, PA.getPointerKind(callV.getInstruction()));
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_cast_user)
	{
		if(callV.getInstruction()->use_empty())
			return COMPILE_EMPTY;

		compileBitCast(callV.getInstruction(), PA.getPointerKind(callV.getInstruction()), HIGHEST);
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_pointer_base)
	{
		compilePointerBase(*it, true);
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_pointer_offset)
	{
		compilePointerOffset(*it, HIGHEST, true);
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_pointer_kind)
	{
		stream << PA.getPointerKind(*it);
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_create_closure)
	{
		assert( globalDeps.needCreateClosure() );

		//We use an helper method to create closures without
		//keeping all local variable around. The helper
		//method is printed on demand depending on a flag
		assert( isa<Function>( callV.getArgument(0) ) );
		POINTER_KIND argKind = PA.getPointerKind( cast<Function>(callV.getArgument(0))->arg_begin() );
		if(argKind == SPLIT_REGULAR)
			stream << namegen.getBuiltinName(NameGenerator::Builtin::CREATE_CLOSURE_SPLIT) << "(";
		else
			stream << namegen.getBuiltinName(NameGenerator::Builtin::CREATE_CLOSURE) << "(";
		compileCompleteObject( callV.getArgument(0) );
		stream << ',';
		if(argKind == SPLIT_REGULAR)
		{
			compilePointerBase( callV.getArgument(1) );
			stream << ',';
			compilePointerOffset( callV.getArgument(1), LOWEST );
		}
		else
			compilePointerAs( callV.getArgument(1), argKind );
		stream << ')';
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_make_complete_object)
	{
		compileCompleteObject(*it);
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_make_regular)
	{
		stream << "{d:";
		compileCompleteObject(*it);
		stream << ",o:";
		compileOperand(*(it+1), LOWEST);
		stream << '}';
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::cheerp_grow_memory)
	{
		stream << namegen.getBuiltinName(NameGenerator::Builtin::GROW_MEM) << '(';
		compileOperand(*it, BIT_OR);
		stream << "|0)|0";
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::flt_rounds)
	{
		// Rounding mode 1: nearest
		stream << '1';
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::ctlz)
	{
		if(asmjs)
			stream << namegen.getBuiltinName(NameGenerator::Builtin::CLZ32);
		else
			stream << Math << "clz32";
		stream << "(";
		compileOperand(*it, LOWEST);
		stream << ')';
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::expect)
	{
		compileOperand(*it);
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::trap && asmjs)
	{
		stream << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY) << "()";
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::stacksave && asmjs)
	{
		stream << namegen.getBuiltinName(NameGenerator::Builtin::STACKPTR);
		return COMPILE_OK;
	}
	else if(intrinsicId==Intrinsic::stackrestore && asmjs)
	{
		stream << namegen.getBuiltinName(NameGenerator::Builtin::STACKPTR) << "=";
		compileOperand(*it, LOWEST);
		return COMPILE_OK;
	}
	else if(cheerp::isFreeFunctionName(ident) || intrinsicId==Intrinsic::cheerp_deallocate)
	{
		if (asmjs || TypeSupport::isAsmJSPointer((*it)->getType()))
		{
			Function* ffree = module.getFunction("free");
			if (!ffree)
				llvm::report_fatal_error("missing free definition");
			if(!asmjs)
				stream << "__asm.";
			stream << namegen.getName(ffree) <<'(';
			compileOperand(*it, PARENT_PRIORITY::BIT_OR);
			stream << "|0)";
			return COMPILE_OK;
		}
		else
		{
			return compileFree(*it);
		}
	}
	else if(ident=="fmod")
	{
		// Handle this internally, C++ does not have float mod operation
		stream << '(';
		compileOperand(*(it), MUL_DIV);
		stream << '%';
		compileOperand(*(it+1), nextPrio(MUL_DIV));
		stream << ')';
		return COMPILE_OK;
	}
	else if(ident=="fmodf")
	{
		stream << "(+";
		compileOperand(*(it), HIGHEST);
		stream << "%+";
		compileOperand(*(it+1), HIGHEST);
		stream << ')';
		return COMPILE_OK;
	}
	else if(useNativeJavaScriptMath || intrinsicId)
	{
		// NOTE: V8 has very strict rules about mixing the double builtins with
		// floats in asm.js, so we need an extra `+` for those
		PARENT_PRIORITY mathPrio = LOWEST;
		bool asmjsFloats = asmjs && useMathFround;
		if(ident=="fabs" || ident=="fabsf" || intrinsicId==Intrinsic::fabs)
		{
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::ABS);
			else
				stream << Math << "abs";
			stream << "(";
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="acos" || ident=="acosf")
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::ACOS);
			else
				stream << Math << "acos";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="asin" || ident=="asinf")
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::ASIN);
			else
				stream << Math << "asin";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="atan" || ident=="atanf")
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::ATAN);
			else
				stream << Math << "atan";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="atan2" || ident=="atan2f")
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::ATAN2);
			else
				stream << Math << "atan2";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ',';
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				stream << '+';
			}
			compileOperand(*(it+1), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="ceil" || ident=="ceilf" || intrinsicId==Intrinsic::ceil)
		{
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::CEIL);
			else
				stream << Math << "ceil";
			stream << "(";
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="cos" || ident=="cosf" || intrinsicId==Intrinsic::cos)
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::COS);
			else
				stream << Math << "cos";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="exp" || ident=="expf" || intrinsicId==Intrinsic::exp)
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::EXP);
			else
				stream << Math << "exp";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="floor" || ident=="floorf" || intrinsicId==Intrinsic::floor)
		{
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FLOOR);
			else
				stream << Math << "floor";
			stream << "(";
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="log" || ident=="logf" || intrinsicId==Intrinsic::log)
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::LOG);
			else
				stream << Math << "log";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="pow" || ident=="powf" || intrinsicId==Intrinsic::pow)
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::POW);
			else
				stream << Math << "pow";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ',';
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				stream << '+';
			}
			compileOperand(*(it+1), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(!asmjs && (ident=="round" || ident=="roundf"))
		{
			stream << Math << "round(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="sin" || ident=="sinf" || intrinsicId==Intrinsic::sin)
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::SIN);
			else
				stream << Math << "sin";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="sqrt" || ident=="sqrtf" || intrinsicId==Intrinsic::sqrt)
		{
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::SQRT);
			else
				stream << Math << "sqrt";
			stream << "(";
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
		else if(ident=="tan" || ident=="tanf")
		{
			if(asmjsFloats && (*it)->getType()->isFloatTy())
				stream << '+';
			if(asmjs)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::TAN);
			else
				stream << Math << "tan";
			stream << "(";
			if(asmjsFloats && (*it)->getType()->isFloatTy())
			{
				mathPrio = HIGHEST;
				stream << '+';
			}
			compileOperand(*(it), mathPrio);
			stream << ')';
			return COMPILE_OK;
		}
	}

	DynamicAllocInfo da(callV, &targetData, forceTypedArrays);
	if (da.isValidAlloc())
	{
		compileAllocation(da);
		return COMPILE_OK;
	}
	if ((func->getIntrinsicID()==Intrinsic::cheerp_allocate || func->getIntrinsicID()==Intrinsic::cheerp_allocate_array) &&
	    (asmjs || TypeSupport::isAsmJSPointer(func->getReturnType())))
	{
		Function* fmalloc = module.getFunction("malloc");
		if (!fmalloc)
			llvm::report_fatal_error("missing malloc definition");
		if(!asmjs)
			stream << "__asm.";
		stream << namegen.getName(fmalloc) << "(";
		compileOperand(*it, PARENT_PRIORITY::LOWEST);
		stream << ")|0";
		return COMPILE_OK;
	}
	else if (asmjs && func->getIntrinsicID()==Intrinsic::cheerp_reallocate && (asmjs || TypeSupport::isAsmJSPointer(func->getReturnType())))
	{
		Function* frealloc = module.getFunction("realloc");
		if (!frealloc)
			llvm::report_fatal_error("missing realloc definition");
		if(!asmjs)
			stream << "__asm.";
		stream << namegen.getName(frealloc) <<'(';
		compileOperand(*it);
		stream << ',';
		compileOperand(*(it+1));
		stream << ")|0";
		return COMPILE_OK;
	}
	else if(ident=="cheerpCreate_ZN6client6StringC2EPKc")
	{
		StringRef str;
		if(llvm::getConstantStringInfo(*it, str))
		{
			stream << '"';
			auto& rawStream = stream.getRawStream();
			uint64_t beginVal = rawStream.tell();
			compileEscapedString(stream.getRawStream(), str, /*forJSON*/false);
			stream.syncRawStream(beginVal);
			stream << '"';
			return COMPILE_OK;
		}
	}

	//If the method is implemented by the user, stop here
	if(userImplemented)
		return COMPILE_UNSUPPORTED;

	if(TypeSupport::isClientFuncName(ident) && !asmjs)
	{
		handleBuiltinNamespace(ident.data(),callV);
		return COMPILE_OK;
	}
	else if(TypeSupport::isClientConstructorName(ident))
	{
		assert(!asmjs && "Unsupported client function for asmjs");
		//Default handling of builtin constructors
		char* typeName;
		int typeLen=strtol(ident.data()+22,&typeName,10);
		//For builtin String, do not use new
		if(strncmp(typeName, "String", 6)!=0)
			stream << "new ";
		stream << StringRef(typeName, typeLen);
		compileMethodArgs(it, itE, callV, /*forceBoolean*/ true);
		return COMPILE_OK;
	}
	return COMPILE_UNSUPPORTED;
}

void CheerpWriter::compilePredicate(CmpInst::Predicate p)
{
	bool asmjs = currentFun->getSection() == StringRef("asmjs");
	switch(p)
	{
		case CmpInst::FCMP_UEQ: //TODO: fix this, if an operand is NaN LLVM expects false,
		case CmpInst::FCMP_OEQ:
		case CmpInst::ICMP_EQ:
			if (asmjs)
				stream << "==";
			else
				stream << "===";
			break;
		case CmpInst::FCMP_UNE: //The undordered case correspond to the usual JS operator
					//See ECMA-262, Section 11.9.6
		case CmpInst::FCMP_ONE:
		case CmpInst::ICMP_NE:
			if (asmjs)
				stream << "!=";
			else
				stream << "!==";
			break;
		case CmpInst::FCMP_OGT: //TODO: fix this, if an operand is NaN LLVM expects false,
		case CmpInst::FCMP_UGT:	//but JS returns undefined. Adding ==true after the whole expression
					//should work
		case CmpInst::ICMP_SGT:
		case CmpInst::ICMP_UGT: //TODO: To support unsigned we need to add casts around the ops
			stream << '>';
			break;
		case CmpInst::FCMP_UGE:
		case CmpInst::FCMP_OGE:
		case CmpInst::ICMP_SGE:
		case CmpInst::ICMP_UGE:
			stream << ">=";
			break;
		case CmpInst::FCMP_OLT: //TODO: fix this, if an operand is NaN LLVM expects false,
		case CmpInst::FCMP_ULT:	//but JS returns undefined. Adding ==true after the whole expression
					//should work
		case CmpInst::ICMP_SLT:
		case CmpInst::ICMP_ULT: //TODO: To support unsigned we need to add casts around the ops
			stream << '<';
			break;
		case CmpInst::FCMP_ULE:
		case CmpInst::FCMP_OLE:
		case CmpInst::ICMP_SLE:
		case CmpInst::ICMP_ULE:
			stream << "<=";
			break;
		default:
			llvm::errs() << "Support predicate " << p << '\n';
	}
}

void CheerpWriter::compileOperandForIntegerPredicate(const Value* v, CmpInst::Predicate p, PARENT_PRIORITY parentPrio)
{
	assert(v->getType()->isIntegerTy());
	if(CmpInst::isSigned(p))
		compileSignedInteger(v, /*forComparison*/ true, parentPrio);
	else if(CmpInst::isUnsigned(p) || !v->getType()->isIntegerTy(32))
	{
		bool asmjs = currentFun->getSection() == StringRef("asmjs");
		compileUnsignedInteger(v, /*forAsmJSComparison*/ asmjs, parentPrio);
	}
	else
		compileSignedInteger(v, /*forComparison*/ true, parentPrio);
}

void CheerpWriter::compileEqualPointersComparison(const llvm::Value* lhs, const llvm::Value* rhs, CmpInst::Predicate p)
{
	StringRef compareString;
	bool asmjs = currentFun->getSection() == StringRef("asmjs");
	StringRef joinString;
	joinString = (p == CmpInst::ICMP_NE) ? "||" : "&&";

	POINTER_KIND lhsKind = PA.getPointerKind(lhs);
	POINTER_KIND rhsKind = PA.getPointerKind(rhs);

	if(lhsKind == RAW)
		assert(asmjs || rhsKind == RAW || dyn_cast<ConstantPointerNull>(rhs));
	if(rhsKind == RAW)
		assert(asmjs || lhsKind == RAW || dyn_cast<ConstantPointerNull>(lhs));

	if (asmjs || lhsKind == RAW || rhsKind == RAW)
		compareString = (p == CmpInst::ICMP_NE) ? "!=" : "==";
	else
		compareString = (p == CmpInst::ICMP_NE) ? "!==" : "===";

	// in asmjs mode all the pointers are RAW pointers
	if(asmjs || lhsKind == RAW || rhsKind == RAW)
	{
		stream << "(";
		compileRawPointer(lhs, PARENT_PRIORITY::BIT_OR);
		stream << "|0)";
		stream << compareString;
		stream << "(";
		compileRawPointer(rhs, PARENT_PRIORITY::BIT_OR);
		stream << "|0)";
	}
	else if((lhsKind == REGULAR || lhsKind == SPLIT_REGULAR || (isGEP(lhs) && cast<User>(lhs)->getNumOperands()==2)) &&
		(rhsKind == REGULAR || rhsKind == SPLIT_REGULAR || (isGEP(rhs) && cast<User>(rhs)->getNumOperands()==2)))
	{
		assert(PA.getPointerKind(lhs) != COMPLETE_OBJECT || !isa<Instruction>(lhs) ||
				isInlineable(*cast<Instruction>(lhs), PA));
		assert(PA.getPointerKind(rhs) != COMPLETE_OBJECT || !isa<Instruction>(rhs) ||
				isInlineable(*cast<Instruction>(rhs), PA));
		if(isa<ConstantPointerNull>(lhs))
			stream << '1';
		else
		{
			compilePointerBase(lhs);
			stream << ".length";
		}
		stream << compareString;
		if(isa<ConstantPointerNull>(rhs))
			stream << '1';
		else
		{
			compilePointerBase(rhs);
			stream << ".length";
		}
		stream << joinString;
		compilePointerBase(lhs);
		stream << compareString;
		compilePointerBase(rhs);
		stream << joinString;
		compilePointerOffset(lhs, COMPARISON);
		stream << compareString;
		compilePointerOffset(rhs, COMPARISON);
	}
	else if(lhsKind == BYTE_LAYOUT || rhsKind == BYTE_LAYOUT)
	{
		assert(PA.getPointerKind(lhs) != COMPLETE_OBJECT);
		assert(PA.getPointerKind(rhs) != COMPLETE_OBJECT);
		compilePointerBase(lhs);
		stream << compareString;
		compilePointerBase(rhs);
		stream << joinString;
		compilePointerOffset(lhs, COMPARISON);
		stream << compareString;
		compilePointerOffset(rhs, COMPARISON);
	}
	else
	{
		assert(PA.getPointerKind(lhs) != BYTE_LAYOUT);
		assert(PA.getPointerKind(rhs) != BYTE_LAYOUT);
		compilePointerAs(lhs, COMPLETE_OBJECT);
		stream << compareString;
		compilePointerAs(rhs, COMPLETE_OBJECT);
	}
}

void CheerpWriter::compileAccessToElement(Type* tp, ArrayRef< const Value* > indices, bool compileLastWrapperArray)
{
	for(uint32_t i=0;i<indices.size();i++)
	{
		// Stop when a byte layout type is found
		if (TypeSupport::hasByteLayout(tp))
			return;
		if(StructType* st = dyn_cast<StructType>(tp))
		{
			assert(isa<ConstantInt>(indices[i]));
			const APInt& index = cast<Constant>(indices[i])->getUniqueInteger();

			stream << '.' << types.getPrefixCharForMember(PA, st, index.getLimitedValue()) << index;
			if((i!=indices.size()-1 || compileLastWrapperArray) && types.useWrapperArrayForMember(PA, st, index.getLimitedValue()))
				stream << "[0]";

			tp = st->getElementType(index.getZExtValue());
		}
		else if(const ArrayType* at = dyn_cast<ArrayType>(tp))
		{
			stream << '[';
			compileOperand(indices[i], LOWEST);
			stream << ']';

			tp = at->getElementType();
		}
		else
		{
			llvm::errs() << "Unexpected type during GEP access " << *tp<< "\n";
			llvm::report_fatal_error("Unsupported code found, please report a bug", false);
		}
	}
}

void CheerpWriter::compileOffsetForGEP(Type* pointerOperandType, ArrayRef< const Value* > indices)
{
	// FIXME This will not compile cause getIndexedType is not const-correct
	/*
	 * Type * tp = GetElementPtrInst::getIndexedType( pointerOperandType, indices.slice(0, indices.size() - 1 ) );
	 */

	Type* tp = GetElementPtrInst::getIndexedType(pointerOperandType->getPointerElementType(),
	                makeArrayRef(const_cast<Value* const*>(indices.begin()),
	                             const_cast<Value* const*>(indices.end() - 1)));

	if(tp->isStructTy())
	{
		// Literal index
		assert(isa<ConstantInt>(indices.back()));
		const ConstantInt* idx = cast<ConstantInt>(indices.back());

		assert(types.useWrapperArrayForMember(PA, cast<StructType>(tp), idx->getZExtValue()));

		stream << '0';
	}
	else
	{
		compileOperand(indices.back());
	}
}

void CheerpWriter::compileCompleteObject(const Value* p, const Value* offset)
{
	// Special handle for undefined pointers
	if(isa<UndefValue>(p))
	{
		compileOperand(p);
		return;
	}
	if(isa<ConstantPointerNull>(p))
	{
		stream << "null";
		if(offset)
		{
			// This will trap anyway, but make sure it's valid code
			stream << "[0]";
		}
		return;
	}

	const llvm::Instruction* I = dyn_cast<Instruction>(p);
	if (I && !isInlineable(*I, PA) &&
		(isGEP(I) || isBitCast(I)) && PA.getPointerKind(I) == COMPLETE_OBJECT)
	{
		stream << namegen.getName(I);
		return;
	}

	bool isOffsetConstantZero = offset == nullptr || (isa<Constant>(offset) && cast<Constant>(offset)->isZeroValue());

	// Direct access path:
	/**
	 * If p comes from a gep, we can just compile that GEP as COMPLETE_OBJECT
	 * That is, instead of a0.a1["a2"] we got a0.a1.a2
	 */
	if(isOffsetConstantZero)
	{
		if(isGEP(p))
		{
			compileGEP(cast<User>(p), COMPLETE_OBJECT, HIGHEST);
			return;
		}
	}

	POINTER_KIND kind = PA.getPointerKind(p);

	if(kind == REGULAR || kind == SPLIT_REGULAR)
	{
		compilePointerBase(p);
		stream << '[';

		const ConstantInt* c1 = dyn_cast_or_null<ConstantInt>(PA.getConstantOffsetForPointer(p));
		const ConstantInt* c2 = dyn_cast_or_null<ConstantInt>(offset);
		if(c1 && c2)
			stream << (c1->getSExtValue() + c2->getSExtValue());
		else if(c1 && c1->isZeroValue() && offset)
			compileOperand(offset, LOWEST);
		else
		{
			compilePointerOffset(p, isOffsetConstantZero ? LOWEST : ADD_SUB);

			if(!isOffsetConstantZero)
			{
				stream << "+";
				compileOperand(offset, ADD_SUB);
				stream << "|0";
			}
		}

		stream << ']';
	}
	else
	{
		compileOperand(p);

		if(!isOffsetConstantZero)
		{
			llvm::errs() << "Can not access a " << kind << " pointer with non zero offset:" << *offset << "\n";
			llvm::report_fatal_error("Unsupported code found, please report a bug", false);
		}
	}
}

void CheerpWriter::compileRawPointer(const Value* p, PARENT_PRIORITY parentPrio, bool forceGEP)
{
	if (isa<ConstantPointerNull>(p))
	{
		stream << '0';
		return;
	}

	const llvm::Instruction* I = dyn_cast<Instruction>(p);
	if (I && !isInlineable(*I, PA) && !forceGEP) {
		stream << namegen.getName(I);
		return;
	}

	bool asmjs = currentFun->getSection() == StringRef("asmjs");
	bool use_imul = asmjs || useMathImul;
	bool needsCoercion = needsIntCoercion(Registerize::INTEGER, parentPrio);
	PARENT_PRIORITY basePrio = ADD_SUB;
	if(needsCoercion)
		basePrio = BIT_OR;
	if(parentPrio > basePrio)
		stream << "(";
	AsmJSGepWriter gepWriter(*this, use_imul);
	p = linearHelper.compileGEP(p, &gepWriter);
	PARENT_PRIORITY gepPrio = gepWriter.offset?ADD_SUB:basePrio;
	compileOperand(p, gepPrio);
	if(needsCoercion)
		stream << "|0";
	if(parentPrio > basePrio)
		stream << ")";
}

int CheerpWriter::getHeapShiftForType(Type* et)
{
	uint32_t shift=0;
	if(et->isIntegerTy(8) || et->isIntegerTy(1))
	{
		shift = 0;
	}
	else if(et->isIntegerTy(16))
	{
		shift = 1;
	}
	else if(et->isIntegerTy(32) || et->isPointerTy() || et->isArrayTy())
	{
		shift = 2;
	}
	else if(et->isFloatTy())
	{
		shift = 2;
	}
	else if(et->isDoubleTy())
	{
		shift = 3;
	}
	else
	{
		llvm::errs() << "Unsupported heap access for  type " << *et << "\n";
		llvm::report_fatal_error("Unsupported code found, please report a bug", false);
	}
	return shift;
}
int CheerpWriter::compileHeapForType(Type* et)
{
	uint32_t shift=0;
	if(et->isIntegerTy(8) || et->isIntegerTy(1))
	{
		stream << heapNames[HEAP8];
		shift = 0;
	}
	else if(et->isIntegerTy(16))
	{
		stream << heapNames[HEAP16];
		shift = 1;
	}
	else if(et->isIntegerTy(32) || et->isPointerTy() || et->isArrayTy())
	{
		stream << heapNames[HEAP32];
		shift = 2;
	}
	else if(et->isFloatTy())
	{
		stream << heapNames[HEAPF32];
		shift = 2;
	}
	else if(et->isDoubleTy())
	{
		stream << heapNames[HEAPF64];
		shift = 3;
	}
	else
	{
		llvm::errs() << "Unsupported heap access for  type " << *et << "\n";
		llvm::report_fatal_error("Unsupported code found, please report a bug", false);
	}
	return shift;
}
void CheerpWriter::compileHeapAccess(const Value* p, Type* t)
{
	if (!isa<PointerType>(p->getType()))
	{
		llvm::errs() << "not a pointer type:\n";
		p->dump();
		llvm::report_fatal_error("please report a bug");
		return;
	}
	PointerType* pt=cast<PointerType>(p->getType());
	Type* et = (t==nullptr) ? pt->getElementType() : t;
	uint32_t shift = compileHeapForType(et);
	stream << '[';
	if(!symbolicGlobalsAsmJS && isa<GlobalVariable>(p))
	{
		stream << (linearHelper.getGlobalVariableAddress(cast<GlobalVariable>(p)) >> shift);
	}
	else
	{
		compileRawPointer(p, PARENT_PRIORITY::SHIFT);
		stream << ">>" << shift;
	}
	stream << ']';
}
void CheerpWriter::compilePointerBase(const Value* p, bool forEscapingPointer)
{
	if(PA.getPointerKind(p) == RAW)
	{
		assert(isa<PointerType>(p->getType()));
		Type* ty = llvm::cast<PointerType>(p->getType())->getPointerElementType();
		compileHeapForType(ty);
		return;
	}
	// Collapse if p is a gepInst
	if(isGEP(p))
	{
		const User* gepInst = cast<User>(p);
		assert(gepInst->getNumOperands() > 1);
		return compileGEPBase(gepInst, forEscapingPointer);
	}

	if(isBitCast(p) && (!isa<Instruction>(p) || isInlineable(*cast<Instruction>(p), PA) || forEscapingPointer))
	{
		compileBitCastBase(cast<User>(p), forEscapingPointer);
		return;
	}

	if(isa<ConstantPointerNull>(p))
	{
		stream << "nullArray";
		return;
	}

	if(PA.getPointerKind(p) == COMPLETE_OBJECT)
	{
		llvm::errs() << "compilePointerBase with COMPLETE_OBJECT pointer:" << *p << '\n' << "In function: " << *currentFun << '\n';
		llvm::report_fatal_error("Unsupported code found, please report a bug", false);
	}

	// Handle intrinsics
	if(const IntrinsicInst* II=dyn_cast<IntrinsicInst>(p))
	{
		switch(II->getIntrinsicID())
		{
			case Intrinsic::cheerp_upcast_collapsed:
			case Intrinsic::cheerp_cast_user:
				return compilePointerBase(II->getOperand(0));
			case Intrinsic::cheerp_make_regular:
				return compileCompleteObject(II->getOperand(0));
			default:
				break;
		}
	}

	if(isa<UndefValue>(p))
	{
		stream << "undefined";
		return;
	}

	if((isa<SelectInst> (p) && isInlineable(*cast<Instruction>(p), PA)) || (isa<ConstantExpr>(p) && cast<ConstantExpr>(p)->getOpcode() == Instruction::Select))
	{
		const User* u = cast<User>(p);
		stream << '(';
		compileOperand(u->getOperand(0), TERNARY, /*allowBooleanObjects*/ true);
		stream << '?';
		compilePointerBase(u->getOperand(1));
		stream << ':';
		compilePointerBase(u->getOperand(2));
		stream << ')';
		return;
	}

	if((!isa<Instruction>(p) || !isInlineable(*cast<Instruction>(p), PA)) && PA.getPointerKind(p) == SPLIT_REGULAR)
	{
		stream << namegen.getName(p);
		return;
	}

	// If value has not been generated from a GEP, just compile it and ask for .d
	compileOperand(p, HIGHEST);
	if(!PA.getConstantOffsetForPointer(p))
		stream << ".d";
}

const Value* CheerpWriter::compileByteLayoutOffset(const Value* p, BYTE_LAYOUT_OFFSET_MODE offsetMode)
{
	// If the value has byte layout skip GEPS and BitCasts until the base is found
	// We need to handle the first GEP having more than an index (so it actually changes types)
	// to support BYTE_LAYOUT_OFFSET_STOP_AT_ARRAY
	// If offsetMode is BYTE_LAYOUT_OFFSET_FULL we can treat every GEP in the same way
	bool findFirstTypeChangingGEP = (offsetMode != BYTE_LAYOUT_OFFSET_FULL);
	const Value* lastOffset = NULL;
	while ( isBitCast(p) || isGEP(p) )
	{
		const User * u = cast<User>(p);
		bool byteLayoutFromHere = PA.getPointerKind(u->getOperand(0)) != BYTE_LAYOUT;
		Type* curType = u->getOperand(0)->getType();
		if (isGEP(p))
		{
			bool skipUntilBytelayout = byteLayoutFromHere;
			SmallVector< const Value *, 8 > indices ( std::next(u->op_begin()), u->op_end() );
			for (uint32_t i=0;i<indices.size();i++)
			{
				if (StructType* ST = dyn_cast<StructType>(curType))
				{
					uint32_t index = cast<ConstantInt>( indices[i] )->getZExtValue();
					const StructLayout* SL = targetData.getStructLayout( ST );
					if (!skipUntilBytelayout && (offsetMode != BYTE_LAYOUT_OFFSET_NO_PRINT))
						stream << SL->getElementOffset(index) << '+';
					curType = ST->getElementType(index);
				}
				else
				{
					if (findFirstTypeChangingGEP && indices.size() > 1 && i == (indices.size() - 1))
					{
						assert (curType->isArrayTy());
						assert (offsetMode != BYTE_LAYOUT_OFFSET_FULL);
						// We have found an array just before the last type, the last offset will be returned instead of used directly.
						lastOffset = indices[i];
						break;
					}
					// This case also handles the first index
					if (!skipUntilBytelayout && (offsetMode != BYTE_LAYOUT_OFFSET_NO_PRINT))
					{
						bool isOffsetConstantZero = isa<Constant>(indices[i])
							&& cast<Constant>(indices[i])->isNullValue();
						if (!isOffsetConstantZero)
						{
							compileOperand( indices[i], MUL_DIV );
							stream << '*' << targetData.getTypeAllocSize(curType->getSequentialElementType()) << '+';
						}
					}
					curType = curType->getSequentialElementType();
				}
				if (skipUntilBytelayout && TypeSupport::hasByteLayout(curType))
					skipUntilBytelayout = false;
			}
			if (indices.size() > 1)
				findFirstTypeChangingGEP = false;
		}
		// In any case, close the summation here
		if(byteLayoutFromHere)
		{
			if(offsetMode != BYTE_LAYOUT_OFFSET_NO_PRINT)
				stream << '0';
			return lastOffset;
		}
		p = u->getOperand(0);
		continue;
	}
	assert (PA.getPointerKind(p) == BYTE_LAYOUT);
	if(offsetMode != BYTE_LAYOUT_OFFSET_NO_PRINT)
	{
		if(const ConstantInt* CI=PA.getConstantOffsetForPointer(p))
		{
			if(useMathImul)
				stream << namegen.getBuiltinName(NameGenerator::Builtin::IMUL);
			stream << '(';
			compileConstant(CI);
			if(useMathImul)
				stream << ',';
			else
				stream << '*';
			stream << targetData.getTypeAllocSize(p->getType()->getPointerElementType()) << ')';
		}
		else
		{
			compileCompleteObject(p);
			stream << ".o";
		}
	}
	return lastOffset;
}

void CheerpWriter::compilePointerOffset(const Value* p, PARENT_PRIORITY parentPrio, bool forEscapingPointer)
{
	bool byteLayout = PA.getPointerKind(p) == BYTE_LAYOUT;
	if ( PA.getPointerKind(p) == RAW)
	{
		assert(isa<PointerType>(p->getType()));
		Type* ty = llvm::cast<PointerType>(p->getType())->getPointerElementType();
		if (parentPrio < SHIFT)
			stream << '(';
		compileRawPointer(p, SHIFT);
		stream << ">>" << getHeapShiftForType(ty);
		if (parentPrio < SHIFT)
			stream << ')';
		return;
	}
	if ( PA.getPointerKind(p) == COMPLETE_OBJECT && !isGEP(p) )
	{
		// This may still happen when doing ptrtoint of a function
		stream << '0';
	}
	// null must be handled first, even if it is bytelayout
	else if(isa<ConstantPointerNull>(p) || isa<UndefValue>(p))
	{
		stream << '0';
	}
	// byteLayout must be handled second, otherwise we may print a constant offset without the required byte multiplier
	else if ( byteLayout && !forEscapingPointer)
	{
		compileByteLayoutOffset(p, BYTE_LAYOUT_OFFSET_FULL);
	}
	else if(isGEP(p) && (!isa<Instruction>(p) || isInlineable(*cast<Instruction>(p), PA) || forEscapingPointer))
	{
		compileGEPOffset(cast<User>(p), parentPrio);
	}
	else if(isBitCast(p) && (!isa<Instruction>(p) || isInlineable(*cast<Instruction>(p), PA) || forEscapingPointer))
	{
		compileBitCastOffset(cast<User>(p), parentPrio);
	}
	else if (const ConstantInt* CI = PA.getConstantOffsetForPointer(p))
	{
		// Check if the offset has been constantized for this pointer
		compileConstant(CI);
	}
	else if(isa<Argument>(p))
	{
		stream << namegen.getSecondaryName(p);
	}
	else if((isa<SelectInst> (p) && isInlineable(*cast<Instruction>(p), PA)) || (isa<ConstantExpr>(p) && cast<ConstantExpr>(p)->getOpcode() == Instruction::Select))
	{
		const User* u = cast<User>(p);
		if(parentPrio >= TERNARY)
			stream << '(';
		compileOperand(u->getOperand(0), TERNARY, /*allowBooleanObjects*/ true);
		stream << '?';
		compilePointerOffset(u->getOperand(1), TERNARY);
		stream << ':';
		compilePointerOffset(u->getOperand(2), TERNARY);
		if(parentPrio >= TERNARY)
			stream << ')';
	}
	else if((!isa<Instruction>(p) || !isInlineable(*cast<Instruction>(p), PA)) && PA.getPointerKind(p) == SPLIT_REGULAR)
	{
		stream << namegen.getSecondaryName(p);
	}
	else if(const IntrinsicInst* II=dyn_cast<IntrinsicInst>(p))
	{
		// Handle intrinsics
		switch(II->getIntrinsicID())
		{
			case Intrinsic::cheerp_upcast_collapsed:
			case Intrinsic::cheerp_cast_user:
				compilePointerOffset(II->getOperand(0), parentPrio);
				return;
			case Intrinsic::cheerp_make_regular:
				compileOperand(II->getOperand(1), parentPrio);
				break;
			default:
				compileOperand(p,HIGHEST);
				stream << ".o";
		}
	} else {
		compileOperand(p, HIGHEST);
		stream << ".o";
	}
}

void CheerpWriter::compileConstantExpr(const ConstantExpr* ce, PARENT_PRIORITY parentPrio, bool asmjs)
{
	switch(ce->getOpcode())
	{
		case Instruction::GetElementPtr:
		{
			compileGEP(ce, PA.getPointerKind(ce), parentPrio);
			break;
		}
		case Instruction::BitCast:
		{
			POINTER_KIND k = PA.getPointerKind(ce);
			compileBitCast(ce, k, parentPrio);
			break;
		}
		case Instruction::IntToPtr:
		{
			compileOperand(ce->getOperand(0), parentPrio);
			break;
		}
		case Instruction::PtrToInt:
		{
			if(asmjs)
				compileRawPointer(ce->getOperand(0), parentPrio);
			else
				compilePtrToInt(ce->getOperand(0));
			break;
		}
		case Instruction::ICmp:
		{
			compileIntegerComparison(ce->getOperand(0), ce->getOperand(1), (CmpInst::Predicate)ce->getPredicate(), parentPrio);
			break;
		}
		case Instruction::Select:
		{
			compileSelect(ce, ce->getOperand(0), ce->getOperand(1), ce->getOperand(2), parentPrio);
			break;
		}
		case Instruction::Sub:
		{
			compileSubtraction(ce->getOperand(0), ce->getOperand(1), parentPrio);
			break;
		}
		case Instruction::Add:
		{
			stream << '(';
			compileOperand(ce->getOperand(0), ADD_SUB);
			stream << "+";
			compileOperand(ce->getOperand(1), ADD_SUB);
			stream << "|0)";
			break;
		}
		default:
			stream << "undefined";
			llvm::errs() << "warning: Unsupported constant expr " << ce->getOpcodeName() << '\n';
	}
}

void CheerpWriter::compileConstantArrayMembers(const Constant* C)
{
	if(const ConstantArray* CA = dyn_cast<ConstantArray>(C))
	{
		Type* elementType = CA->getType()->getElementType();
		for(uint32_t i=0;i<CA->getNumOperands();i++)
		{
			if(i!=0)
				stream << ',';
			if(elementType->isPointerTy())
				compilePointerAs(CA->getOperand(i), PA.getPointerKindForStoredType(elementType));
			else
				compileOperand(CA->getOperand(i), LOWEST);
		}
	}
	else
	{
		const ConstantDataSequential* CD = dyn_cast<ConstantDataSequential>(C);
		assert(CD);
		for(uint32_t i=0;i<CD->getNumElements();i++)
		{
			if(i!=0)
				stream << ',';
			compileConstant(CD->getElementAsConstant(i));
		}
	}
}

bool CheerpWriter::doesConstantDependOnUndefined(const Constant* C) const
{
	if(isa<ConstantExpr>(C) && C->getOperand(0)->getType()->isPointerTy())
		return doesConstantDependOnUndefined(cast<Constant>(C->getOperand(0)));
	else if(isa<GlobalVariable>(C) && !compiledGVars.count(cast<GlobalVariable>(C)))
		return true;
	else
		return false;
}

void CheerpWriter::compileConstant(const Constant* c, PARENT_PRIORITY parentPrio)
{
	//TODO: what to do when currentFun == nullptr? for now asmjs=false
	bool asmjs = false;
	if (currentFun)
	{
		asmjs = currentFun->getSection() == StringRef("asmjs");
	}
	if(!currentFun && doesConstantDependOnUndefined(c))
	{
		// If we are compiling a constant expr using a global variable which has
		// not been defined yet, just print undefined
		stream << "undefined";
	}
	else if(isa<ConstantExpr>(c))
	{
		compileConstantExpr(cast<ConstantExpr>(c), parentPrio, asmjs);
	}
	else if(isa<ConstantDataSequential>(c))
	{
		const ConstantDataSequential* d=cast<ConstantDataSequential>(c);
		Type* t=d->getElementType();
		stream << "new ";
		compileTypedArrayType(t);
		stream << "([";
		compileConstantArrayMembers(d);
		stream << "])";
	}
	else if(isa<ConstantArray>(c))
	{
		const ConstantArray* d=cast<ConstantArray>(c);
		stream << '[';
		assert(d->getType()->getNumElements() == d->getNumOperands());
		compileConstantArrayMembers(d);
		stream << ']';
	}
	else if(isa<ConstantStruct>(c))
	{
		const ConstantStruct* d=cast<ConstantStruct>(c);
		if(cast<StructType>(c->getType())->hasByteLayout())
		{
			// Populate a DataView with a byte buffer
			stream << "new DataView(new Int8Array([";
			JSBytesWriter bytesWriter(stream);
			linearHelper.compileConstantAsBytes(c, /*asmjs*/false, &bytesWriter);
			stream << "]).buffer)";
			return;
		}
		stream << '{';
		assert(d->getType()->getNumElements() == d->getNumOperands());

		for(uint32_t i=0;i<d->getNumOperands();i++)
		{
			stream << types.getPrefixCharForMember(PA, d->getType(), i) << i << ':';
			bool useWrapperArray = types.useWrapperArrayForMember(PA, d->getType(), i);
			if (useWrapperArray)
				stream << '[';
			Type* elementType = d->getOperand(i)->getType();
			bool dependOnUndefined = !currentFun && doesConstantDependOnUndefined(d->getOperand(i));
			if(elementType->isPointerTy())
			{
				TypeAndIndex baseAndIndex(d->getType(), i, TypeAndIndex::STRUCT_MEMBER);
				POINTER_KIND k = PA.getPointerKindForMemberPointer(baseAndIndex);
				if((k==REGULAR || k==SPLIT_REGULAR) && PA.getConstantOffsetForMember(baseAndIndex))
				{
					if(dependOnUndefined)
						stream << "undefined";
					else
						compilePointerBase(d->getOperand(i));
				}
				else if(k == SPLIT_REGULAR)
				{
					if(dependOnUndefined)
						stream << "undefined";
					else
						compilePointerBase(d->getOperand(i));
					stream << ',';
					stream << types.getPrefixCharForMember(PA, d->getType(), i) << i << 'o';
					stream << ':';
					if(dependOnUndefined)
						stream << "undefined";
					else
						compilePointerOffset(d->getOperand(i), LOWEST);
				}
				else
				{
					if(dependOnUndefined)
						stream << "undefined";
					else
						compilePointerAs(d->getOperand(i), k);
				}
			}
			else if(dependOnUndefined)
				stream << "undefined";
			else
				compileOperand(d->getOperand(i), LOWEST);

			if (useWrapperArray)
				stream << ']';
			if((i+1)<d->getNumOperands())
				stream << ',';
		}

		stream << '}';
	}
	else if(isa<ConstantFP>(c))
	{
		Registerize::REGISTER_KIND regKind = registerize.getRegKindFromType(c->getType(), asmjs);
		const ConstantFP* f=cast<ConstantFP>(c);
		bool useFloat = false;
		
		if(f->getValueAPF().isInfinity())
		{
			if (needsFloatCoercion(regKind, parentPrio))
				stream<< namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
			if(f->getValueAPF().isNegative())
			{
				if(parentPrio > LOWEST)
					stream << ' ';
				stream << '-';
			}

			stream << "Infinity";
			if (needsFloatCoercion(regKind, parentPrio))
				stream << ')';
		}
		else if(f->getValueAPF().isNaN())
		{
			if (needsFloatCoercion(regKind, parentPrio))
				stream<< namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
			stream << "NaN";
			if (needsFloatCoercion(regKind, parentPrio))
				stream << ')';
		}
		else
		{
			APFloat apf = f->getValueAPF();
			// We want the most compact representation possible, so we first try
			// to represent the number with a maximum of nuumeric_limits::digits10.
			// We convert the string back to a double, and if it is not the same
			// as the original we try again with numeric_limits::max_digits10
			
			// Needed by APFloat::convert, not used here
			bool losesInfo = false;
			SmallString<32> buf;

			apf.convert(APFloat::IEEEdouble, APFloat::roundingMode::rmNearestTiesToEven, &losesInfo);
			assert(!losesInfo);
			double original = apf.convertToDouble();

			apf.toString(buf, std::numeric_limits<double>::digits10);
			double converted = 0;
			sscanf(buf.c_str(),"%lf",&converted);
			if(converted != original)
			{
				buf.clear();
				apf.toString(buf, std::numeric_limits<double>::max_digits10);
			}

			apf.convert(APFloat::IEEEsingle, APFloat::roundingMode::rmNearestTiesToEven, &losesInfo);
			// If we don't lose information or if the actual type is a float
			// (and thus we don't care that we are losing it), try to see if
			// it is shorter to use a float instead of a double (using fround)
			if(useMathFround && (!losesInfo || f->getType()->isFloatTy()))
			{
				float original = apf.convertToFloat();
				SmallString<32> tmpbuf;
				apf.toString(tmpbuf, std::numeric_limits<float>::digits10);
				float converted = 0;
				sscanf(tmpbuf.c_str(),"%f",&converted);
				if(converted != original)
				{
					tmpbuf.clear();
					apf.toString(tmpbuf, std::numeric_limits<float>::max_digits10);
				}
				// We actually use the float only if it is shorter to write,
				// including the call to fround
				size_t floatsize = tmpbuf.size() + namegen.getBuiltinName(NameGenerator::Builtin::FROUND).size()+2;  
				if(buf.size() > floatsize || (regKind == Registerize::FLOAT))
				{
					useFloat = true;
					// In asm.js double and float are distinct types, so
					// we cast back to double if needed
					if(asmjs && f->getType()->isDoubleTy())
					{
						if (parentPrio > LOWEST)
							stream << ' ';
						stream << '+';
					}
					if(parentPrio != FROUND)
						stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
					buf = tmpbuf;
				}
				else if(parentPrio > LOWEST && f->getValueAPF().isNegative())
					stream << ' ';
			}
			// asm.js require the floating point literals to have a dot
			if(asmjs && buf.find('.') == StringRef::npos)
			{
				auto it = buf.begin();
				// We must insert the dot before the exponent part
				// (or at the end if there is no exponent)
				for (;it != buf.end() && *it != 'E' && *it != 'e'; it++);
				buf.insert(it,'.');
			}
			// If the number is in the form `0.xyz...` we can remove the leading 0
			int start = 0;
			if (buf[0] == '0' && buf.size() > 2)
				start = 1;
			stream << buf.c_str()+start;
			if (useFloat && parentPrio != FROUND)
				stream << ')';
		}
	}
	else if(isa<ConstantInt>(c))
	{
		const ConstantInt* i=cast<ConstantInt>(c);
		if(i->getBitWidth()==32)
		{
			if(parentPrio > LOWEST && i->isNegative())
				stream << ' ';
			stream << i->getSExtValue();
		}
		else
			stream << i->getZExtValue();
	}
	else if(isa<ConstantPointerNull>(c))
	{
		if (asmjs)
			stream << '0';
		else if(PA.getPointerKind(c) == COMPLETE_OBJECT)
			stream << "null";
		else
			stream << "nullObj";
	}
	else if(isa<GlobalAlias>(c))
	{
		const GlobalAlias* a=cast<GlobalAlias>(c);
		compileConstant(a->getAliasee());
	}
	else if(isa<GlobalValue>(c))
	{
		if (!asmjs)
		{
			asmjs = cast<GlobalValue>(c)->getSection() == StringRef("asmjs");
		}
		assert(c->hasName());

		if(asmjs && isa<Function>(c))
		{
			if (linearHelper.functionHasAddress(cast<Function>(c))) {
				int addr = linearHelper.getFunctionAddress(cast<Function>(c));
				stream << addr;
			} else {
				stream << '0';
			}
		}
		else if (isa<GlobalVariable>(c) && !symbolicGlobalsAsmJS && asmjs)
		{
			stream << linearHelper.getGlobalVariableAddress(cast<GlobalVariable>(c));
		}
		else
			stream << namegen.getName(c);
	}
	else if(isa<ConstantAggregateZero>(c) || isa<UndefValue>(c))
	{
		if (asmjs && c->getType()->isPointerTy())
			stream << '0';
		else
			compileType(c->getType(), LITERAL_OBJ);
	}
	else
	{
		llvm::errs() << "Unsupported constant type ";
		c->dump();
		stream << "null";
	}
}

void CheerpWriter::compileOperand(const Value* v, PARENT_PRIORITY parentPrio, bool allowBooleanObjects)
{
	if(const Constant* c=dyn_cast<Constant>(v))
		compileConstant(c, parentPrio);
	else if(const Instruction* it=dyn_cast<Instruction>(v))
	{
		if(isInlineable(*it, PA))
		{
			bool isBooleanObject = false;
			if(it->getType()->isIntegerTy(1))
			{
				switch(it->getOpcode())
				{
					case Instruction::ICmp:
					case Instruction::FCmp:
					case Instruction::And:
					case Instruction::Or:
					case Instruction::Xor:
						isBooleanObject = true;
						break;
					default:
						break;
				}
			}
			PARENT_PRIORITY myPrio = parentPrio;
			if(isBooleanObject && !allowBooleanObjects)
			{
				myPrio = TERNARY;
				if (parentPrio >= TERNARY)
					stream << '(';
			}
			const llvm::DebugLoc* oldLoc = nullptr;
			if(sourceMapGenerator)
			{
				const DebugLoc& debugLoc = it->getDebugLoc();
				if(debugLoc)
				{
					oldLoc = sourceMapGenerator->getDebugLoc();
					sourceMapGenerator->setDebugLoc(&debugLoc);
				}
			}
			compileInlineableInstruction(*cast<Instruction>(v), myPrio);
			if(sourceMapGenerator && oldLoc)
				sourceMapGenerator->setDebugLoc(oldLoc);
			if(isBooleanObject && !allowBooleanObjects)
			{
				stream << "?1:0";
				if(parentPrio >= TERNARY)
					stream << ')';
			}
		}
		else
		{
			stream << namegen.getName(it);
		}
	}
	else if(const Argument* arg=dyn_cast<Argument>(v))
	{
		stream << namegen.getName(arg);
	}
	else
	{
		llvm::errs() << "No name for value ";
		v->dump();
	}
}

bool CheerpWriter::needsPointerKindConversion(const PHINode* phi, const Value* incoming,
                                              const PointerAnalyzer& PA, const Registerize& registerize)
{
	if(canDelayPHI(phi, PA, registerize))
		return false;
	Type* phiType=phi->getType();
	const Instruction* incomingInst=getUniqueIncomingInst(incoming, PA);
	if(!incomingInst)
		return true;
	assert(!isInlineable(*incomingInst, PA));
	POINTER_KIND incomingKind = UNKNOWN;
	POINTER_KIND phiKind = UNKNOWN;
	const llvm::ConstantInt* incomingOffset = nullptr;
	const llvm::ConstantInt* phiOffset = nullptr;
	if(phiType->isPointerTy())
	{
		incomingKind = PA.getPointerKind(incomingInst);
		phiKind = PA.getPointerKind(phi);
		if(incomingKind == SPLIT_REGULAR || incomingKind == REGULAR || incomingKind == BYTE_LAYOUT)
			incomingOffset = PA.getConstantOffsetForPointer(incomingInst);
		if(phiKind == SPLIT_REGULAR || phiKind == REGULAR || phiKind == BYTE_LAYOUT)
			phiOffset = PA.getConstantOffsetForPointer(phi);
	}
	return
		registerize.getRegisterId(phi)!=registerize.getRegisterId(incomingInst) ||
		phiKind!=incomingKind ||
		phiOffset!=incomingOffset;
}

bool CheerpWriter::needsPointerKindConversionForBlocks(const BasicBlock* to, const BasicBlock* from,
                                                       const PointerAnalyzer& PA, const Registerize& registerize)
{
	class PHIHandler: public EndOfBlockPHIHandler
	{
	public:
		PHIHandler(const PointerAnalyzer& PA, const Registerize& registerize):
		           EndOfBlockPHIHandler(PA),needsPointerKindConversion(false),PA(PA),registerize(registerize)
		{
		}
		~PHIHandler()
		{
		}
		bool needsPointerKindConversion;
	private:
		const PointerAnalyzer& PA;
		const Registerize& registerize;
		void handleRecursivePHIDependency(const Instruction* incoming) override
		{
		}
		void handlePHI(const PHINode* phi, const Value* incoming, bool selfReferencing) override
		{
			needsPointerKindConversion |= CheerpWriter::needsPointerKindConversion(phi, incoming, PA, registerize);
		}
	};

	auto handler = PHIHandler(PA, registerize);
	handler.runOnEdge(registerize, from, to);
	return handler.needsPointerKindConversion;
}

void CheerpWriter::compilePHIOfBlockFromOtherBlock(const BasicBlock* to, const BasicBlock* from)
{
	class WriterPHIHandler: public EndOfBlockPHIHandler
	{
	public:
		WriterPHIHandler(CheerpWriter& w, const BasicBlock* f, const BasicBlock* t):EndOfBlockPHIHandler(w.PA),writer(w),fromBB(f),toBB(t)
		{
		}
		~WriterPHIHandler()
		{
		}
	private:
		CheerpWriter& writer;
		const BasicBlock* fromBB;
		const BasicBlock* toBB;
		void handleRecursivePHIDependency(const Instruction* incoming) override
		{
			assert(incoming);
			if(incoming->getType()->isPointerTy() && writer.PA.getPointerKind(incoming)==SPLIT_REGULAR && !writer.PA.getConstantOffsetForPointer(incoming))
			{
				writer.stream << writer.namegen.getSecondaryNameForEdge(incoming, fromBB, toBB);
				writer.stream << '=';
				writer.compilePointerOffset(incoming, LOWEST);
				writer.stream << ';' << writer.NewLine;
			}
			writer.stream << writer.namegen.getNameForEdge(incoming, fromBB, toBB);
			writer.stream << '=' << writer.namegen.getName(incoming) << ';' << writer.NewLine;
		}
		void handlePHI(const PHINode* phi, const Value* incoming, bool selfReferencing) override
		{
			// We can avoid assignment from the same register if no pointer kind conversion is required
			if(!needsPointerKindConversion(phi, incoming, writer.PA, writer.registerize))
				return;
			// We can leave undefined values undefined
			if (isa<UndefValue>(incoming))
				return;
			Type* phiType=phi->getType();
			if(phiType->isPointerTy())
			{
				POINTER_KIND k=writer.PA.getPointerKind(phi);
				if((k==REGULAR || k==SPLIT_REGULAR || k==BYTE_LAYOUT) && writer.PA.getConstantOffsetForPointer(phi))
				{
					writer.stream << writer.namegen.getName(phi) << '=';
					writer.registerize.setEdgeContext(fromBB, toBB);
					writer.compilePointerBase(incoming);
				}
				else if(k==SPLIT_REGULAR)
				{
					POINTER_KIND incomingKind=writer.PA.getPointerKind(incoming);
					// TODO: Won't have a self ref tmp if there is a tmpphi already for this PHI
					if(selfReferencing)
					{
						assert(!PA.getConstantOffsetForPointer(incoming));
						assert(PA.getPointerKind(incoming) == SPLIT_REGULAR);
					}
					uint32_t tmpOffsetReg = -1;
					if(selfReferencing)
					{
						tmpOffsetReg = writer.registerize.getSelfRefTmpReg(phi, fromBB, toBB);
						writer.stream << writer.namegen.getName(phi->getParent()->getParent(), tmpOffsetReg);
					}
					else
						writer.stream << writer.namegen.getSecondaryName(phi);
					writer.stream << '=';
					writer.registerize.setEdgeContext(fromBB, toBB);
					if (incomingKind == RAW)
					{
						writer.compileRawPointer(incoming, SHIFT);
						writer.stream << ">>" << writer.getHeapShiftForType(cast<PointerType>(phiType)->getPointerElementType());
					}
					else
					{
						writer.compilePointerOffset(incoming, LOWEST);
					}
					writer.stream << ';' << writer.NewLine;
					writer.registerize.clearEdgeContext();
					writer.stream << writer.namegen.getName(phi) << '=';
					writer.registerize.setEdgeContext(fromBB, toBB);
					if (incomingKind == RAW)
						writer.compileHeapForType(cast<PointerType>(phiType)->getPointerElementType());
					else
						writer.compilePointerBase(incoming);
					if(selfReferencing)
					{
						writer.stream << ';' << writer.NewLine;
						writer.registerize.clearEdgeContext();
						writer.stream << writer.namegen.getSecondaryName(phi) << '=' << writer.namegen.getName(phi->getParent()->getParent(), tmpOffsetReg);
					}
				}
				else if(k==RAW)
				{
					writer.stream << writer.namegen.getName(phi) << '=';
					writer.registerize.setEdgeContext(fromBB, toBB);
					writer.compileRawPointer(incoming, LOWEST);
				}
				else
				{
					writer.stream << writer.namegen.getName(phi) << '=';
					writer.registerize.setEdgeContext(fromBB, toBB);
					writer.compilePointerAs(incoming, k);
				}
			}
			else
			{
				writer.stream << writer.namegen.getName(phi) << '=';
				writer.registerize.setEdgeContext(fromBB, toBB);
				writer.compileOperand(incoming, LOWEST);
			}
			writer.stream << ';' << writer.NewLine;
			writer.registerize.clearEdgeContext();
		}
	};
	WriterPHIHandler(*this, from, to).runOnEdge(registerize, from, to);
}

void CheerpWriter::compileMethodArgs(User::const_op_iterator it, User::const_op_iterator itE, ImmutableCallSite callV, bool forceBoolean)
{
	assert(callV.arg_begin() <= it && it <= callV.arg_end() && "compileMethodArgs, it out of range!");
	assert(callV.arg_begin() <= itE && itE <= callV.arg_end() && "compileMethodArgs, itE out of range!");
	assert(it <= itE);

	stream << '(';

	const Function* F = callV.getCalledFunction();
	bool asmjs = callV.getCaller()->getSection() == StringRef("asmjs");

	Function::const_arg_iterator arg_it;

	// Check if we have a direct call
	if(F && it != itE)
	{
		// Set arg_it to the argument relative to it.
		arg_it = F->arg_begin();
		unsigned argNo = callV.getArgumentNo(it);

		// Check if it is a variadic argument
		if(argNo < F->arg_size())
		{
			std::advance(arg_it, callV.getArgumentNo(it));
		}
		else
		{
			arg_it = F->arg_end();
		}
	}

	uint32_t opCount = 0;
	for(User::const_op_iterator cur=it; cur!=itE; ++cur, ++opCount)
	{
		if(cur!=it)
			stream << ',';

		Type* tp = (*cur)->getType();

		if (asmjs)
		{
			const PointerType* pTy = cast<PointerType>(callV.getCalledValue()->getType());
			const FunctionType* fTy = cast<FunctionType>(pTy->getElementType());
			bool isImport = F && globalDeps.asmJSImports().count(F);
			PARENT_PRIORITY prio = LOWEST;
			if (tp->isPointerTy() || (tp->isIntegerTy() &&
				(isImport ||
				(!F && !linearHelper.getFunctionTables().count(fTy)))))
			{
				prio = BIT_OR;
			}
			else if(isImport && tp->isFloatTy())
				stream << "+";
			compileOperand(*cur,prio);
			if (prio == BIT_OR)
				stream << "|0";
		}
		else if(tp->isPointerTy())
		{
			POINTER_KIND argKind = UNKNOWN;
			// Calling convention:
			// If this is a direct call and the argument is not a variadic one,
			// we pass the kind decided by getPointerKind(arg_it).
			// If it's variadic we use the base kind derived from the type
			// If it's indirect we use a kind good for any argument of a given type at a given position
			if (!F)
			{
				TypeAndIndex typeAndIndex(tp->getPointerElementType(), opCount, TypeAndIndex::ARGUMENT);
				argKind = PA.getPointerKindForArgumentTypeAndIndex(typeAndIndex);
			}
			else if (arg_it != F->arg_end())
				argKind = PA.getPointerKind(arg_it);
			else
			{
				if(isa<ConstantPointerNull>(*cur) && (cur+1)==itE && cur!=it)
				{
					// Special case for NULL which are the last variadic parameter, copy the previous type
					Type* prevType = (*(cur-1))->getType();
					if(prevType->isPointerTy())
						tp = prevType;
				}
				if(StructType* st = dyn_cast<StructType>(tp->getPointerElementType()))
				{
					while(st->getDirectBase())
						st = st->getDirectBase();
					tp = st->getPointerTo();
				}
				compilePointerAs(*cur, PA.getPointerKindForStoredType(tp));
			}

			assert(argKind != REGULAR);
			POINTER_KIND curKind = PA.getPointerKind(cur->get());
			// The second condition is for when the function is only declared
			// And the passed pointer is BYTE_LAYOUT. We decide to compile it as
			// SPLIT_REGULAR, since the code will crash here anyway
			if(argKind == SPLIT_REGULAR ||
				(argKind == COMPLETE_OBJECT && curKind == BYTE_LAYOUT))
			{
				if(curKind == RAW)
				{
					int shift = compileHeapForType(cast<PointerType>(cur->get()->getType())->getPointerElementType());
					stream << ',';
					compileRawPointer(*cur, SHIFT);
					stream << ">>" << shift;
				}
				else
				{
					compilePointerBase(*cur, true);
					stream << ',';
					compilePointerOffset(*cur, LOWEST, true);
				}
			}
			else if(argKind == RAW)
			{
				compileRawPointer(*cur, LOWEST);
			}
			else if(argKind != UNKNOWN)
				compilePointerAs(*cur, argKind);
		}
		else if(tp->isIntegerTy(1) && forceBoolean)
		{
			stream << "!!";
			compileOperand(*cur, HIGHEST);
		}
		else
			compileOperand(*cur,LOWEST);

		if(F && arg_it != F->arg_end())
		{
			++arg_it;
		}
	}
	stream << ')';
}

/*
 * This method is fragile, each opcode must handle the phis in the correct place
 */
CheerpWriter::COMPILE_INSTRUCTION_FEEDBACK CheerpWriter::compileTerminatorInstruction(const TerminatorInst& I)
{
	bool asmjs = currentFun->getSection() == StringRef("asmjs");
	switch(I.getOpcode())
	{
		case Instruction::Ret:
		{
			const ReturnInst& ri = cast<ReturnInst>(I);
			assert(I.getNumSuccessors()==0);
			Value* retVal = ri.getReturnValue();

			if(retVal)
			{
				Registerize::REGISTER_KIND kind = registerize.getRegKindFromType(retVal->getType(), asmjs);
				switch(kind)
				{
					case Registerize::INTEGER:
						stream << "return ";
						compileOperand(retVal, BIT_OR);
						stream << "|0";
						break;
					case Registerize::DOUBLE:
						stream << "return ";
						compileOperand(retVal, LOWEST);
						break;
					case Registerize::FLOAT:
						stream << "return ";
						stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
						compileOperand(retVal, FROUND);
						stream << ')';
						break;
					case Registerize::OBJECT:
						POINTER_KIND k=PA.getPointerKindForReturn(ri.getParent()->getParent());
						// For SPLIT_REGULAR we return the .d part and store the .o part into oSlot
						if(k==SPLIT_REGULAR)
						{
							stream << "oSlot=";
							compilePointerOffset(retVal, LOWEST);
							stream << ';' << NewLine;
						}
						stream << "return ";
						assert(k != REGULAR);
						if(k==SPLIT_REGULAR)
							compilePointerBase(retVal);
						else
							compilePointerAs(retVal, k);
						break;
				}
			}
			else if(blockDepth == 0)
			{
				// A return statement at depth 0 means the function is finished
				// This is a void return at the end of the function, just skip it
				return COMPILE_EMPTY;
			}
			else
				stream << "return";

			stream << ';' << NewLine;
			return COMPILE_OK;
		}
		case Instruction::Invoke:
		{
			const InvokeInst& ci = cast<InvokeInst>(I);

			//TODO: Support unwind
			//For now, pretend it's a regular call
			if(ci.getCalledFunction())
			{
				//Direct call
				COMPILE_INSTRUCTION_FEEDBACK cf=handleBuiltinCall(&ci, ci.getCalledFunction());
				assert(cf!=COMPILE_EMPTY);
				if(cf==COMPILE_OK)
				{
					stream << ';' << NewLine;
					//Only consider the normal successor for PHIs here
					//For each successor output the variables for the phi nodes
					compilePHIOfBlockFromOtherBlock(ci.getNormalDest(), I.getParent());
					return COMPILE_OK;
				}
				else
					stream << namegen.getName(ci.getCalledFunction());
			}
			else
			{
				//Indirect call
				compileOperand(ci.getCalledValue());
			}

			compileMethodArgs(ci.op_begin(),ci.op_begin()+ci.getNumArgOperands(),&ci, /*forceBoolean*/ false);
			stream << ';' << NewLine;
			//Only consider the normal successor for PHIs here
			//For each successor output the variables for the phi nodes
			compilePHIOfBlockFromOtherBlock(ci.getNormalDest(), I.getParent());
			return COMPILE_OK;
		}
		case Instruction::Resume:
		{
			//TODO: support exceptions
			return COMPILE_OK;
		}
		case Instruction::Br:
		case Instruction::Switch:
		case Instruction::Unreachable:
			return COMPILE_EMPTY;
		default:
			stream << "alert('Unsupported code');" << NewLine;
			llvm::errs() << "\tImplement terminator inst " << I.getOpcodeName() << '\n';
	}
	return COMPILE_UNSUPPORTED;
}

CheerpWriter::COMPILE_INSTRUCTION_FEEDBACK CheerpWriter::compileNotInlineableInstruction(const Instruction& I, PARENT_PRIORITY parentPrio)
{
	bool asmjs = currentFun->getSection() == StringRef("asmjs");
	switch(I.getOpcode())
	{
		case Instruction::Alloca:
		{
			const AllocaInst* ai = cast<AllocaInst>(&I);
			const auto* allocaStores = allocaStoresExtractor.getValuesForAlloca(ai);
			POINTER_KIND k = PA.getPointerKind(ai);
			assert(k != RAW && "Allocas to RAW pointers are removed in the AllocaLowering pass");

			StringRef varName = namegen.getName(&I);
			if(k == REGULAR)
			{
				stream << "{d:[";
				compileType(ai->getAllocatedType(), LITERAL_OBJ, varName, allocaStores);
				stream << "],o:0}";
			}
			else if(k == SPLIT_REGULAR)
			{
				stream << "=0";
				stream << ';' << NewLine;
				stream << namegen.getName(ai) << '=';
				stream << '[';
				compileType(ai->getAllocatedType(), LITERAL_OBJ, varName, allocaStores);
				stream << ']';
			}
			else if(k == BYTE_LAYOUT)
			{
				assert(!allocaStores);
				stream << "{d:";
				compileType(ai->getAllocatedType(), LITERAL_OBJ, varName);
				stream << ",o:0}";
			}
			else 
				compileType(ai->getAllocatedType(), LITERAL_OBJ, varName, allocaStores);

			return COMPILE_OK;
		}
		case Instruction::LandingPad:
		{
			//TODO: Support exceptions
			stream << " alert('Exceptions not supported')";
			//Do not continue block
			return COMPILE_UNSUPPORTED;
		}
		case Instruction::InsertValue:
		{
			const InsertValueInst& ivi = cast<InsertValueInst>(I);
			const Value* aggr=ivi.getAggregateOperand();
			StructType* t=dyn_cast<StructType>(aggr->getType());
			assert(ivi.getIndices().size()==1);
			if(!t)
			{
				llvm::errs() << "insertvalue: Expected struct, found " << *t << "\n";
				llvm::report_fatal_error("Unsupported code found, please report a bug", false);
				return COMPILE_UNSUPPORTED;
			}
			uint32_t offset=ivi.getIndices()[0];
			if(isa<UndefValue>(aggr))
			{
				// We have to assemble the type object from scratch
				stream << '{';
				for(unsigned int i=0;i<t->getNumElements();i++)
				{
					assert(!t->getElementType(i)->isStructTy());
					assert(!t->getElementType(i)->isArrayTy());
					char memberPrefix = types.getPrefixCharForMember(PA, t, i);
					bool useWrapperArray = types.useWrapperArrayForMember(PA, t, i);
					if(i!=0)
						stream << ',';
					stream << memberPrefix << i << ':';
					if(useWrapperArray)
						stream << '[';
					if(offset == i)
						compileOperand(ivi.getInsertedValueOperand(), LOWEST);
					else
						compileType(t->getElementType(i), LITERAL_OBJ);
					if(useWrapperArray)
						stream << ']';
				}
				stream << '}';
			}
			else
			{
				// We have to make a copy with a field of a different value
				stream << '{';
				for(unsigned int i=0;i<t->getNumElements();i++)
				{
					assert(!t->getElementType(i)->isStructTy());
					assert(!t->getElementType(i)->isArrayTy());
					char memberPrefix = types.getPrefixCharForMember(PA, t, i);
					bool useWrapperArray = types.useWrapperArrayForMember(PA, t, i);
					if(i!=0)
						stream << ',';
					stream << memberPrefix << i << ':';
					if(useWrapperArray)
						stream << '[';
					if(offset == i)
						compileOperand(ivi.getInsertedValueOperand(), LOWEST);
					else
					{
						stream << namegen.getName(aggr);
						stream << '.' << memberPrefix << i;
						if(useWrapperArray)
							stream << "[0]";
					}
					if(useWrapperArray)
						stream << ']';
				}
				stream << '}';
			}
			return COMPILE_OK;
		}
		case Instruction::Store:
		{
			const StoreInst& si = cast<StoreInst>(I);
			const Value* ptrOp=si.getPointerOperand();
			const Value* valOp=si.getValueOperand();
			POINTER_KIND kind = PA.getPointerKind(ptrOp);
			if (checkBounds)
			{
				if(kind == REGULAR || kind == SPLIT_REGULAR)
				{
					compileCheckBounds(ptrOp);
					stream<<",";
				}
				else if(kind == COMPLETE_OBJECT && isGEP(ptrOp))
				{
					bool needsOffset = valOp->getType()->isPointerTy() && PA.getPointerKind(&si) == SPLIT_REGULAR && !PA.getConstantOffsetForPointer(&si);
					compileCheckDefined(ptrOp, needsOffset);
					stream<<",";
				}
				else if(kind == RAW)
				{
					compileCheckBoundsAsmJS(ptrOp, targetData.getTypeAllocSize(valOp->getType())-1);
					stream<<",";
				}
			}
			// TODO: we need this hack because PointerAnalyzer cannot correctly assign
			// the RAW kind to null pointers
			bool asmjs = currentFun && currentFun->getSection()==StringRef("asmjs");
			bool asmjs_nullptr = asmjs && isa<ConstantPointerNull>(ptrOp);
			if (RAW == kind || asmjs_nullptr)
			{
				compileHeapAccess(ptrOp);
			}
			else if (kind == BYTE_LAYOUT)
			{
				//Optimize stores of single values from unions
				compilePointerBase(ptrOp);
				Type* pointedType=ptrOp->getType()->getPointerElementType();
				if(pointedType->isIntegerTy(8))
					stream << ".setInt8(";
				else if(pointedType->isIntegerTy(16))
					stream << ".setInt16(";
				else if(pointedType->isIntegerTy(32))
					stream << ".setInt32(";
				else if(pointedType->isFloatTy())
					stream << ".setFloat32(";
				else if(pointedType->isDoubleTy())
					stream << ".setFloat64(";
				compilePointerOffset(ptrOp, LOWEST);
				stream << ',';

				//Special case compilation of operand, the default behavior use =
				compileOperand(valOp, LOWEST);
				if(!pointedType->isIntegerTy(8))
					stream << ",true";
				stream << ')';
				return COMPILE_OK;
			}
			else
			{
				compileCompleteObject(ptrOp);
			}

			stream << '=';
			if(!asmjs && valOp->getType()->isPointerTy())
			{
				POINTER_KIND storedKind = PA.getPointerKind(&si);
				// If regular see if we can omit the offset part
				if((storedKind==SPLIT_REGULAR || storedKind==REGULAR || storedKind==BYTE_LAYOUT) && PA.getConstantOffsetForPointer(&si))
					compilePointerBase(valOp);
				else if(storedKind==SPLIT_REGULAR)
				{
					compilePointerBase(valOp);
					stream << ';' << NewLine;
					compileCompleteObject(ptrOp);
					stream << "o=";
					compilePointerOffset(valOp, LOWEST);
				}
				else
					compilePointerAs(valOp, storedKind);
			}
			else
			{
				PARENT_PRIORITY storePrio = LOWEST;
				if(asmjs)
				{
					// On asm.js we can pretend the store will add a |0
					// This is not necessarily true in genericjs
					// As we might be storing in an object member or a plain array
					Registerize::REGISTER_KIND regKind = registerize.getRegKindFromType(valOp->getType(), asmjs);
					if(regKind == Registerize::INTEGER)
						storePrio = BIT_OR;
					// The same applies for fround
					else if(regKind == Registerize::FLOAT)
						storePrio = FROUND;
				}
				compileOperand(valOp, storePrio);
			}
			return COMPILE_OK;
		}
		case Instruction::PHI:
		{
			const PHINode* phi = cast<PHINode>(&I);
			assert(phi->getType()->isPointerTy());
			assert(canDelayPHI(phi, PA, registerize));
			// If we get here we know that all the values are rendered indentically
			const Value* incoming = phi->getIncomingValue(0);
			POINTER_KIND k = PA.getPointerKind(phi);
			if(k == SPLIT_REGULAR)
			{
				if(!PA.getConstantOffsetForPointer(phi))
				{
					compilePointerOffset(incoming, LOWEST);
					stream << ';' << NewLine;
					stream << namegen.getName(phi) << '=';
				}
				compilePointerBase(incoming);
			}
			else
				compilePointerAs(incoming, k);
			return COMPILE_OK;
		}
		default:
		{
			bool convertBoolean = false;
			if(!asmjs && I.getType()->isIntegerTy(1))
			{
				switch(I.getOpcode())
				{
					case Instruction::ICmp:
					case Instruction::FCmp:
					case Instruction::And:
					case Instruction::Or:
					case Instruction::Xor:
						convertBoolean = true;
						break;
					default:
						break;
				}
			}
			COMPILE_INSTRUCTION_FEEDBACK ret=compileInlineableInstruction(I, convertBoolean?TERNARY:parentPrio);
			if (ret == COMPILE_OK && convertBoolean)
				stream << "?1:0";
			return ret;
		}
	}
}

void CheerpWriter::compileGEPBase(const llvm::User* gep_inst, bool forEscapingPointer)
{
	SmallVector< const Value*, 8 > indices(std::next(gep_inst->op_begin()), gep_inst->op_end());
	Type* basePointerType = gep_inst->getOperand(0)->getType();
	Type* targetType = gep_inst->getType()->getPointerElementType();

	StructType* containerStructType = dyn_cast<StructType>(getGEPContainerType(gep_inst));
	bool useDownCastArray = false;
	if(containerStructType && indices.size() > 1)
	{
		assert(isa<ConstantInt>(indices.back()));
		const ConstantInt* idx = cast<ConstantInt>(indices.back());
		uint32_t lastOffsetConstant = idx->getZExtValue();
		useDownCastArray = !types.useWrapperArrayForMember(PA, containerStructType, lastOffsetConstant);
	}
	bool byteLayout = PA.getPointerKind(gep_inst) == BYTE_LAYOUT;
	if (byteLayout)
	{
		const Value* baseOperand = gep_inst->getOperand(0);
		bool byteLayoutFromHere = PA.getPointerKind(baseOperand) != BYTE_LAYOUT;
		if (byteLayoutFromHere)
			compileCompleteObject(gep_inst);
		else if (!TypeSupport::hasByteLayout(targetType) && forEscapingPointer)
		{
			assert(TypeSupport::isTypedArrayType(targetType, /* forceTypedArray*/ true));
			// Forge an appropiate typed array
			assert (!TypeSupport::hasByteLayout(targetType));
			stream << "new ";
			compileTypedArrayType(targetType);
			stream << '(';
			compilePointerBase( baseOperand );
			stream << ".buffer,";
			// If this GEP or a previous one passed through an array of immutables generate a regular from
			// the start of the array and not from the pointed element
			compileByteLayoutOffset( gep_inst, BYTE_LAYOUT_OFFSET_STOP_AT_ARRAY );
			stream << ')';
		}
		else
			compilePointerBase( baseOperand );
	}
	else if (indices.size() == 1)
	{
		// Just another pointer from this one
		compilePointerBase(gep_inst->getOperand(0));
	}
	else
	{
		// HACK: Accessing members of NULL is invalid, but it is used to compute an offset from the start of a structure
		// TODO: We need to detect and block this on the clang side. In the mean time, just compile an invalid null access
		if( isa<ConstantPointerNull>(gep_inst->getOperand(0)) )
		{
			stream << "null[0]";
			return;
		}
		compileCompleteObject(gep_inst->getOperand(0), indices.front());
		Type* basePointedType = basePointerType->getPointerElementType();
		if (useDownCastArray)
		{
			compileAccessToElement(basePointedType, makeArrayRef(std::next(indices.begin()),indices.end()), /*compileLastWrapperArray*/true);
			stream << ".a";
		}
		else if(containerStructType)
		{
			compileAccessToElement(basePointedType, makeArrayRef(std::next(indices.begin()),indices.end()), /*compileLastWrapperArray*/false);
		}
		else
		{
			compileAccessToElement(basePointedType, makeArrayRef(std::next(indices.begin()),std::prev(indices.end())), /*compileLastWrapperArray*/true);
		}
	}
}

void CheerpWriter::compileGEPOffset(const llvm::User* gep_inst, PARENT_PRIORITY parentPrio)
{
	SmallVector< const Value*, 8 > indices(std::next(gep_inst->op_begin()), gep_inst->op_end());
	Type* basePointerType = gep_inst->getOperand(0)->getType();
	Type* targetType = gep_inst->getType()->getPointerElementType();

	StructType* containerStructType = dyn_cast<StructType>(getGEPContainerType(gep_inst));
	bool useDownCastArray = false;
	if(containerStructType && indices.size() > 1)
	{
		assert(isa<ConstantInt>(indices.back()));
		const ConstantInt* idx = cast<ConstantInt>(indices.back());
		uint32_t lastOffsetConstant = idx->getZExtValue();
		useDownCastArray = !types.useWrapperArrayForMember(PA, containerStructType, lastOffsetConstant);
	}

	bool byteLayout = PA.getPointerKind(gep_inst) == BYTE_LAYOUT;
	if (byteLayout)
	{
		if (TypeSupport::hasByteLayout(targetType))
			compilePointerOffset( gep_inst, HIGHEST );
		else
		{
			assert(TypeSupport::isTypedArrayType(targetType, /* forceTypedArray*/ true));
			// If this GEP or a previous one passed through an array of immutables generate a regular from
			// the start of the array and not from the pointed element
			const Value* lastOffset = compileByteLayoutOffset( gep_inst, BYTE_LAYOUT_OFFSET_NO_PRINT );
			if (lastOffset)
				compileOperand(lastOffset);
			else
				stream << '0';
		}
	}
	else if (indices.size() == 1)
	{
		bool isOffsetConstantZero = isa<Constant>(indices.front()) && cast<Constant>(indices.front())->isNullValue();
		PARENT_PRIORITY prio = parentPrio;

		// Just another pointer from this one
		if (!isOffsetConstantZero)
		{
			if(parentPrio > BIT_OR) stream << '(';
			prio = ADD_SUB;
		}
		compilePointerOffset(gep_inst->getOperand(0), prio);

		if(!isOffsetConstantZero)
		{
			stream << '+';
			compileOperand(indices.front(), prio);
			stream << "|0";
			if(parentPrio > BIT_OR) stream << ')';
		}
	}
	else
	{
		if (useDownCastArray)
		{
			Type* basePointedType = basePointerType->getPointerElementType();
			compileCompleteObject(gep_inst->getOperand(0), indices.front());
			compileAccessToElement(basePointedType, makeArrayRef(std::next(indices.begin()), indices.end()), /*compileLastWrapperArray*/true);
			stream << ".o";
		}
		else
			compileOffsetForGEP(gep_inst->getOperand(0)->getType(), indices);
	}
}

void CheerpWriter::compileGEP(const llvm::User* gep_inst, POINTER_KIND kind, PARENT_PRIORITY parentPrio)
{
	SmallVector< const Value*, 8 > indices(std::next(gep_inst->op_begin()), gep_inst->op_end());
	Type* basePointerType = gep_inst->getOperand(0)->getType();

	StructType* containerStructType = dyn_cast<StructType>(GetElementPtrInst::getIndexedType(basePointerType->getPointerElementType(),
			makeArrayRef(const_cast<Value* const*>(indices.begin()),
				     const_cast<Value* const*>(indices.end() - 1))));
	if(containerStructType && indices.size() > 1)
	{
		assert(isa<ConstantInt>(indices.back()));
	}


	// TODO: we need this hack because PointerAnalyzer cannot correctly assign
	// the RAW kind to null pointers
	bool asmjs = currentFun && currentFun->getSection()==StringRef("asmjs");
	bool asmjs_nullptr = asmjs && isa<ConstantPointerNull>(gep_inst->getOperand(0));
	if (RAW == kind || asmjs_nullptr)
	{
		compileRawPointer(gep_inst, parentPrio);
	}
	else if(COMPLETE_OBJECT == kind)
	{
		const llvm::Instruction* I = dyn_cast<Instruction>(gep_inst->getOperand(0));
		if (I && !isInlineable(*I, PA) &&
			(isGEP(I) || isBitCast(I)) && PA.getPointerKind(I) == COMPLETE_OBJECT)
		{
			stream << namegen.getName(I);
		} else {
			compileCompleteObject(gep_inst->getOperand(0), indices.front());
		}
		compileAccessToElement(gep_inst->getOperand(0)->getType()->getPointerElementType(),
		                       makeArrayRef(std::next(indices.begin()), indices.end()), /*compileLastWrapperArray*/true);
	}
	else
	{
		if (PA.getConstantOffsetForPointer(gep_inst))
		{
			Type* basePointedType = basePointerType->getPointerElementType();
			compileCompleteObject(gep_inst->getOperand(0), indices.front());
			compileAccessToElement(basePointedType, makeArrayRef(std::next(indices.begin()),std::prev(indices.end())), /*compileLastWrapperArray*/false);
			return;
		}

		stream << "{d:";
		compilePointerBase( gep_inst, true);
		stream << ",o:";
		compilePointerOffset( gep_inst, LOWEST, true);
		stream << '}';
	}
}

void CheerpWriter::compileSignedInteger(const llvm::Value* v, bool forComparison, PARENT_PRIORITY parentPrio)
{
	//We anyway have to use 32 bits for sign extension to work
	uint32_t shiftAmount = 32-v->getType()->getIntegerBitWidth();
	if(const ConstantInt* C = dyn_cast<ConstantInt>(v))
	{
		if(forComparison)
			stream << (C->getSExtValue() << shiftAmount);
		else
			stream << C->getSExtValue();
		return;
	}
	PARENT_PRIORITY signedPrio = shiftAmount == 0 ? BIT_OR : SHIFT;
	if(parentPrio > signedPrio) stream << '(';
	if(shiftAmount==0)
	{
		//Use simpler code
		compileOperand(v, BIT_OR);
		stream << "|0";
	}
	else if(forComparison)
	{
		// When comparing two signed values we can avoid the right shift
		compileOperand(v, SHIFT);
		stream << "<<" << shiftAmount;
	}
	else
	{
		compileOperand(v, SHIFT);
		stream << "<<" << shiftAmount << ">>" << shiftAmount;
	}
	if(parentPrio > signedPrio) stream << ')';
}

void CheerpWriter::compileUnsignedInteger(const llvm::Value* v, bool forAsmJSComparison, PARENT_PRIORITY parentPrio, bool forceTruncation)
{
	if(const ConstantInt* C = dyn_cast<ConstantInt>(v))
	{
		stream << C->getZExtValue();
		return;
	}
	//We anyway have to use 32 bits for sign extension to work
	uint32_t initialSize = v->getType()->getIntegerBitWidth();
	if(initialSize == 32)
	{
		if(parentPrio > SHIFT) stream << '(';
		//Use simpler code
		compileOperand(v, SHIFT);
		stream << ">>>0";
		if(parentPrio > SHIFT) stream << ')';
	}
	else if(!forceTruncation && !needsUnsignedTruncation(v, /*asmjs, not fully accurate*/forAsmJSComparison))
	{
		if(forAsmJSComparison)
		{
			if(parentPrio > BIT_OR) stream << '(';
			compileOperand(v, BIT_OR);
			stream << "|0";
			if(parentPrio > BIT_OR) stream << ')';
		}
		else
			compileOperand(v, parentPrio);
	}
	else
	{
		if(parentPrio > BIT_AND) stream << '(';
		compileOperand(v, BIT_AND);
		stream << '&' << getMaskForBitWidth(initialSize);
		if(parentPrio > BIT_AND) stream << ')';
	}
}

/*
 * This can be used for both named instructions and inlined ones
 * NOTE: Call, Ret, Invoke are NEVER inlined
 */
CheerpWriter::COMPILE_INSTRUCTION_FEEDBACK CheerpWriter::compileInlineableInstruction(const Instruction& I, PARENT_PRIORITY parentPrio)
{
	bool asmjs = currentFun->getSection() == StringRef("asmjs");
	Registerize::REGISTER_KIND regKind = registerize.getRegKindFromType(I.getType(), asmjs);
	switch(I.getOpcode())
	{
		case Instruction::BitCast:
		{
			POINTER_KIND k=PA.getPointerKind(&I);
			compileBitCast(&I, k, parentPrio);
			return COMPILE_OK;
		}
		case Instruction::FPToSI:
		{
			const CastInst& ci = cast<CastInst>(I);
			stream << "~~";
			compileOperand(ci.getOperand(0), HIGHEST);
			return COMPILE_OK;
		}
		case Instruction::FPToUI:
		{
			// TODO: When we will keep track of signedness to avoid useless casts we will need to fix this
			const CastInst& ci = cast<CastInst>(I);
			//Cast to signed anyway
			stream << "~~";
			compileOperand(ci.getOperand(0), HIGHEST);
			return COMPILE_OK;
		}
		case Instruction::SIToFP:
		{
			const CastInst& ci = cast<CastInst>(I);
			if (needsFloatCoercion(regKind, parentPrio))
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
			else
				stream << "(+";
			compileSignedInteger(ci.getOperand(0), /*forComparison*/ false, HIGHEST);
			stream << ')';
			return COMPILE_OK;
		}
		case Instruction::UIToFP:
		{
			const CastInst& ci = cast<CastInst>(I);
			if (needsFloatCoercion(regKind, parentPrio))
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
			else
				stream << "(+";
			//We need to cast to unsigned before
			compileUnsignedInteger(ci.getOperand(0), /*forAsmJSComparison*/ false, HIGHEST, /*forceTruncation*/ true);
			stream << ')';
			return COMPILE_OK;
		}
		case Instruction::GetElementPtr:
		{
			const GetElementPtrInst& gep = cast<GetElementPtrInst>(I);
			Type* t=gep.getOperand(0)->getType();
			assert(t->isPointerTy());
			PointerType* ptrT=cast<PointerType>(t);

			if(TypeSupport::isClientType(ptrT->getElementType()))
			{
				//Client objects are just passed through
				compileOperand(gep.getOperand(0), parentPrio);
			}
			else if (!isInlineable(gep, PA) && PA.getPointerKind(&gep) == RAW)
			{
				compileRawPointer(&gep, parentPrio, /*forceGEP*/true);
			}
			else
			{
				compileGEP(&gep, PA.getPointerKind(&gep), parentPrio);
			}
			return COMPILE_OK;
		}
		case Instruction::Add:
		{
			//Integer addition
			PARENT_PRIORITY addPrio = ADD_SUB;
			if(needsIntCoercion(regKind, parentPrio))
				addPrio = BIT_OR;
			Value* lhs = I.getOperand(0);
			Value* rhs = I.getOperand(1);
			// TODO: Move negative constants on RHS
			if(parentPrio > addPrio) stream << '(';
			compileOperand(lhs, ADD_SUB);
			if(I.getType()->isIntegerTy(32) && isa<ConstantInt>(rhs) && cast<ConstantInt>(rhs)->isNegative())
			{
				// Special case negative constants, print them directly without adding an operator
				// NOTE: i8/i16 constants are always zero extended
				compileConstant(cast<ConstantInt>(rhs), LOWEST);
			}
			else
			{
				stream << "+";
				compileOperand(rhs, ADD_SUB);
			}
			if(addPrio == BIT_OR)
				stream << "|0";
			if(parentPrio > addPrio) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::FAdd:
		{
			//Floating point addition
			bool needsFround = needsFloatCoercion(regKind, parentPrio);
			if(needsFround)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
				parentPrio = FROUND;
			}
			if(parentPrio > ADD_SUB) stream << '(';
			compileOperand(I.getOperand(0), ADD_SUB);
			stream << '+';
			compileOperand(I.getOperand(1), nextPrio(ADD_SUB));
			if(parentPrio > ADD_SUB) stream << ')';
			if(needsFround)
				stream << ')';
			return COMPILE_OK;
		}
		case Instruction::Sub:
		{
			compileSubtraction(I.getOperand(0), I.getOperand(1), parentPrio);
			return COMPILE_OK;
		}
		case Instruction::FSub:
		{
			//Floating point subtraction
			bool needsFround = needsFloatCoercion(regKind, parentPrio);
			if(needsFround)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
				parentPrio = FROUND;
			}
			if(parentPrio > ADD_SUB) stream << '(';
			// Optimize negation
			if(!(isa<ConstantFP>(I.getOperand(0)) && cast<ConstantFP>(I.getOperand(0))->isZero()))
				compileOperand(I.getOperand(0), ADD_SUB);
			stream << '-';
			compileOperand(I.getOperand(1), nextPrio(ADD_SUB));
			if(parentPrio > ADD_SUB) stream << ')';
			if(needsFround)
				stream << ')';
			return COMPILE_OK;
		}
		case Instruction::ZExt:
		{
			const ZExtInst& bi = cast<ZExtInst>(I);
			Type* src=bi.getSrcTy();
#ifndef NDEBUG
			Type* dst=bi.getDestTy();
#endif
			assert(src->isIntegerTy() && dst->isIntegerTy());
			if(src->isIntegerTy(1) && !asmjs)
			{
				//If the source type is i1, attempt casting from Boolean
				if(parentPrio >= TERNARY) stream << '(';
				compileOperand(bi.getOperand(0), TERNARY);
				stream << "?1:0";
				if(parentPrio >= TERNARY) stream << ')';
			}
			else
			{
				//Let's mask out upper bits, to make sure we get zero extension
				//The value might have been initialized with a negative value
				compileUnsignedInteger(I.getOperand(0), /*forAsmJSComparison*/ false, parentPrio);
			}
			return COMPILE_OK;
		}
		case Instruction::SDiv:
		{
			//Integer signed division
			PARENT_PRIORITY sdivPrio = MUL_DIV;
			if(needsIntCoercion(regKind, parentPrio))
				sdivPrio = BIT_OR;
			if(parentPrio > sdivPrio) stream << '(';
			compileSignedInteger(I.getOperand(0), /*forComparison*/ false, MUL_DIV);
			stream << '/';
			compileSignedInteger(I.getOperand(1), /*forComparison*/ false, nextPrio(MUL_DIV));
			if(sdivPrio == BIT_OR)
				stream << "|0";
			if(parentPrio > sdivPrio) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::UDiv:
		{
			//Integer unsigned division
			PARENT_PRIORITY udivPrio = MUL_DIV;
			if(needsIntCoercion(regKind, parentPrio))
				udivPrio = BIT_OR;
			if(parentPrio > udivPrio) stream << '(';
			compileUnsignedInteger(I.getOperand(0), /*forAsmJSComparison*/ false, MUL_DIV);
			stream << '/';
			compileUnsignedInteger(I.getOperand(1), /*forAsmJSComparison*/ false, nextPrio(MUL_DIV));
			if(udivPrio == BIT_OR)
				stream << "|0";
			if(parentPrio > udivPrio) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::SRem:
		{
			//Integer signed remainder
			PARENT_PRIORITY sremPrio = MUL_DIV;
			if(needsIntCoercion(regKind, parentPrio))
				sremPrio = BIT_OR;
			if(parentPrio > sremPrio) stream << '(';
			compileSignedInteger(I.getOperand(0), /*forComparison*/ false, MUL_DIV);
			stream << '%';
			compileSignedInteger(I.getOperand(1), /*forComparison*/ false, nextPrio(MUL_DIV));
			if(sremPrio == BIT_OR)
				stream << "|0";
			if(parentPrio > sremPrio) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::URem:
		{
			//Integer unsigned remainder
			PARENT_PRIORITY uremPrio = MUL_DIV;
			if(needsIntCoercion(regKind, parentPrio))
				uremPrio = BIT_OR;
			if(parentPrio > uremPrio) stream << '(';
			compileUnsignedInteger(I.getOperand(0), /*forAsmJSComparison*/ false, MUL_DIV);
			stream << '%';
			compileUnsignedInteger(I.getOperand(1), /*forAsmJSComparison*/ false, nextPrio(MUL_DIV));
			if(uremPrio == BIT_OR)
				stream << "|0";
			if(parentPrio > uremPrio) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::FDiv:
		{
			//Floating point division
			bool needsFround = needsFloatCoercion(regKind, parentPrio);
			if(needsFround)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
				parentPrio = FROUND;
			}
			if(parentPrio > MUL_DIV) stream << '(';
			compileOperand(I.getOperand(0), MUL_DIV);
			stream << '/';
			compileOperand(I.getOperand(1), nextPrio(MUL_DIV));
			if(parentPrio > MUL_DIV) stream << ')';
			if(needsFround)
				stream << ')';
			return COMPILE_OK;
		}
		case Instruction::FRem:
		{
			//Floating point division remainder
			bool needsFround = needsFloatCoercion(regKind, parentPrio);
			if(needsFround)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
				parentPrio = FROUND;
			}
			if(parentPrio > MUL_DIV) stream << '(';
			// NOTE: Modulo on float is not properly supported by Asm.js
			if(regKind == Registerize::FLOAT)
			{
				stream << "+";
				compileOperand(I.getOperand(0), HIGHEST);
			}
			else
				compileOperand(I.getOperand(0), MUL_DIV);
			stream << '%';
			if(regKind == Registerize::FLOAT)
			{
				stream << "+";
				compileOperand(I.getOperand(1), HIGHEST);
			}
			else
				compileOperand(I.getOperand(1), nextPrio(MUL_DIV));
			if(parentPrio > MUL_DIV) stream << ')';
			if(needsFround)
				stream << ')';
			return COMPILE_OK;
		}
		case Instruction::Mul:
		{
			//Integer signed multiplication
			PARENT_PRIORITY mulPrio = MUL_DIV;
			// NOTE: V8 requires imul to be coerced with `|0` no matter what in asm.js
			if(needsIntCoercion(regKind, parentPrio) || asmjs)
				mulPrio = BIT_OR;
			// NOTE: V8 requires imul to be coerced to int like normal functions
			if(parentPrio > mulPrio) stream << '(';
			if(useMathImul || asmjs)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::IMUL) << '(';
				compileOperand(I.getOperand(0), LOWEST);
				stream << ',';
				compileOperand(I.getOperand(1), LOWEST);
				stream << ')';
			}
			else
			{
				compileOperand(I.getOperand(0), MUL_DIV);
				stream << '*';
				compileOperand(I.getOperand(1), MUL_DIV);
			}
			if(mulPrio == BIT_OR)
				stream << "|0";
			if(parentPrio > mulPrio) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::FMul:
		{
			//Floating point multiplication
			bool needsFround = needsFloatCoercion(regKind, parentPrio);
			if(needsFround)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
				parentPrio = FROUND;
			}
			if(parentPrio > MUL_DIV) stream << '(';
			compileOperand(I.getOperand(0), MUL_DIV);
			stream << '*';
			compileOperand(I.getOperand(1), nextPrio(MUL_DIV));
			if(parentPrio > MUL_DIV) stream << ')';
			if(needsFround)
				stream << ')';
			return COMPILE_OK;
		}
		case Instruction::ICmp:
		{
			//Integer comparison
			const CmpInst& ci = cast<CmpInst>(I);
			compileIntegerComparison(ci.getOperand(0), ci.getOperand(1), ci.getPredicate(), parentPrio);
			return COMPILE_OK;
		}
		case Instruction::FCmp:
		{
			//Float comparison
			const CmpInst& ci = cast<CmpInst>(I);
			compileFloatComparison(ci.getOperand(0), ci.getOperand(1), ci.getPredicate(), parentPrio, asmjs);
			return COMPILE_OK;
		}
		case Instruction::And:
		{
			//Integer logical and
			//No need to apply the >> operator. The result is an integer by spec
			PARENT_PRIORITY andPrio = (I.getType()->isIntegerTy(1)&&!asmjs) ? LOGICAL_AND : BIT_AND;
			if(parentPrio > andPrio) stream << '(';
			compileOperand(I.getOperand(0), andPrio, /*allowBooleanObjects*/ true);
			if(!asmjs && I.getType()->isIntegerTy(1))
				stream << "&&";
			else
				stream << '&';
			compileOperand(I.getOperand(1), andPrio, /*allowBooleanObjects*/ true);
			if(parentPrio > andPrio) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::LShr:
		{
			//Integer logical shift right
			PARENT_PRIORITY shiftPrio = SHIFT;
			int width = I.getOperand(0)->getType()->getIntegerBitWidth();
			if(parentPrio > SHIFT) stream << '(';
			bool needsTruncation = width != 32 && needsUnsignedTruncation(I.getOperand(0), asmjs);
			if(needsTruncation)
			{
				shiftPrio = BIT_AND;
				stream << '(';
			}
			compileOperand(I.getOperand(0), shiftPrio);
			if(needsTruncation)
				stream << '&' << getMaskForBitWidth(width) << ')';
			stream << ">>>";
			compileOperand(I.getOperand(1), nextPrio(SHIFT));
			if(parentPrio > SHIFT) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::AShr:
		{
			//Integer arithmetic shift right
			//No need to apply the >> operator. The result is an integer by spec
			if(parentPrio > SHIFT) stream << '(';
			if(types.isI32Type(I.getOperand(0)->getType()))
				compileOperand(I.getOperand(0), SHIFT);
			else
				compileSignedInteger(I.getOperand(0), /*forComparison*/ false, SHIFT);
			stream << ">>";
			compileOperand(I.getOperand(1), nextPrio(SHIFT));
			if(parentPrio > SHIFT) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::Shl:
		{
			//Integer shift left
			//No need to apply the >> operator. The result is an integer by spec
			if(parentPrio > SHIFT) stream << '(';
			compileOperand(I.getOperand(0), SHIFT);
			stream << "<<";
			compileOperand(I.getOperand(1), nextPrio(SHIFT));
			if(parentPrio > SHIFT) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::Or:
		{
			//Integer logical or
			//No need to apply the >> operator. The result is an integer by spec
			PARENT_PRIORITY orPrio = (!asmjs && I.getType()->isIntegerTy(1)) ? LOGICAL_OR : BIT_OR;
			if(parentPrio > orPrio) stream << '(';
			compileOperand(I.getOperand(0), orPrio, /*allowBooleanObjects*/ true);
			//If the type is i1 we can use the boolean operator to take advantage of logic short-circuit
			//This is possible because we know that instruction with side effects, like calls, are never inlined
			if(!asmjs && I.getType()->isIntegerTy(1))
				stream << "||";
			else
				stream << '|';
			compileOperand(I.getOperand(1), orPrio, /*allowBooleanObjects*/ true);
			if(parentPrio > orPrio) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::Xor:
		{
			//Integer logical xor
			//Xor with 1s is used to implement bitwise and logical negation
			//TODO: Optimize the operation with 1s
			//No need to apply the >> operator. The result is an integer by spec
			if(parentPrio > BIT_XOR) stream << '(';
			compileOperand(I.getOperand(0), BIT_XOR);
			stream << '^';
			compileOperand(I.getOperand(1), BIT_XOR);
			if(parentPrio > BIT_XOR) stream << ')';
			return COMPILE_OK;
		}
		case Instruction::Trunc:
		{
			compileOperand(I.getOperand(0), parentPrio);
			return COMPILE_OK;
		}
		case Instruction::SExt:
		{
			//We can use a couple of shift to make this work
			compileSignedInteger(I.getOperand(0), /*forComparison*/ false, parentPrio);
			return COMPILE_OK;
		}
		case Instruction::Select:
		{
			const SelectInst& si = cast<SelectInst>(I);
			if(si.getType()->isPointerTy() && PA.getPointerKind(&si) == SPLIT_REGULAR)
			{
				compileOperand(si.getOperand(0), TERNARY, /*allowBooleanObjects*/ true);
				stream << '?';
				compilePointerOffset(si.getOperand(1), TERNARY);
				stream << ':';
				compilePointerOffset(si.getOperand(2), TERNARY);
				stream << ';' << NewLine;
				stream << namegen.getName(&si) << '=';
				compileOperand(si.getOperand(0), TERNARY, /*allowBooleanObjects*/ true);
				stream << '?';
				compilePointerBase(si.getOperand(1));
				stream << ':';
				compilePointerBase(si.getOperand(2));
			}
			else
			{
				// We need to protect the outside RHS from being absorbed by the rightmost part of the select
				if(parentPrio != LOWEST)
					stream << "(";
				compileSelect(&si, si.getCondition(), si.getTrueValue(), si.getFalseValue(), LOWEST);
				if(parentPrio != LOWEST)
					stream << ")";
			}
			return COMPILE_OK;
		}
		case Instruction::ExtractValue:
		{
			const ExtractValueInst& evi = cast<ExtractValueInst>(I);
			const Value* aggr=evi.getAggregateOperand();
			Type* t=aggr->getType();
			if(!t->isStructTy())
			{
				llvm::errs() << "extractvalue: Expected struct, found " << *t << "\n";
				llvm::report_fatal_error("Unsupported code found, please report a bug", false);
				return COMPILE_OK;
			}
			assert(!isa<UndefValue>(aggr));

			compileOperand(aggr, HIGHEST);

			uint32_t offset=evi.getIndices()[0];
			stream << '.' << types.getPrefixCharForMember(PA, cast<StructType>(t), offset) << offset;
			if(types.useWrapperArrayForMember(PA, cast<StructType>(t), offset))
				stream << "[0]";
			return COMPILE_OK;
		}
		case Instruction::FPExt:
		{
			const Value* src=I.getOperand(0);
			if(asmjs)
			{
				parentPrio = LOWEST;
				stream << "(+(";
			}
			compileOperand(src, parentPrio);
			if(asmjs)
				stream << "))";
			return COMPILE_OK;
		}
		case Instruction::FPTrunc:
		{
			const Value* src=I.getOperand(0);
			if(useMathFround)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
				parentPrio = FROUND;
			}
			compileOperand(src, parentPrio);
			if(useMathFround)
				stream << ')';
			return COMPILE_OK;
		}
		case Instruction::PtrToInt:
		{
			const PtrToIntInst& pi=cast<PtrToIntInst>(I);
			compilePtrToInt(pi.getOperand(0));
			return COMPILE_OK;
		}
		case Instruction::VAArg:
		{
			const VAArgInst& vi=cast<VAArgInst>(I);
			if (asmjs)
			{
				// floats are promoted to double as per standard
				if (vi.getType()->isFloatingPointTy())
					stream<< '+' << heapNames[HEAPF64];
				// int8 and int16 are promoted to int32 as per standard
				else if (vi.getType()->isIntegerTy() || vi.getType()->isPointerTy())
					stream << heapNames[HEAP32];
				stream << '[';
				compileHeapAccess(vi.getPointerOperand());
				if (vi.getType()->isIntegerTy() || vi.getType()->isPointerTy() || vi.getType()->isFloatTy())
					stream << ">>2]|0";
				else
					stream << ">>3]";
				stream << ';' << NewLine;

				compileHeapAccess(vi.getPointerOperand());
				stream << "=((";
				compileHeapAccess(vi.getPointerOperand());
				stream << "|0)+8)|0";
			}
			else
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::HANDLE_VAARG) << "(";
				compileCompleteObject(vi.getPointerOperand());
				stream << ')';

				assert( globalDeps.needHandleVAArg() );
			}
			return COMPILE_OK;
		}
		case Instruction::Call:
		{
			const CallInst& ci = cast<CallInst>(I);
			const Function * calledFunc = ci.getCalledFunction();
			const Value * calledValue = ci.getCalledValue();
			const PointerType* pTy = cast<PointerType>(calledValue->getType());
			const FunctionType* fTy = cast<FunctionType>(pTy->getElementType());
			// Skip over bitcasts of function
			if(isa<ConstantExpr>(calledValue) && cast<ConstantExpr>(calledValue)->getOpcode() == Instruction::BitCast)
			{
				calledValue = cast<User>(calledValue)->getOperand(0);
				calledFunc = dyn_cast<Function>(calledValue);
			}
			const Type* retTy = fTy->getReturnType();
			// NOTE: if the type is void, OBJECT is returned, but we explicitly
			// check the void case later
			Registerize::REGISTER_KIND kind = registerize.getRegKindFromType(retTy, asmjs);
			if(!retTy->isVoidTy())
			{
				if(kind == Registerize::DOUBLE)
				{
					if(parentPrio > LOWEST)
						stream << ' ';
					stream << '+';
				}
				else if(kind == Registerize::FLOAT)
				{
					stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
				}
				else if(kind == Registerize::INTEGER && parentPrio > BIT_OR)
				{
					stream << '(';
				}
			}
			if(calledFunc)
			{
				COMPILE_INSTRUCTION_FEEDBACK cf=handleBuiltinCall(&ci, calledFunc);
				if(cf!=COMPILE_UNSUPPORTED)
				{
					if (!retTy->isVectorTy() && (
						(kind == Registerize::INTEGER && parentPrio > BIT_OR) ||
						kind == Registerize::FLOAT))
					{
						stream << ')';
					}
					return cf;
				}
				stream << namegen.getName(calledFunc);
			}
			else if (ci.isInlineAsm())
			{
				compileInlineAsm(ci);
				//If we are dealing with inline asm we are done, close coercions
				switch(kind)
				{
					case Registerize::INTEGER:
						stream << "|0";
						if(parentPrio > BIT_OR)
							stream << ')';
						break;
					case Registerize::DOUBLE:
						break;
					case Registerize::FLOAT:
						stream << ')';
						break;
					case Registerize::OBJECT:
						break;
				}
				return COMPILE_OK;
			}
			else if (asmjs)
			{
				//Indirect call, asm.js mode
				if (!linearHelper.getFunctionTables().count(fTy))
				{
					stream << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY);
				}
				else
				{
					const auto& table = linearHelper.getFunctionTables().at(fTy);
					stream << table.name << '[';
					// NOTE: V8 does not like constants here, so we add a useless
					// ternary operator to make it happy.
					if (const Constant* c = dyn_cast<Constant>(calledValue))
					{
						stream << "(0!=0?0:";
						compileConstant(c);
						stream << ')';
					}
					else
					{
						compileRawPointer(calledValue, PARENT_PRIORITY::BIT_AND);
					}
					stream << '&' << linearHelper.getFunctionAddressMask(fTy) << ']';
				}

			}
			else
			{
				//Indirect call, normal mode
				compilePointerAs(calledValue, COMPLETE_OBJECT);
			}

			{
				// In calling asmjs functions the varargs are passed on the stack
				bool asmJSCallingConvention = asmjs || (calledFunc && calledFunc->getSection() == StringRef("asmjs"));
				size_t n = asmJSCallingConvention ? fTy->getNumParams() : ci.getNumArgOperands();
				compileMethodArgs(ci.op_begin(),ci.op_begin()+n, &ci, /*forceBoolean*/ false);
			}
			if(!retTy->isVoidTy())
			{
				switch(kind)
				{
					case Registerize::INTEGER:
						stream << "|0";
						if(parentPrio > BIT_OR)
							stream << ')';
						break;
					case Registerize::DOUBLE:
						break;
					case Registerize::FLOAT:
						stream << ')';
						break;
					case Registerize::OBJECT:
						if(PA.getPointerKind(&ci) == SPLIT_REGULAR && !ci.use_empty())
						{
							assert(!isInlineable(ci, PA));
							stream << ';' << NewLine;
							stream << namegen.getSecondaryName(&ci) << "=oSlot";
						}
						break;
				}
			}
			return COMPILE_OK;
		}
		case Instruction::Load:
		{
			const LoadInst& li = cast<LoadInst>(I);
			const Value* ptrOp=li.getPointerOperand();
			bool asmjs = currentFun->getSection()==StringRef("asmjs");
			POINTER_KIND kind = PA.getPointerKind(ptrOp);
			bool needsOffset = !li.use_empty() && li.getType()->isPointerTy() && PA.getPointerKind(&li) == SPLIT_REGULAR && !PA.getConstantOffsetForPointer(&li);
			bool needsCheckBounds = false;
			if (checkBounds)
			{
				if(kind == REGULAR || kind == SPLIT_REGULAR)
				{
					needsCheckBounds = true;
					stream<<"(";
					compileCheckBounds(ptrOp);
					stream<<",";
				}
				else if(kind == COMPLETE_OBJECT && isGEP(ptrOp))
				{
					needsCheckBounds = true;
					stream<<"(";
					compileCheckDefined(ptrOp, needsOffset);
					stream<<",";
				}
				else if(kind == RAW)
				{
					needsCheckBounds = true;
					stream<<"(";
					compileCheckBoundsAsmJS(ptrOp, targetData.getTypeAllocSize(li.getType())-1);
					stream<<",";
				}
			}
			Registerize::REGISTER_KIND regKind = registerize.getRegKindFromType(li.getType(),asmjs);
			if(regKind==Registerize::INTEGER && needsIntCoercion(regKind, parentPrio))
			{
				if (parentPrio > BIT_OR)
					stream << '(';
			}
			else if(regKind==Registerize::DOUBLE)
			{
				if (parentPrio > LOWEST)
					stream << ' ';
				stream << '+';
			}
			else if(needsFloatCoercion(regKind, parentPrio))
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
			}

			if (asmjs || kind == RAW)
			{
				compileHeapAccess(ptrOp);
			}
			else if (kind == BYTE_LAYOUT)
			{
				//Optimize loads of single values from unions
				compilePointerBase(ptrOp);
				Type* pointedType=ptrOp->getType()->getPointerElementType();
				if(pointedType->isIntegerTy(8))
					stream << ".getUint8(";
				else if(pointedType->isIntegerTy(16))
					stream << ".getUint16(";
				else if(pointedType->isIntegerTy(32))
					stream << ".getInt32(";
				else if(pointedType->isFloatTy())
					stream << ".getFloat32(";
				else if(pointedType->isDoubleTy())
					stream << ".getFloat64(";
				compilePointerOffset(ptrOp, LOWEST);
				if(!pointedType->isIntegerTy(8))
					stream << ",true";
				stream << ')';
			}
			else
				compileCompleteObject(ptrOp);
			if(needsOffset)
			{
				assert(!isInlineable(li, PA));
				if(kind == RAW)
				{
					int shift =  getHeapShiftForType(cast<PointerType>(li.getType())->getPointerElementType());
					if (shift != 0)
						stream << ">>" << shift;
				}
				else
				{
					stream <<'o';
				}
				if(needsCheckBounds)
				{
					// Close the bounds check here
					stream << ")";
					needsCheckBounds = false;
				}
				stream << ';' << NewLine;
				stream << namegen.getName(&li) << '=';
				if(kind == RAW)
					compileHeapForType(cast<PointerType>(li.getType())->getPointerElementType());
				else
					compileCompleteObject(ptrOp);
			}
			if(regKind==Registerize::INTEGER && needsIntCoercion(regKind, parentPrio))
			{
				stream << "|0";
				if (parentPrio > BIT_OR)
					stream << ')';
			}
			else if(needsFloatCoercion(regKind, parentPrio))
			{
				stream << ')';
			}
			if (needsCheckBounds)
				stream<<')';
			return COMPILE_OK;
		}
		case Instruction::IntToPtr:
		{
			if (asmjs)
			{
				compileOperand(I.getOperand(0));
				return COMPILE_OK;
			}
			// FALLTHROUGH if !asmjs
		}
		default:
			stream << "alert('Unsupported code')";
			llvm::errs() << "\tImplement inst " << I.getOpcodeName() << '\n';
			return COMPILE_UNSUPPORTED;
	}
}

void CheerpWriter::compileBB(const BasicBlock& BB)
{
	BasicBlock::const_iterator I=BB.begin();
	BasicBlock::const_iterator IE=BB.end();
	bool emptyBlock = true;
	for(;I!=IE;++I)
	{
		if(isInlineable(*I, PA))
			continue;
		if(const PHINode* phi = dyn_cast<PHINode>(I))
		{
			if(!canDelayPHI(phi, PA, registerize))
				continue;
		}
		const DebugLoc& debugLoc = I->getDebugLoc();
		if(sourceMapGenerator)
		{
			if(debugLoc)
				sourceMapGenerator->setDebugLoc(&debugLoc);
			else
				sourceMapGenerator->setDebugLoc(nullptr);
		}
		bool isDowncast = false;
		if(const IntrinsicInst* II=dyn_cast<IntrinsicInst>(&(*I)))
		{
			//Skip some kind of intrinsics
			if(II->getIntrinsicID()==Intrinsic::lifetime_start ||
				II->getIntrinsicID()==Intrinsic::lifetime_end ||
				II->getIntrinsicID()==Intrinsic::dbg_declare ||
				II->getIntrinsicID()==Intrinsic::dbg_value ||
				II->getIntrinsicID()==Intrinsic::assume)
			{
				continue;
			}
			else if(II->getIntrinsicID()==Intrinsic::cheerp_downcast)
				isDowncast = true;
		}
		if(!I->use_empty())
		{
			if(I->getType()->isPointerTy() && (I->getOpcode() != Instruction::Call || isDowncast) && PA.getPointerKind(I) == SPLIT_REGULAR && !PA.getConstantOffsetForPointer(I))
			{
				stream << namegen.getSecondaryName(I) << '=';
			}
			else if(!I->getType()->isVoidTy())
			{
				stream << namegen.getName(I) << '=';
			}
		}
		if(I->isTerminator())
		{
			auto ret = compileTerminatorInstruction(*dyn_cast<TerminatorInst>(I));
			if (ret == COMPILE_OK)
				emptyBlock = false;
		}
		else if(!I->use_empty() || I->mayHaveSideEffects())
		{
			COMPILE_INSTRUCTION_FEEDBACK ret=compileNotInlineableInstruction(*I, LOWEST);

			if(ret==COMPILE_OK)
			{
				stream << ';' << NewLine;
				emptyBlock = false;
			}
			else if(ret==COMPILE_UNSUPPORTED)
			{
				//Stop basic block compilation
				return;
			}
		}
	}
	if (emptyBlock && !isNumStatementsLessThan<1>(&BB, PA, registerize) && lastDepth0Block != &BB)
	{
		stream << ';' << NewLine;
	}
}

bool CheerpWriter::isInlineableInstruction(const Value* v) const
{
	if(const Instruction* I = dyn_cast<Instruction>(v))
		return isInlineable(*I, PA);
	else
		return false;
}

void CheerpRenderInterface::renderBlock(const BasicBlock* bb)
{
	if(writer->blockDepth == 0)
		writer->lastDepth0Block = bb;
	else
		writer->lastDepth0Block = nullptr;
	writer->compileBB(*bb);
}

void CheerpRenderInterface::renderCondition(const BasicBlock* bb, int branchId, CheerpWriter::PARENT_PRIORITY parentPrio, bool booleanInvert)
{
	const TerminatorInst* term=bb->getTerminator();

	bool asmjs = bb->getParent()->getSection() == StringRef("asmjs");
	if(isa<BranchInst>(term))
	{
		const BranchInst* bi=cast<BranchInst>(term);
		assert(bi->isConditional());
		//The second branch is the default
		assert(branchId==0);
		const Value* cond = bi->getCondition();
		bool canInvertCond = writer->isInlineableInstruction(cond);
		if(canInvertCond && isa<ICmpInst>(cond))
		{
			const CmpInst* ci = cast<CmpInst>(cond);
			CmpInst::Predicate p = ci->getPredicate();
			if(booleanInvert)
				p = CmpInst::getInversePredicate(p);
			writer->compileIntegerComparison(ci->getOperand(0), ci->getOperand(1), p, parentPrio);
		}
		else if(canInvertCond && isa<FCmpInst>(cond))
		{
			const CmpInst* ci = cast<CmpInst>(cond);
			CmpInst::Predicate p = ci->getPredicate();
			if(booleanInvert)
				p = CmpInst::getInversePredicate(p);
			writer->compileFloatComparison(ci->getOperand(0), ci->getOperand(1), p, parentPrio, asmjs);
		}
		else
		{
			if(booleanInvert)
				writer->stream << "!(";
			writer->compileOperand(cond, parentPrio, /*allowBooleanObjects*/ true);
			if(booleanInvert)
				writer->stream << ")";
		}
	}
	else if(isa<SwitchInst>(term))
	{
		const SwitchInst* si=cast<SwitchInst>(term);
		assert(branchId > 0);
		SwitchInst::ConstCaseIt it=si->case_begin();
		for(int i=1;i<branchId;i++)
			++it;
		StringRef compareString;
		StringRef joinString;
		if(booleanInvert)
		{
			if(asmjs)
			{
				compareString = "!=";
				joinString = "&";
			}
			else
			{
				compareString = "!==";
				joinString = "&&";
			}
		}
		else
		{
			if(asmjs)
			{
				compareString = "==";
				joinString = "|";
			}
			else
			{
				compareString = "===";
				joinString = "||";
			}
		}
		const BasicBlock* dest=it.getCaseSuccessor();
		writer->compileOperandForIntegerPredicate(si->getCondition(), CmpInst::ICMP_EQ, CheerpWriter::COMPARISON);
		writer->stream << compareString;
		writer->compileOperandForIntegerPredicate(it.getCaseValue(), CmpInst::ICMP_EQ, CheerpWriter::COMPARISON);
		//We found the destination, there may be more cases for the same
		//destination though
		for(++it;it!=si->case_end();++it)
		{
			if(it.getCaseSuccessor()==dest)
			{
				//Also add this condition
				writer->stream << joinString;
				writer->compileOperandForIntegerPredicate(si->getCondition(), CmpInst::ICMP_EQ, CheerpWriter::COMPARISON);
				writer->stream << compareString;
				writer->compileOperandForIntegerPredicate(it.getCaseValue(), CmpInst::ICMP_EQ, CheerpWriter::COMPARISON);
			}
		}
	}
	else
	{
		term->dump();
		llvm::report_fatal_error("Unsupported code found, please report a bug", false);
	}
}

void CheerpRenderInterface::renderLabelForSwitch(int labelId)
{
	writer->stream << 'L' << labelId << ':';
}
void CheerpRenderInterface::renderSwitchOnLabel(IdShapeMap& idShapeMap)
{
	writer->stream << "switch(" << labelName;
	if (asmjs)
		writer->stream << "|0";
	writer->stream << "){" << NewLine;
	writer->blockDepth++;
}
void CheerpRenderInterface::renderCaseOnLabel(int labelId)
{
	writer->stream << "case ";
	writer->stream << labelId << ":{" << NewLine;
	writer->blockDepth++;
}
void CheerpRenderInterface::renderSwitchBlockBegin(const SwitchInst* switchInst,
		BlockBranchMap& branchesOut)
{
	const Value* cond = switchInst->getCondition();
	writer->stream << "switch(";
	writer->compileOperandForIntegerPredicate(cond, CmpInst::ICMP_EQ, CheerpWriter::LOWEST);
	writer->stream << "){" << NewLine;
	writer->blockDepth++;
}
void CheerpRenderInterface::renderCaseBlockBegin(const BasicBlock* bb, int branchId)
{
	const TerminatorInst* term = bb->getTerminator();
	assert(isa<SwitchInst>(term));
	const SwitchInst* si=cast<SwitchInst>(term);
	assert(branchId > 0);
	SwitchInst::ConstCaseIt it=si->case_begin();
	for(int i=1;i<branchId;i++)
		++it;
	writer->stream << "case ";
	writer->compileOperandForIntegerPredicate(it.getCaseValue(), CmpInst::ICMP_EQ, CheerpWriter::LOWEST);
	writer->stream << ':' << NewLine;
	//We found the destination, there may be more cases for the same
	//destination though
	const BasicBlock* dest=it.getCaseSuccessor();
	for(++it;it!=si->case_end();++it)
	{
		if(it.getCaseSuccessor()==dest)
		{
			writer->stream << "case ";
			writer->compileOperandForIntegerPredicate(it.getCaseValue(), CmpInst::ICMP_EQ, CheerpWriter::LOWEST);
			writer->stream << ':' << NewLine;
		}
	}
	writer->stream << '{' << NewLine;
	writer->blockDepth++;
}
void CheerpRenderInterface::renderDefaultBlockBegin(bool empty)
{
	if (!empty)
	{
		writer->stream << "default:{" << NewLine;
		writer->blockDepth++;
	}
}
void CheerpRenderInterface::renderIfBlockBegin(const BasicBlock* bb, int branchId, bool first, int labelId)
{
	if(!first)
		writer->stream << "}else ";
	else
	{
		if (labelId > 0)
		{
			writer->stream << 'L' << labelId << ':';
			if (asmjs)
				writer->stream << '{';
		}
		writer->blockDepth++;
	}
	writer->stream << "if(";
	renderCondition(bb, branchId, CheerpWriter::LOWEST, /*booleanInvert*/false);
	writer->stream << "){" << NewLine;
}

void CheerpRenderInterface::renderIfBlockBegin(const BasicBlock* bb, const std::vector<int>& skipBranchIds, bool first, int labelId)
{
	if(!first)
		writer->stream << "}else ";
	else
	{
		if (labelId > 0)
		{
			writer->stream << 'L' << labelId << ':';
			if (asmjs)
				writer->stream << '{';
		}
		writer->blockDepth++;
	}
	writer->stream << "if(";
	for(uint32_t i=0;i<skipBranchIds.size();i++)
	{
		if(i!=0)
		{
			if (asmjs)
				writer->stream << "&";
			else
				writer->stream << "&&";
		}
		renderCondition(bb, skipBranchIds[i], skipBranchIds.size() == 1 ? CheerpWriter::LOWEST : CheerpWriter::LOGICAL_AND, /*booleanInvert*/true);
	}
	writer->stream << "){" << NewLine;
}

void CheerpRenderInterface::renderElseBlockBegin()
{
	writer->stream << "}else{" << NewLine;
}

void CheerpRenderInterface::renderIfBlockEnd(bool labelled)
{
	writer->stream << '}';
	if (labelled && asmjs)
		writer->stream << '}';
	writer->stream << NewLine;
	writer->blockDepth--;
}

void CheerpRenderInterface::renderBlockEnd(bool empty)
{
	if (!empty)
	{
		writer->stream << '}' << NewLine;
		writer->blockDepth--;
	}
}

void CheerpRenderInterface::renderBlockPrologue(const BasicBlock* bbTo, const BasicBlock* bbFrom)
{
	writer->compilePHIOfBlockFromOtherBlock(bbTo, bbFrom);
}

void CheerpRenderInterface::renderWhileBlockBegin()
{
	writer->stream << "while(1){" << NewLine;
	writer->blockDepth++;
}

void CheerpRenderInterface::renderWhileBlockBegin(int blockLabel)
{
	writer->stream << 'L' << blockLabel << ':';
	renderWhileBlockBegin();
}

void CheerpRenderInterface::renderDoBlockBegin()
{
	writer->stream << "do{" << NewLine;
	writer->blockDepth++;
}

void CheerpRenderInterface::renderDoBlockBegin(int blockLabel)
{
	writer->stream << 'L' << blockLabel << ':';
	renderDoBlockBegin();
}

void CheerpRenderInterface::renderDoBlockEnd()
{
	writer->stream << "}while(0);" << NewLine;
	writer->blockDepth--;
}

void CheerpRenderInterface::renderBlockBegin(int blockLabel)
{
	writer->stream << 'L' << blockLabel << ":{" << NewLine;
	writer->blockDepth++;
}

void CheerpRenderInterface::renderBreak()
{
	writer->stream << "break;" << NewLine;
}

void CheerpRenderInterface::renderBreak(int labelId)
{
	writer->stream << "break L" << labelId << ';' << NewLine;
}

void CheerpRenderInterface::renderContinue()
{
	writer->stream << "continue;" << NewLine;
}

void CheerpRenderInterface::renderContinue(int labelId)
{
	writer->stream << "continue L" << labelId << ';' << NewLine;
}

void CheerpRenderInterface::renderLabel(int labelId)
{
	writer->stream << labelName << "=" << labelId << "|0;" << NewLine;
}

void CheerpRenderInterface::renderIfOnLabel(int labelId, bool first)
{
	if(first==false)
		writer->stream << "else ";
	writer->stream << "if(" << labelName;
	if (asmjs)
		writer->stream << ">>>0==" << labelId << ">>>0){" << NewLine;
	else
		writer->stream << "===" << labelId << "){" << NewLine;
	writer->blockDepth++;
}

void CheerpWriter::compileMethodLocal(StringRef name, Registerize::REGISTER_KIND kind)
{
	stream << name << '=';
	if(kind == Registerize::INTEGER)
		stream << '0';
	else if(kind == Registerize::DOUBLE)
	{
		// NOTE: V8 requires the `.` to identify it as a double in asm.js
		stream << "-0.";
	}
	else if(kind == Registerize::FLOAT)
		stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << "(0.)";
	else
		stream << "null";
}

void CheerpWriter::compileMethodLocals(const Function& F, bool needsLabel)
{
	// Declare are all used locals in the beginning
	bool firstVar = true;
	if(needsLabel)
	{
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::LABEL) << "=0";
		firstVar = false;
	}
	const std::vector<Registerize::RegisterInfo>& regsInfo = registerize.getRegistersForFunction(&F);
	for(unsigned int regId = 0; regId < regsInfo.size(); regId++)
	{
		if(firstVar)
			stream << "var ";
		else
			stream << ',';
		compileMethodLocal(namegen.getName(&F, regId), regsInfo[regId].regKind);
		firstVar = false;
		if(regsInfo[regId].needsSecondaryName)
		{
			stream << ',';
			compileMethodLocal(namegen.getSecondaryName(&F, regId), Registerize::INTEGER);
		}
	}
	if(!firstVar)
		stream << ';' << NewLine;
}

void CheerpWriter::compileCondition(const BasicBlock* BB, bool booleanInvert)
{
	const TerminatorInst* term=BB->getTerminator();
	bool asmjs = BB->getParent()->getSection() == StringRef("asmjs");
	assert(isa<BranchInst>(term));
	const BranchInst* bi=cast<BranchInst>(term);
	assert(bi->isConditional());
	const Value* cond = bi->getCondition();
	bool canInvertCond = isInlineableInstruction(cond);
	if(canInvertCond && isa<ICmpInst>(cond))
	{
		const CmpInst* ci = cast<CmpInst>(cond);
		CmpInst::Predicate p = ci->getPredicate();
		if(booleanInvert)
			p = CmpInst::getInversePredicate(p);
		compileIntegerComparison(ci->getOperand(0), ci->getOperand(1), p, PARENT_PRIORITY::LOWEST);
	}
	else if(canInvertCond && isa<FCmpInst>(cond))
	{
		const CmpInst* ci = cast<CmpInst>(cond);
		CmpInst::Predicate p = ci->getPredicate();
		if(booleanInvert)
			p = CmpInst::getInversePredicate(p);
		compileFloatComparison(ci->getOperand(0), ci->getOperand(1), p, PARENT_PRIORITY::LOWEST, asmjs);
	}
	else
	{
		if(booleanInvert)
			stream << "!(";
		compileOperand(cond, PARENT_PRIORITY::LOWEST, /*allowBooleanObjects*/ true);
		if(booleanInvert)
			stream << ")";
	}
}

static DenseSet<const Token*> getLabeledTokens(const TokenList& Tokens)
{
	std::vector<const Token*> ScopeStack;
	// First, compute which Tokens need a label
	DenseSet<const Token*> LabeledTokens;
	for (const Token& T: Tokens)
	{
		switch (T.getKind())
		{
			case Token::TK_BasicBlock:
			case Token::TK_Block:
			case Token::TK_Case:
			case Token::TK_If:
			case Token::TK_IfNot:
			case Token::TK_Else:
			case Token::TK_Prologue:
			case Token::TK_Condition:
			case Token::TK_BrIf:
			case Token::TK_BrIfNot:
				break;
			case Token::TK_Loop:
			case Token::TK_Switch:
				ScopeStack.push_back(&T);
				break;
			case Token::TK_Branch:
			{
				const Token* Target = T.getMatch();
				if (Target->getKind() == Token::TK_End)
					Target = Target->getMatch();
				if ((Target->getKind() & (Token::TK_Block|Token::TK_If|Token::TK_IfNot))
					|| Target != ScopeStack.back())
					LabeledTokens.insert(Target);
				break;
			}
			case Token::TK_End:
				if (T.getMatch()->getKind() == Token::TK_Loop
					|| T.getMatch()->getKind() == Token::TK_Switch)
				{
					ScopeStack.pop_back();
				}
				break;
			case Token::TK_Invalid:
				report_fatal_error("Invalid token found");
				break;
		}
	}
	assert(ScopeStack.empty());
	return LabeledTokens;
}
static bool omitBraces(const Token& T, const PointerAnalyzer& PA, const Registerize& registerize)
{
	assert(T.getKind()&(Token::TK_If|Token::TK_IfNot|Token::TK_Else));
	const Token* Inner = T.getNextNode();
	const Token* End = T.getMatch();
	// Empty if. Ideally it should have been removed by now...
	if (End == Inner)
		return true;
	switch (Inner->getKind())
	{
		case Token::TK_Prologue:
		{
			return false;
		}
		case Token::TK_BasicBlock:
		{
			if (Inner->getNextNode() != End)
				return false;
			return isNumStatementsLessThan<2>(Inner->getBB(), PA, registerize);
		}
		case Token::TK_Block:
		case Token::TK_Loop:
		case Token::TK_Switch:
		{
			return Inner->getMatch()->getNextNode() == End;
		}
		case Token::TK_If:
		case Token::TK_IfNot:
		{
			if (End->getKind() == Token::TK_Else)
				return false;
			else if (Inner->getMatch()->getKind() == Token::TK_Else)
				return Inner->getMatch()->getMatch()->getNextNode() == End;
			else
				return Inner->getMatch()->getNextNode() == End;
		}
		case Token::TK_Branch:
		{
			return Inner->getNextNode() == End;
		}
		default:
		{
			llvm_unreachable("Unexpected Token");
		}
	} 
}

class LabelNameGenerator
{
	DenseMap<const Token*, uint32_t> Labels;
	std::vector<SmallString<2>> LabelList;
	uint32_t NextLabel{0};
	std::vector<std::string> External;
	name_iterator<JSSymbols, 2> NameIt{JSSymbols(External)};
public:
	using iterator = std::vector<SmallString<2>>::iterator;
	iterator end()
	{
		return LabelList.end();
	}
	const SmallString<2>& allocate(const Token* T)
	{
		if (NextLabel == LabelList.size())
		{
			LabelList.push_back(*NameIt);
			++NameIt;
		}
		Labels.insert(std::make_pair(T, NextLabel));
		return LabelList[NextLabel++];
	}
	void deallocate()
	{
		NextLabel--;
	}
	iterator get(const Token* T)
	{
		auto it = Labels.find(T);
		if (it == Labels.end())
			return end();
		return LabelList.begin()+it->second;
	}
};

void CheerpWriter::compileTokens(const TokenList& Tokens)
{
	auto LabeledTokens = getLabeledTokens(Tokens);
	LabelNameGenerator LabelGen;
	for (auto it = Tokens.begin(), ie = Tokens.end(); it != ie; ++it)
	{
		const Token& T = *it;
		bool Labeled = LabeledTokens.count(&T);
		if (Labeled)
		{
			auto Label = LabelGen.allocate(&T);
			stream << Label << ':';
		}
		switch (T.getKind())
		{
			case Token::TK_BasicBlock:
			{
				if(blockDepth == 0)
					lastDepth0Block = T.getBB();
				else
					lastDepth0Block = nullptr;
				compileBB(*T.getBB());
				break;
			}
			case Token::TK_Loop:
			{
				stream << "while(1){" << NewLine;
				blockDepth++;
				break;
			}
			case Token::TK_Block:
			{
				stream << '{' << NewLine;
				blockDepth++;
				break;
			}
			case Token::TK_Condition:
			{
				compileCondition(T.getBB(), false);
				stream << ';' << NewLine;
				break;
			}
			case Token::TK_If:
			case Token::TK_IfNot:
			{
				bool IfNot = T.getKind() == Token::TK_IfNot;
				stream << "if(";
				compileCondition(T.getBB(), IfNot);
				stream << ")";
				if (!omitBraces(T, PA, registerize))
				{
					stream << '{' << NewLine;
				}
				else if (T.getNextNode() == T.getMatch())
				{
					// Empty if. Ideally it should have been removed by now...
					stream << ';' << NewLine;
				}
				blockDepth++;
				break;
			}
			case Token::TK_Else:
			{
				if (!omitBraces(*T.getMatch()->getMatch(), PA, registerize))
					stream << '}';
				stream << "else";
				if (!omitBraces(T, PA, registerize))
				{
					stream << '{' << NewLine;
				}
				else if (T.getNextNode() == T.getMatch())
				{
					// Empty else. Ideally it should have been removed by now...
					stream << ';' << NewLine;
				}
				else 
				{
					stream << ' ';
				}
				break;
			}
			case Token::TK_Branch:
			{
				if (T.getMatch()->getKind() == Token::TK_Loop)
					stream << "continue";
				else
					stream << "break";
				const Token* Scope = T.getMatch()->getKind() == Token::TK_Loop
					? T.getMatch()
					: T.getMatch()->getMatch();
				auto LabelIt = LabelGen.get(Scope);
				if (LabelIt != LabelGen.end())
				{
					stream << ' ' << *LabelIt;
				}
				stream << ';' << NewLine;
				break;
			}
			case Token::TK_End:
			{
				if (LabelGen.get(T.getMatch()) != LabelGen.end())
					LabelGen.deallocate();
				if (T.getMatch()->getKind() == Token::TK_Loop
					&& T.getPrevNode()->getKind() != Token::TK_Branch
					&& !(T.getPrevNode()->getKind() == Token::TK_BasicBlock
						&& isa<ReturnInst>(T.getPrevNode()->getBB()->getTerminator())))
				{
					stream << "break;" << NewLine;
				}
				if (T.getMatch()->getKind() & (Token::TK_If|Token::TK_IfNot))
				{
					const Token* Prev = T.getMatch();
					if (Prev->getMatch() != &T)
						Prev = Prev->getMatch();
					if (!omitBraces(*Prev, PA, registerize))
						stream << '}' << NewLine;
				}
				else
					stream << '}' << NewLine;
				blockDepth--;
				break;
			}
			case Token::TK_Prologue:
			{
				const BasicBlock* To = T.getBB()->getTerminator()->getSuccessor(T.getId());
				compilePHIOfBlockFromOtherBlock(To, T.getBB());
				break;
			}
			case Token::TK_Switch:
			{
				const SwitchInst* si = cast<SwitchInst>(T.getBB()->getTerminator());
				stream << "switch(";
				compileOperandForIntegerPredicate(si->getCondition(), CmpInst::ICMP_EQ, CheerpWriter::LOWEST);
				stream << "){" << NewLine;
				blockDepth++;
				break;
			}
			case Token::TK_Case:
			{
				const SwitchInst* si = cast<SwitchInst>(T.getBB()->getTerminator());
				int id = T.getId();
				if (id == 0)
					stream << "default";
				else
				{
					// The value to match for case `i` has index `2*i`
					auto cv = cast<ConstantInt>(si->getOperand(2*id));
					stream << "case ";
					compileOperandForIntegerPredicate(cv, CmpInst::ICMP_EQ, CheerpWriter::LOWEST);
				}
				stream << ':' << NewLine;
				break;
			}
			case Token::TK_BrIf:
			case Token::TK_BrIfNot:
			{
				report_fatal_error("Unexpected BR_IF token found");
			}
			case Token::TK_Invalid:
			{
				report_fatal_error("Invalid token found");
			}
		}
	}
}
void CheerpWriter::compileMethod(Function& F)
{
	bool asmjs = F.getSection() == StringRef("asmjs");
	if (sourceMapGenerator) {
#ifdef CHEERP_DEBUG_SOURCE_MAP
		llvm::errs() << "compileMethod: " << F.getName() << "\n";
#endif

		auto search = functionToDebugInfoMap.find(F.getName());
		if (search != functionToDebugInfoMap.end()) {
#ifdef CHEERP_DEBUG_SOURCE_MAP
			llvm::errs() << "Found on " << search->second.getFilename()
				<< ":"  << search->second.getLineNumber() << '\n';
#endif
			sourceMapGenerator->setFunctionName(search->second);
		}
	}
	currentFun = &F;
	stream << "function " << namegen.getName(&F) << '(';
	const Function::const_arg_iterator A=F.arg_begin();
	const Function::const_arg_iterator AE=F.arg_end();
	for(Function::const_arg_iterator curArg=A;curArg!=AE;++curArg)
	{
		if(curArg!=A)
			stream << ',';
		if(curArg->getType()->isPointerTy() && PA.getPointerKind(curArg) == SPLIT_REGULAR)
			stream << namegen.getName(curArg) << ',' << namegen.getSecondaryName(curArg);
		else
			stream << namegen.getName(curArg);
	}
	stream << "){" << NewLine;
	if (measureTimeToMain && F.getName() == "main")
	{
		stream << "__cheerp_main_time=__cheerp_now();" << NewLine;
	}
	if (asmjs)
	{
		compileParamTypeAnnotationsAsmJS(&F);
	}
	lastDepth0Block = nullptr;
	if(F.size()==1)
	{
		compileMethodLocals(F, false);
		lastDepth0Block = F.begin();
		compileBB(*F.begin());
	}
	else
	{
		if (useCfgLegacy)
		{
			Relooper* rl = runRelooperOnFunction(F, PA, registerize);
			CheerpRenderInterface ri(this, namegen.getBuiltinName(NameGenerator::Builtin::LABEL), NewLine, asmjs);
			compileMethodLocals(F, rl->needsLabel());
			rl->Render(&ri);
		}
		else
		{
			compileMethodLocals(F, false);
			CheerpRenderInterface ri(this, namegen.getBuiltinName(NameGenerator::Builtin::LABEL), NewLine, asmjs);

			DominatorTree &DT = pass.getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
			LoopInfo &LI = pass.getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
			CFGStackifier::Mode Mode = asmjs ? CFGStackifier::AsmJS : CFGStackifier::GenericJS;
			CFGStackifier CN(F, LI, DT, registerize, PA, Mode);
			compileTokens(CN.Tokens);
		}
	}
	assert(blockDepth == 0);
	if (asmjs && (!lastDepth0Block || !isa<ReturnInst>(lastDepth0Block->getTerminator())))
	{
		if(!F.getReturnType()->isVoidTy())
		{
			// asm.js needs a final return statement for not-void functions
			stream << "return";
			Registerize::REGISTER_KIND kind = registerize.getRegKindFromType(F.getReturnType(), true);
			switch(kind)
			{
				case Registerize::INTEGER:
					stream << " 0";
					break;
				case Registerize::FLOAT:
					stream << " " << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << "(0.)";
					break;
				case Registerize::DOUBLE:
					stream << " 0.";
					break;
				case Registerize::OBJECT:
					llvm::errs() << "OBJECT register kind should not appear in asm.js functions\n";
					llvm::report_fatal_error("please report a bug");
					break;
			}
			stream << ';' << NewLine;
		}
	}
	stream << '}' << NewLine;
	currentFun = NULL;
}

CheerpWriter::GlobalSubExprInfo CheerpWriter::compileGlobalSubExpr(const GlobalDepsAnalyzer::SubExprVec& subExpr)
{
	for ( auto it = std::next(subExpr.begin()); it != subExpr.end(); ++it )
	{
		const Use * u = *it;

		if ( isa<ConstantArray>( u->getUser() ) )
		{
			stream << '[' << u->getOperandNo() << ']';
			if (it == (subExpr.end()-1) && (*it)->get()->getType()->isPointerTy())
			{
				POINTER_KIND elementPointerKind = PA.getPointerKindForStoredType((*it)->get()->getType());
				return GlobalSubExprInfo(elementPointerKind, false);
			}
		}
		else if ( ConstantStruct* cs=dyn_cast<ConstantStruct>( u->getUser() ) )
		{
			stream << ".a" << u->getOperandNo();
			bool useWrapperArray = types.useWrapperArrayForMember(PA, cs->getType(), u->getOperandNo());
			if (useWrapperArray)
				stream << "[0]";
			if (it == (subExpr.end()-1) && (*it)->get()->getType()->isPointerTy())
			{
				// We don't expect anything which is not a pointer here, as we are fixing dependencies between globals
				assert(cs->getType()->getElementType(u->getOperandNo())->isPointerTy());
				TypeAndIndex b(cs->getType(), u->getOperandNo(), TypeAndIndex::STRUCT_MEMBER);
				POINTER_KIND elementPointerKind = PA.getPointerKindForMemberPointer(b);
				bool hasConstantOffset = PA.getConstantOffsetForMember(b) != NULL;
				return GlobalSubExprInfo(elementPointerKind, hasConstantOffset);
			}
		}
		else
			assert(false);
	}
	assert(false);
}

void CheerpWriter::compileGlobal(const GlobalVariable& G)
{
	assert(G.hasName());
	if(TypeSupport::isClientGlobal(&G) && !G.hasInitializer())
	{
		// Extern globals in the client namespace are only placeholders for JS globals
		return;
	}
	stream  << "var " << namegen.getName(&G);

	if(G.hasInitializer())
	{
		stream << '=';
		const Constant* C = G.getInitializer();
		POINTER_KIND k = PA.getPointerKind(&G);

		if(k == REGULAR)
		{
			stream << "{d:[";
			if(C->getType()->isPointerTy())
				compilePointerAs(C, PA.getPointerKindForStoredType(C->getType()));
			else
				compileOperand(C, LOWEST);
			stream << "],o:0}";
		}
		else if(k == BYTE_LAYOUT)
		{
			stream << "{d:";
			if(C->getType()->isPointerTy())
				compilePointerAs(C, PA.getPointerKindForStoredType(C->getType()));
			else
				compileOperand(C, LOWEST);
			stream << ",o:0}";
		}
		else if(k == SPLIT_REGULAR)
		{
			stream << '[';
			if(C->getType()->isPointerTy())
				compilePointerAs(C, PA.getPointerKindForStoredType(C->getType()));
			else
				compileOperand(C, LOWEST);
			stream << ']';
			stream << ';' << NewLine;
			stream << "var " << namegen.getSecondaryName(&G);
			stream << "=0";
		}
		else
		{
			if(C->getType()->isPointerTy())
			{
				POINTER_KIND storedKind = PA.getPointerKindForStoredType(C->getType());
				if(storedKind == REGULAR && PA.getConstantOffsetForPointer(&G))
					compilePointerBase(C);
				else
					compilePointerAs(C, storedKind);
			}
			else
				compileOperand(C);
		}
	}
	stream << ';' << NewLine;

	compiledGVars.insert(&G);
	if(G.hasInitializer())
	{
		if(StructType* st=dyn_cast<StructType>(G.getType()->getPointerElementType()))
		{
			//TODO: Verify that it makes sense to assume struct with no name has no bases
			if(st->hasName() && module.getNamedMetadata(Twine(st->getName(),"_bases")) &&
				globalDeps.classesWithBaseInfo().count(st))
			{
				stream << namegen.getClassName(st) << '(';
				compilePointerAs(&G, COMPLETE_OBJECT);
				stream << ");" << NewLine;
			}
		}
	}

	//Now we have defined a new global, check if there are fixups for previously defined globals
	auto fixup_range = globalDeps.fixupVars().equal_range(&G);
	
	for ( auto it = fixup_range.first; it != fixup_range.second; ++it )
	{
		const GlobalDepsAnalyzer::SubExprVec & subExpr = it->second;
		assert( !subExpr.empty() );
		assert( isa<GlobalVariable>( subExpr.front()->getUser() ) );
		const GlobalVariable* otherGV = cast<GlobalVariable>(subExpr.front()->getUser());
		if(!otherGV->hasInitializer())
		{
			llvm::errs() << "Expected initializer for ";
			otherGV->dump();
			llvm::errs() << "\n";
			llvm::report_fatal_error("Unsupported code found, please report a bug", false);
			continue;
		}

		compileCompleteObject(otherGV);

		Value* valOp = subExpr.back()->get();
		GlobalSubExprInfo subExprInfo = compileGlobalSubExpr(subExpr);

		stream << '=';
		if (valOp->getType()->isPointerTy())
		{
			assert(subExprInfo.kind != UNKNOWN);
			if((subExprInfo.kind == REGULAR || subExprInfo.kind == SPLIT_REGULAR) && subExprInfo.hasConstantOffset)
				compilePointerBase(valOp);
			else if(subExprInfo.kind == SPLIT_REGULAR)
			{
				compilePointerBase(valOp);
				stream << ";" << NewLine;
				compileCompleteObject(otherGV);
				compileGlobalSubExpr(subExpr);
				stream << 'o';
				stream << '=';
				compilePointerOffset(valOp, LOWEST);
			}
			else
				compilePointerAs(valOp, subExprInfo.kind);
		}
		else
			compileOperand(valOp, LOWEST);
		stream << ';' << NewLine;
	}
}

void CheerpWriter::compileGlobalAsmJS(const GlobalVariable& G)
{
	assert(G.hasName());
	if (TypeSupport::isClientGlobal(&G) && !G.hasInitializer())
	{
		// Extern globals in the client namespace are only placeholders for JS globals
		llvm::errs() << "client namespace functions not supported in asmjs mode yet:\n";
		G.dump();
		return;
	}
	if (symbolicGlobalsAsmJS)
	{
		stream << "var " << namegen.getName(&G) << '=';
		uint32_t globalAddr = linearHelper.getGlobalVariableAddress(&G);
		stream << globalAddr << ';' << NewLine;
	}
}

void CheerpWriter::compileGlobalsInitAsmJS()
{

	if (asmJSMem)
	{
		ostream_proxy os(*asmJSMem, nullptr, false);
		BinaryBytesWriter bytesWriter(os);
		uint32_t last_address = linearHelper.getStackStart();
		uint32_t last_size = 0;
		for ( const GlobalVariable* GV : linearHelper.globals() )
		{
			if (GV->hasInitializer())
			{
				const Constant* init = GV->getInitializer();
				Type* ty = init->getType();
				uint32_t cur_address = linearHelper.getGlobalVariableAddress(GV);
				uint32_t padding = cur_address - (last_address+last_size);
				for ( uint32_t i = 0; i < padding; i++ )
				{
					os << (char)0;
				}
				linearHelper.compileConstantAsBytes(init,/* asmjs */ true, &bytesWriter);
				last_size = targetData.getTypeAllocSize(ty);
				last_address = cur_address;
			}
			else
			{
				last_size = 0;
			}
		}
	}
	else
	{
		for ( const GlobalVariable* GV : linearHelper.globals() )
		{
			if (GV->hasInitializer())
			{
				const Constant* init = GV->getInitializer();

				// Skip global variables that are zero-initialised.
				if (linearHelper.isZeroInitializer(init))
					continue;

				stream  << heapNames[HEAP8] << ".set([";
				JSBytesWriter bytesWriter(stream);
				linearHelper.compileConstantAsBytes(init,/* asmjs */ true, &bytesWriter);
				stream << "]," << linearHelper.getGlobalVariableAddress(GV) << ");" << NewLine;
			}
		}
	}
}

void CheerpWriter::compileParamTypeAnnotationsAsmJS(const Function* F)
{
	const Function::const_arg_iterator A=F->arg_begin();
	const Function::const_arg_iterator AE=F->arg_end();
	for(Function::const_arg_iterator curArg=A;curArg!=AE;++curArg)
	{
		stream << namegen.getName(curArg) << '=';
		Registerize::REGISTER_KIND kind = registerize.getRegKindFromType(curArg->getType(), true);
		switch(kind)
		{
			case Registerize::INTEGER:
				stream << namegen.getName(curArg) << "|0";
				break;
			case Registerize::FLOAT:
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '(';
				stream << namegen.getName(curArg) << ')';
				break;
			case Registerize::DOUBLE:
				stream << '+' << namegen.getName(curArg);
				break;
			case Registerize::OBJECT:
				llvm::errs() << "OBJECT register kind should not appear in asm.js functions\n";
				llvm::report_fatal_error("please report a bug");
				break;
		}
		stream << ';' << NewLine;
	}
}

void CheerpWriter::compileNullPtrs()
{
	stream << "var oSlot=0;var nullArray=[null];var nullObj={d:nullArray,o:0};" << NewLine;
}

void CheerpWriter::compileCreateClosure()
{
	stream << "function " << namegen.getBuiltinName(NameGenerator::Builtin::CREATE_CLOSURE) << "(func, obj){return function(e){func(obj,e);};}" << NewLine;
	stream << "function " << namegen.getBuiltinName(NameGenerator::Builtin::CREATE_CLOSURE_SPLIT) << "(func, obj, objo){return function(e){func(obj,objo,e);};}" << NewLine;
}

void CheerpWriter::compileHandleVAArg()
{
	stream << "function " << namegen.getBuiltinName(NameGenerator::Builtin::HANDLE_VAARG) << "(ptr){var ret=ptr.d[ptr.o];ptr.o++;return ret;}" << NewLine;
}

void CheerpWriter::compileBuiltins(bool asmjs)
{
	StringRef math = asmjs?"stdlib.Math.":"Math.";
	if(useMathImul || asmjs)
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::IMUL) << '=' << math << "imul;" << NewLine;
	if(useMathFround)
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << '=' << math << "fround;" << NewLine;
}

void CheerpWriter::compileCheckBoundsHelper()
{
	stream << "function checkBounds(arr,offs){if(offs>=arr.length || offs<0) throw new Error('OutOfBounds');}" << NewLine;
}

void CheerpWriter::compileCheckBounds(const Value* p)
{
	stream<<"checkBounds(";
	compilePointerBase(p);
	stream<<",";
	compilePointerOffset(p,LOWEST);
	stream<<")";
}

void CheerpWriter::compileCheckDefinedHelper()
{
	stream << "function checkDefined(m){if(m===undefined) throw new Error('UndefinedMemberAccess');}" << NewLine;
}

void CheerpWriter::compileCheckDefined(const Value* p, bool needsOffset)
{
	// When compiling a SPIT_REGULAR, if there is an offset, we only check that.
	// If the offset exists the base is guaranteed to exists in the type.
	stream<<"checkDefined(";
	compileGEP(cast<User>(p),COMPLETE_OBJECT, HIGHEST);
	if(needsOffset)
		stream << "o";
	stream<<")";
}

void CheerpWriter::compileCheckBoundsAsmJSHelper()
{
	stream << "function checkBoundsAsmJS(addr,align,size){if((addr&align) || addr>=size || addr<0) throw new Error('OutOfBoundsAsmJS: '+addr);}" << NewLine;
}

void CheerpWriter::compileCheckBoundsAsmJS(const Value* p, int alignMask)
{
	stream<<"checkBoundsAsmJS(";
	compileOperand(p,LOWEST);
	stream<<','<<alignMask<<','<<heapSize*1024*1024<<"|0)|0";
}

void CheerpWriter::compileFunctionTablesAsmJS()
{
	for (const auto& table : linearHelper.getFunctionTables())
	{
		stream << "var " << table.second.name << "=[";
		bool first = true;
		uint32_t num = 0;
		for (const auto F : table.second.functions)
		{
			if (!first)
				stream << ',';
			first = false;
			stream << namegen.getName(F);
			num++;
		}
		uint32_t mask = linearHelper.getFunctionAddressMask(table.second.functions[0]->getFunctionType());
		for (; num <= mask; num++)
		{
			stream << ',' << namegen.getName(table.second.functions[0]);
		}
		stream << "];" << NewLine;
	}
}

void CheerpWriter::compileGrowMem()
{
	stream << "function " << namegen.getBuiltinName(NameGenerator::Builtin::GROW_MEM) << "(bytes){" << NewLine;
	stream << "var pages=(bytes+65535)>>16;" << NewLine;
	stream << "try{" << NewLine;
	stream << "__asm." << namegen.getBuiltinName(NameGenerator::MEMORY) << ".grow(pages);" << NewLine;
	for (int i = HEAP8; i<=HEAPF64; i++)
		stream << heapNames[i] << "=new " << typedArrayNames[i] << "(__asm." << namegen.getBuiltinName(NameGenerator::MEMORY) << ".buffer);" << NewLine;
	stream << "return pages<<16;" << NewLine;
	stream << "}catch(e){" << NewLine;
	stream << "return -1;" << NewLine;
	stream << '}' << NewLine;
	stream << "}" << NewLine;
}

void CheerpWriter::compileMathDeclAsmJS()
{
	stream << "var Infinity=stdlib.Infinity;" << NewLine;
	stream << "var NaN=stdlib.NaN;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::ABS_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::ABS) << "=stdlib.Math.abs;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::ACOS_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::ACOS) << "=stdlib.Math.acos;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::ASIN_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::ASIN) << "=stdlib.Math.asin;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::ATAN_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::ATAN) << "=stdlib.Math.atan;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::ATAN2_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::ATAN2) << "=stdlib.Math.atan2;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::CEIL_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::CEIL) << "=stdlib.Math.ceil;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::COS_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::COS) << "=stdlib.Math.cos;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::EXP_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::EXP) << "=stdlib.Math.exp;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::FLOOR_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::FLOOR) << "=stdlib.Math.floor;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::LOG_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::LOG) << "=stdlib.Math.log;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::POW_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::POW) << "=stdlib.Math.pow;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::SIN_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::SIN) << "=stdlib.Math.sin;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::SQRT_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::SQRT) << "=stdlib.Math.sqrt;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::TAN_F64))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::TAN) << "=stdlib.Math.tan;" << NewLine;
	if(globalDeps.needsBuiltin(GlobalDepsAnalyzer::CLZ32))
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::CLZ32) << "=stdlib.Math.clz32;" << NewLine;
}

void CheerpWriter::compileAsmJSImports()
{
	for (const Function* F: globalDeps.asmJSImports())
	{
		if(F->empty() || F->arg_size() == 0) continue;

		stream << "function _asm_" << namegen.getName(F) << '(';
		const Function::const_arg_iterator A=F->arg_begin();
		const Function::const_arg_iterator AE=F->arg_end();
		for(Function::const_arg_iterator curArg=A;curArg!=AE;++curArg)
		{
			if(curArg!=A)
			{
				stream << ',';
			}
			stream << namegen.getName(curArg);
		}
		stream << "){" << NewLine;
		if (!F->getReturnType()->isVoidTy())
			stream << "return ";
		stream << namegen.getName(F) << '(';
		for(Function::const_arg_iterator curArg=A;curArg!=AE;++curArg)
		{
			if(curArg!=A)
				stream << ',';
			int shift = 0;
			if(curArg->getType()->isPointerTy() && !TypeSupport::isAsmJSPointer(curArg->getType()))
			{
				shift = compileHeapForType(cast<PointerType>(curArg->getType())->getPointerElementType());
				stream << ',';
			}
			stream << namegen.getName(curArg);
			if (shift)
				stream << ">>" << shift;
		}
		stream << ");" << NewLine;
		stream << '}' << NewLine;
	}
}
void CheerpWriter::compileAsmJSExports()
{
	for (const Function* F: globalDeps.asmJSExports())
	{
		if(F->empty()) continue;
		Type* retTy = F->getReturnType();
		POINTER_KIND retKind = retTy->isPointerTy()? PA.getPointerKindForReturn(F): UNKNOWN; 
		assert(retKind == UNKNOWN || retKind == RAW || retKind == SPLIT_REGULAR);

		stream << "function " << namegen.getName(F) << '(';
		const Function::const_arg_iterator A=F->arg_begin();
		const Function::const_arg_iterator AE=F->arg_end();
		for(Function::const_arg_iterator curArg=A;curArg!=AE;++curArg)
		{
			if(curArg!=A)
			{
				stream << ',';
			}
			stream << namegen.getName(curArg);
		}
		stream << "){" << NewLine;
		if (retKind == SPLIT_REGULAR)
		{
			stream << "oSlot=";
		}
		else if (!F->getReturnType()->isVoidTy())
			stream << "return ";
		stream << "__asm." << namegen.getName(F) << '(';
		for(Function::const_arg_iterator curArg=A;curArg!=AE;++curArg)
		{
			if(curArg!=A)
				stream << ',';
			stream << namegen.getName(curArg);
		}
		stream << ')';
		if (retKind == SPLIT_REGULAR)
		{
			int shift =  getHeapShiftForType(cast<PointerType>(F->getReturnType())->getPointerElementType());
			if (shift != 0)
				stream << ">>" << shift;
			stream << ';' << NewLine;
			stream << "return ";
			compileHeapForType(cast<PointerType>(F->getReturnType())->getPointerElementType());
		}
		stream << ';' << NewLine;
		stream << '}' << NewLine;
	}
}

void CheerpWriter::compileFetchBuffer()
{
	stream << "function fetchBuffer(p) {" << NewLine;
	stream << "var bytes = null;" << NewLine;
	stream << "if (typeof window === 'undefined' && typeof self === 'undefined' && typeof require === 'undefined') {" << NewLine;
	stream << "bytes = new Promise( (resolve, reject) => {" << NewLine;
	stream << "resolve(read(p,'binary'));" << NewLine;
	stream << "});" << NewLine;
	stream << "} else if (typeof window === 'undefined' && typeof self === 'undefined') {" << NewLine;
	stream << "var fs = require('fs');" << NewLine;
	stream << "var path = require('path');" << NewLine;
	stream << "p = path.join(__dirname, p);" << NewLine;
	stream << "bytes = new Promise( (resolve, reject) => {" << NewLine;
	stream << "fs.readFile(p, function(error, data) {" << NewLine;
	stream << "if(error) reject(error);" << NewLine;
	stream << "else resolve(data);" << NewLine;
	stream << "});" << NewLine;
	stream << "});" << NewLine;
	stream << "} else {" << NewLine;
	stream << "bytes = fetch(p).then(response => response.arrayBuffer());" << NewLine;
	stream << "}" << NewLine;
	stream << "return bytes;" << NewLine;
	stream << "}" << NewLine;
}

void CheerpWriter::makeJS()
{
	if (sourceMapGenerator) {
		sourceMapGenerator->beginFile();

		NamedMDNode *cu = module.getNamedMetadata("llvm.dbg.cu");
		if (!cu || cu->getNumOperands() == 0) {
			llvm::errs() << "warning: no debug symbols found but source map is requested\n";
		}

		DebugInfoFinder finder;
		finder.processModule(module);

		for (const DISubprogram *method : finder.subprograms()) {
#ifdef CHEERP_DEBUG_SOURCE_MAP
			llvm::errs() << "Name: " << method.getName()
				<< " LinkageName: " << method.getLinkageName()
				<< " Line: " << method.getLineNumber()
				<< " ScopeLine: " << method.getScopeLineNumber()
				<< " Type: " << method.getType()
				<< " IsLocalToUnit: " << method.isLocalToUnit()
				<< " IsDefinition: " << method.isDefinition()
				<< "\n";
#endif

			StringRef linkName = method->getLinkageName();
			if (linkName.empty())
				linkName = method->getName();
			auto it = functionToDebugInfoMap.find(linkName);
			if(it == functionToDebugInfoMap.end())
				functionToDebugInfoMap.insert(std::make_pair(linkName, method));
			else if(method->isDefinition() && !it->second->isDefinition())
				it->second = method;
		}
	}

	if (makeModule==MODULE_TYPE::CLOSURE)
		stream << "(function(){" << NewLine;

	// Enable strict mode first
	stream << "\"use strict\";" << NewLine;

	if(addCredits)
		stream << "/*Compiled using Cheerp (R) by Leaning Technologies Ltd*/" << NewLine;

	if (measureTimeToMain)
	{
		stream << "var __cheerp_now = typeof dateNow!==\"undefined\"?dateNow:(typeof performance!==\"undefined\"?performance.now:function(){return new Date().getTime()});" << NewLine;
		stream << "var __cheerp_main_time = -0;" << NewLine;
		stream << "var __cheerp_start_time = __cheerp_now();" << NewLine;
	}

	//Compile the bound-checking function
	if ( checkBounds )
	{
		compileCheckBoundsHelper();
		compileCheckDefinedHelper();
	}

	compileBuiltins(false);

	std::vector<StringRef> exportedClassNames = compileClassesExportedToJs();
	compileNullPtrs();

	// Utility function for loading files
	if(!wasmFile.empty() || asmJSMem)
		compileFetchBuffer();

	if (globalDeps.needAsmJS() && checkBounds)
	{
		compileCheckBoundsAsmJSHelper();
	}

	if (globalDeps.needAsmJS() && wasmFile.empty())
	{
		// compile boilerplate
		stream << "function asmJS(stdlib, ffi, __heap){" << NewLine;
		stream << "\"use asm\";" << NewLine;
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::STACKPTR) << "=ffi.stackStart|0;" << NewLine;
		for (int i = HEAP8; i<=HEAPF64; i++)
		{
			stream << "var "<<heapNames[i]<<"=new stdlib."<<typedArrayNames[i]<<"(__heap);" << NewLine;
		}
		compileMathDeclAsmJS();
		compileBuiltins(true);
		stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY) << "=ffi." << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY) << ";" << NewLine;
		if (checkBounds)
		{
			stream << "var checkBoundsAsmJS=ffi.checkBoundsAsmJS;" << NewLine;
		}
		for (const Function* imported: globalDeps.asmJSImports())
		{
			stream << "var " << namegen.getName(imported) << "=ffi." << namegen.getName(imported) << ';' << NewLine;
		}
		if (globalDeps.needsBuiltin(GlobalDepsAnalyzer::GROW_MEM))
		{

			stream << "var " << namegen.getBuiltinName(NameGenerator::Builtin::GROW_MEM);
			stream << "=ffi.";
			stream << namegen.getBuiltinName(NameGenerator::Builtin::GROW_MEM);
			stream << ';' << NewLine;
		}

		// Declare globals
		for ( const GlobalVariable* GV : linearHelper.globals() )
			compileGlobalAsmJS(*GV);

		for ( Function & F : module.getFunctionList() )
		{
			if (!F.empty() && F.getSection() == StringRef("asmjs"))
			{
				compileMethod(F);
			}
		}

		compileFunctionTablesAsmJS();

		stream << "return {" << NewLine;
		// export constructors
		for (const Function * F : globalDeps.constructors() )
		{
			if (F->getSection() == StringRef("asmjs"))
				stream << namegen.getName(F) << ':' << namegen.getName(F) << ',' << NewLine;
		}
		// if entry point is in asm.js, explicitly export it
		if ( const Function * entryPoint = globalDeps.getEntryPoint())
		{
			if (entryPoint->getSection() == StringRef("asmjs"))
				stream << namegen.getName(entryPoint) << ':' << namegen.getName(entryPoint) << ',' << NewLine;
		}
		for (const Function* exported: globalDeps.asmJSExports())
		{
			StringRef name = namegen.getName(exported);
			stream << name << ':' << name << ',' << NewLine;
		}
		stream << "};" << NewLine;
		stream << "};" << NewLine;
		stream << "var __heap = new ArrayBuffer("<<heapSize*1024*1024<<");" << NewLine;
		for (int i = HEAP8; i<=HEAPF64; i++)
			stream << "var " << heapNames[i] << "= new " << typedArrayNames[i] << "(__heap);" << NewLine;
		compileAsmJSImports();
		compileAsmJSExports();
		stream << "function " << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY) << "(){throw new Error('this should be unreachable');};" << NewLine;
		stream << "var ffi = {" << NewLine;
		stream << "heapSize:__heap.byteLength," << NewLine;
		stream << "stackStart:" << linearHelper.getStackStart() << ',' << NewLine;
		stream << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY) << ":" << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY) << "," << NewLine;
		if (checkBounds)
		{
			stream << "checkBoundsAsmJS:checkBoundsAsmJS," << NewLine;
		}
		for (const Function* imported: globalDeps.asmJSImports())
		{
			std::string name;
			if (imported->empty() && TypeSupport::isClientFunc(imported))
			{
				assert(imported->hasFnAttribute(Attribute::Static) && "Only static client functions can be imported");
				StringRef className, funcName;
				std::tie(className, funcName) = getBuiltinClassAndFunc(imported->getName().data()+10);
				name = (className + "." + funcName).str();
			}
			else if (imported->empty() && !TypeSupport::isClientFunc(imported))
				name = namegen.getBuiltinName(NameGenerator::Builtin::DUMMY);
			else if (imported->arg_size() == 0)
				name = namegen.getName(imported);
			else
				name = ("_asm_"+namegen.getName(imported)).str();
			stream << namegen.getName(imported) << ':' << name  << ',' << NewLine;
		}
		if (globalDeps.needsBuiltin(GlobalDepsAnalyzer::GROW_MEM))
		{

			stream << namegen.getBuiltinName(NameGenerator::Builtin::GROW_MEM);
			stream << ':';
			stream << namegen.getBuiltinName(NameGenerator::Builtin::GROW_MEM);
			stream << ',' << NewLine;
		}
		stream << "};" << NewLine;
		stream << "var stdlib = {"<<NewLine;
		stream << "Math:Math,"<<NewLine;
		stream << "Infinity:Infinity,"<<NewLine;
		stream << "NaN:NaN,"<<NewLine;
		for (int i = HEAP8; i<=HEAPF64; i++)
		{
			stream << typedArrayNames[i] << ':' << typedArrayNames[i] << ',' << NewLine;
		}
		stream << "};" << NewLine;
		compileGlobalsInitAsmJS();
	}

	for ( Function & F : module.getFunctionList() )
		if (!F.empty() && F.getSection() != StringRef("asmjs"))
		{
#ifdef CHEERP_DEBUG_POINTERS
			dumpAllPointers(F, PA);
#endif //CHEERP_DEBUG_POINTERS
			compileMethod(F);
		}
	for ( const GlobalVariable & GV : module.getGlobalList() )
	{
		// Skip global ctors array
		if (GV.getName() == "llvm.global_ctors")
			continue;
		if (GV.getSection() != StringRef("asmjs"))
			compileGlobal(GV);
	}

	for ( StructType * st : globalDeps.classesUsed() )
	{
		if ( st->getNumElements() > V8MaxLiteralProperties )
			compileClassConstructor(st);
	}

	for ( StructType * st : globalDeps.classesWithBaseInfo() )
		compileClassType(st);

	for ( Type * st : globalDeps.dynAllocArrays() )
		compileArrayClassType(st);

	if ( globalDeps.needCreatePointerArray() )
		compileArrayPointerType();
	
	//Compile the closure creation helper
	if ( globalDeps.needCreateClosure() )
		compileCreateClosure();
	
	//Compile handleVAArg if needed
	if( globalDeps.needHandleVAArg() )
		compileHandleVAArg();

	//Compile growLinearMemory if needed
	if (globalDeps.needsBuiltin(GlobalDepsAnalyzer::GROW_MEM))
		compileGrowMem();
	
	//Load Wast module
	if (!wasmFile.empty())
	{
		for (int i = HEAP8; i<=HEAPF64; i++)
			stream << "var " << heapNames[i] << "=null;" << NewLine;
		stream << "var __asm=null;" << NewLine;
		stream << "var __heap=null;" << NewLine;
		compileAsmJSImports();
		compileAsmJSExports();
		stream << "function " << namegen.getBuiltinName(NameGenerator::Builtin::DUMMY) << "(){throw new Error('this should be unreachable');};" << NewLine;
		if (makeModule == MODULE_TYPE::COMMONJS)
		{
			stream << "module.exports=";
		}
		else
		{
			for (StringRef &className : exportedClassNames)
				stream << className << ".promise=" << NewLine;
		}
		stream << "fetchBuffer('" << wasmFile << "').then(r=>" << NewLine;
		stream << "WebAssembly.instantiate(r," << NewLine;
		stream << "{i:{" << NewLine;
		for (const Function* imported: globalDeps.asmJSImports())
		{
			std::string name;
			if (imported->empty() && TypeSupport::isClientFunc(imported))
			{
				assert(imported->hasFnAttribute(Attribute::Static) && "Only static client functions can be imported");
				StringRef className, funcName;
				std::tie(className, funcName) = getBuiltinClassAndFunc(imported->getName().data()+10);
				name = (className + "." + funcName).str();
			}
			else if (imported->empty() && !TypeSupport::isClientFunc(imported))
				name = namegen.getBuiltinName(NameGenerator::Builtin::DUMMY);
			else if (imported->arg_size() == 0)
				name = namegen.getName(imported);
			else
				name = ("_asm_"+namegen.getName(imported)).str();
			stream << namegen.getName(imported) << ':' << name  << ',' << NewLine;
		}
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::ACOS_F64))
			stream << namegen.getBuiltinName(NameGenerator::ACOS) << ":Math.acos," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::ASIN_F64))
			stream << namegen.getBuiltinName(NameGenerator::ASIN) << ":Math.asin," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::ATAN_F64))
			stream << namegen.getBuiltinName(NameGenerator::ATAN) << ":Math.atan," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::ATAN2_F64))
			stream << namegen.getBuiltinName(NameGenerator::ATAN2) << ":Math.atan2," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::COS_F64))
			stream << namegen.getBuiltinName(NameGenerator::COS) << ":Math.cos," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::EXP_F64))
			stream << namegen.getBuiltinName(NameGenerator::EXP) << ":Math.exp," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::LOG_F64))
			stream << namegen.getBuiltinName(NameGenerator::LOG) << ":Math.log," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::POW_F64))
			stream << namegen.getBuiltinName(NameGenerator::POW) << ":Math.pow," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::SIN_F64))
			stream << namegen.getBuiltinName(NameGenerator::SIN) << ":Math.sin," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::TAN_F64))
			stream << namegen.getBuiltinName(NameGenerator::TAN) << ":Math.tan," << NewLine;
		if(linearHelper.getBuiltinId(GlobalDepsAnalyzer::GROW_MEM))
		{
			stream << namegen.getBuiltinName(NameGenerator::Builtin::GROW_MEM);
			stream << ':';
			stream << namegen.getBuiltinName(NameGenerator::Builtin::GROW_MEM);
			stream << ',' << NewLine;
		}
		stream << "}})" << NewLine;
		stream << ",console.log).then(r=>{" << NewLine;
		stream << "var i=r.instance;" << NewLine;
		for (int i = HEAP8; i<=HEAPF64; i++)
			stream << heapNames[i] << "=new " << typedArrayNames[i] << "(i.exports." << namegen.getBuiltinName(NameGenerator::MEMORY) << ".buffer);" << NewLine;
		stream << "__asm=i.exports;" << NewLine;
		stream << "__heap=i.exports." << namegen.getBuiltinName(NameGenerator::MEMORY) << ".buffer;" << NewLine;
	}
	//Load asm.js module
	else if (globalDeps.needAsmJS() && asmJSMem)
	{
		stream << "var __asm=null;" << NewLine;
		if (makeModule == MODULE_TYPE::COMMONJS)
		{
			stream << "module.exports=";
		}
		stream << "fetchBuffer('" << sys::path::filename(asmJSMemFile) << "').then(r=>{" << NewLine;
		stream << heapNames[HEAP8] << ".set(new Uint8Array(r),";
		stream << linearHelper.getStackStart() << ");" << NewLine;
		stream << "__asm=asmJS(stdlib, ffi, __heap);" << NewLine;
	}
	else
	{
		if (globalDeps.needAsmJS())
			stream << "var __asm=asmJS(stdlib, ffi, __heap);" << NewLine;

		if (makeModule == MODULE_TYPE::COMMONJS)
			stream << "module.exports=Promise.resolve().then(_=>{" << NewLine;
	}

	//Call constructors
	if (wasmFile.empty()) {
		for (const Function * F : globalDeps.constructors() )
		{
			if (F->getSection() == StringRef("asmjs"))
				stream << "__asm.";
			stream << namegen.getName(F) << "();" << NewLine;
		}
	} else {
		llvm::Function* entry = module.getFunction("_start");
		if(entry)
			stream << "__asm." << namegen.getName(entry) << "();" << NewLine;
	}

	//Invoke the entry point
	if ( const Function * entryPoint = globalDeps.getEntryPoint() )
	{
		if (!wasmFile.empty() && entryPoint->getSection() == StringRef("asmjs"))
			stream << "i.exports.";
		else if (wasmFile.empty() && entryPoint->getSection() == StringRef("asmjs"))
			stream << "__asm.";
		stream << namegen.getName(entryPoint) << "();" << NewLine;
	}
	if (makeModule == MODULE_TYPE::COMMONJS)
	{
		stream << "return{" << NewLine;
		for (StringRef &className : exportedClassNames)
			stream << className << ":" << className << ',' << NewLine;
		stream << "};" << NewLine;
	}
	if (!wasmFile.empty() || (globalDeps.needAsmJS() && asmJSMem))
	{
		stream << "},console.log,console.log);" << NewLine;
	}
	else if (makeModule == MODULE_TYPE::COMMONJS)
	{
		stream << "});" << NewLine;
	}

	if (makeModule==MODULE_TYPE::CLOSURE) {
		if (!exportedClassNames.empty()) {
			// The following JavaScript code originates from:
			// https://github.com/jashkenas/underscore/blob/master/underscore.js
			// Establish the root object, `window` (`self`) in the browser, `global`
			// on the server, or `this` in some virtual machines. We use `self`
			// instead of `window` for `WebWorker` support.
			stream << "var __root =" << NewLine;
			stream << "\ttypeof self === 'object' && self.self === self && self ||" << NewLine;
			stream << "\ttypeof global === 'object' && global.global === global && global ||" << NewLine;
			stream << "\tthis;" << NewLine;
		}

		for (StringRef &className : exportedClassNames)
		{
			// Genericjs and asmjs should export a promise property as well.
			// It will resolve immediately since there is no asynchronous
			// module compilation required.
			if (wasmFile.empty())
				stream << className << ".promise=Promise.resolve();";
			stream << "__root." << className << " = " << className << ";" << NewLine;
		}

		stream << "})();" << NewLine;
	}

	if (measureTimeToMain)
	{
		stream << "console.log(\"main() called after\", __cheerp_main_time-__cheerp_start_time, \"ms\");" << NewLine;
	}


	// Link the source map if necessary
	if(sourceMapGenerator)
	{
		sourceMapGenerator->endFile();
		stream << "//# sourceMappingURL=" << sourceMapGenerator->getSourceMapName();
	}
}

Relooper* CheerpWriter::runRelooperOnFunction(const llvm::Function& F, const PointerAnalyzer& PA,
                                              const Registerize& registerize)
{
	//TODO: Support exceptions
	Function::const_iterator B=F.begin();
	Function::const_iterator BE=F.end();
	//First run, create the corresponding relooper blocks
	std::map<const BasicBlock*, /*relooper::*/Block*> relooperMap;
	int BlockId = 1;
	for(;B!=BE;++B)
	{
		if(B->isLandingPad())
			continue;
		//Decide if this block should be duplicated instead
		//of actually directing the control flow to reach it
		//Currently we just check if the block ends with a return
		//and its small enough. This should simplify some control flows.
		bool isSplittable = B->size()<3 && isa<ReturnInst>(B->getTerminator());
		//Decide if we can use a switch instead of an if/else chain for 
		//the control flow
		const TerminatorInst* term = B->getTerminator();
		// If this is not null, we can use a switch
		const SwitchInst* switchInst = useSwitch(term) ? cast<SwitchInst>(term) : nullptr;
		Block* rlBlock = new Block(&(*B), isSplittable, BlockId++, switchInst);
		relooperMap.insert(make_pair(&(*B),rlBlock));
	}

	B=F.begin();
	BE=F.end();
	//Second run, add the branches
	for(;B!=BE;++B)
	{
		if(B->isLandingPad())
			continue;
		const TerminatorInst* term=B->getTerminator();
		uint32_t defaultBranchId=-1;
		//Find out which branch id is the default
		if(isa<BranchInst>(term))
		{
			const BranchInst* bi=cast<BranchInst>(term);
			if(bi->isUnconditional())
				defaultBranchId = 0;
			else
				defaultBranchId = 1;
		}
		else if(isa<SwitchInst>(term))
		{
#ifndef NDEBUG
			const SwitchInst* si=cast<SwitchInst>(term);
#endif
			assert(si->getDefaultDest()==si->getSuccessor(0));
			defaultBranchId = 0;
		}
		else if(isa<InvokeInst>(term))
		{
#ifndef NDEBUG
			const InvokeInst* ii=cast<InvokeInst>(term);
#endif
			assert(ii->getNormalDest()==ii->getSuccessor(0));
			defaultBranchId = 0;
		}
		else if(term->getNumSuccessors())
		{
			//Only a problem if there are successors
			term->dump();
			llvm::report_fatal_error("Unsupported code found, please report a bug", false);
		}

		for(uint32_t i=0;i<term->getNumSuccessors();i++)
		{
			if(term->getSuccessor(i)->isLandingPad())
				continue;
			Block* target=relooperMap[term->getSuccessor(i)];
			const BasicBlock* bbTo = target->llvmBlock;
			bool hasPrologue = bbTo->getFirstNonPHI()!=&bbTo->front();
			if (hasPrologue)
			{
				// We can avoid assignment from the same register if no pointer kind
				// conversion is required
				hasPrologue = needsPointerKindConversionForBlocks(bbTo, &(*B), PA, registerize);
			}
			//Use -1 for the default target
			bool ret=relooperMap[&(*B)]->AddBranchTo(target, (i==defaultBranchId)?-1:i, hasPrologue);

			if(ret==false) //More than a path for a single block can only happen for switch
			{
				assert(isa<SwitchInst>(term));
			}
		}
	}

	B=F.begin();
	BE=F.end();
	//Third run, add the block to the relooper and run it
	Relooper* rl=new Relooper(BlockId);
	for(;B!=BE;++B)
	{
		if(B->isLandingPad())
			continue;
		rl->AddBlock(relooperMap[&(*B)]);
	}
	rl->Calculate(relooperMap[&F.getEntryBlock()]);
	return rl;
}
bool CheerpWriter::useSwitch(const TerminatorInst* term)
{
	// Consider only switch instructions
	if (!isa<SwitchInst>(term))
		return false;
	const SwitchInst* si = cast<SwitchInst>(term);
	// At least 3 successors
	if (si->getNumSuccessors() < 3)
		return false;
	//In asm.js cases values must be in the range [-2^31,2^31),
	//and the difference between the biggest and the smaller must be < 2^31
	int64_t max = std::numeric_limits<int64_t>::min();
	int64_t min = std::numeric_limits<int64_t>::max();
	for (auto& c: si->cases())
	{
		int64_t curr = c.getCaseValue()->getSExtValue();
		max = std::max(max,curr);
		min = std::min(min,curr);
	}
	if (min >= std::numeric_limits<int32_t>::min() &&
		max <= std::numeric_limits<int32_t>::max() && 
		//NOTE: this number is the maximum allowed by V8 for wasm's br_table,
		// it is not defined in the spec
		max-min <= 32 * 1024 &&
		// Avoid extremely big and extremely sparse tables, require at least 3% fill rate
		(max-min <= 100 || si->getNumCases() * 100 >= 3 * (max-min)))
	{
		return true;
	}
	return false;
}

void CheerpWriter::JSBytesWriter::addByte(uint8_t byte)
{
	if(!first)
		stream << ',';
	stream << (int)byte;
	first = false;
}

void CheerpWriter::AsmJSGepWriter::addValue(const llvm::Value* v, uint32_t size)
{
	offset = true;
	if (size == 1)
	{
		writer.compileOperand(v ,ADD_SUB);
		writer.stream << '+';
	}
	else if (isPowerOf2_32(size))
	{
		writer.stream << '(';
		writer.compileOperand(v, SHIFT);
		writer.stream << "<<";
		writer.stream << Log2_32(size);
		writer.stream << ")+";
	}
	else if (use_imul)
	{
		// NOTE: V8 requires imul to be coerced to int like normal functions
		writer.stream << '(' << writer.namegen.getBuiltinName(NameGenerator::Builtin::IMUL) << '(';
		writer.compileOperand(v ,LOWEST);
		writer.stream << ',' << size << ')';
		writer.stream << "|0)+";
	}
	else
	{
		writer.stream << '(';
		writer.compileOperand(v, MUL_DIV);
		writer.stream << '*';
		writer.stream << size;
		writer.stream << "|0)+";
	}
}

void CheerpWriter::AsmJSGepWriter::addConst(int64_t v)
{
	assert(v);
	// Just make sure that the constant part of the offset is not too big
	assert(v>=std::numeric_limits<int32_t>::min());
	assert(v<=std::numeric_limits<int32_t>::max());

	offset = true;
	writer.stream << v << '+';
}

bool CheerpWriter::AsmJSGepWriter::isInlineable(const llvm::Value* p)
{
	if (const auto I = dyn_cast<BitCastInst>(p))
		return ::isInlineable(*I, writer.PA);

	if (const auto I = dyn_cast<GetElementPtrInst>(p))
		return ::isInlineable(*I, writer.PA);

	return true;
}
