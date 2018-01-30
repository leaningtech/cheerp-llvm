//===-- Types.cpp - The Cheerp JavaScript generator -----------------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2011-2015 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#include "llvm/Cheerp/Writer.h"
#include "llvm/Cheerp/Utility.h"
#include <stdio.h>

using namespace cheerp;
using namespace llvm;

void CheerpWriter::compileTypedArrayType(Type* t)
{
	if(t->isIntegerTy(8))
		stream << "Uint8Array";
	else if(t->isIntegerTy(16))
		stream << "Uint16Array";
	else if(t->isIntegerTy(32))
		stream << "Int32Array";
	else if(t->isFloatTy())
		stream << "Float32Array";
	else if(t->isDoubleTy())
		stream << "Float64Array";
	else
	{
		llvm::errs() << "Typed array requested for type " << *t << "\n";
		llvm::report_fatal_error("Unsupported code found, please report a bug", false);
	}
}

void CheerpWriter::compileSimpleType(Type* t)
{
	assert(TypeSupport::isSimpleType(t, forceTypedArrays));
	switch(t->getTypeID())
	{
		case Type::IntegerTyID:
		{
			//We only really have 32bit integers.
			//We will allow anything shorter.
			//Print out a '0' to let the engine know this is an integer.
			stream << '0';
			break;
		}
		case Type::FloatTyID:
		{
			if(useMathFround)
			{
				stream << namegen.getBuiltinName(NameGenerator::Builtin::FROUND) << "(0.)";
				break;
			}
		}
		case Type::DoubleTyID:
		{
			// NOTE: V8 requires the `.` to identify it as a double in asm.js
			stream << "0.";
			break;
		}
		case Type::PointerTyID:
		{
			if(PA.getPointerKindForStoredType(t)==COMPLETE_OBJECT)
				stream << "null";
			else
				stream << "nullObj";
			break;
		}
		case Type::StructTyID:
		{
			assert(TypeSupport::hasByteLayout(t));
			uint32_t typeSize = targetData.getTypeAllocSize(t);
			stream << "new Uint8Array(";
			// Round up the size to make sure that any typed array can be initialized from the buffer
			stream << ((typeSize + 7) & (~7));
			stream << ")";
			break;
		}
		case Type::ArrayTyID:
		{
			if(TypeSupport::hasByteLayout(t))
			{
				uint32_t typeSize = targetData.getTypeAllocSize(t);
				stream << "new Uint8Array(";
				// Round up the size to make sure that any typed array can be initialized from the buffer
				stream << ((typeSize + 7) & (~7));
				stream << ")";
			}
			else
			{
				ArrayType* at=cast<ArrayType>(t);
				Type* et=at->getElementType();
				assert(types.isTypedArrayType(et, forceTypedArrays) && at->getNumElements()>1);
				stream << "new ";
				compileTypedArrayType(et);
				stream << '(' << at->getNumElements() << ')';
			}
			break;
		}
		default:
			assert(false);
	}
}

uint32_t CheerpWriter::compileComplexType(Type* t, COMPILE_TYPE_STYLE style, StringRef varName, uint32_t maxDepth, uint32_t totalLiteralProperties)
{
	assert(!TypeSupport::isSimpleType(t, forceTypedArrays));
	// Handle complex arrays and objects, they are all literals in JS
	assert(t->getTypeID() == Type::StructTyID || t->getTypeID() == Type::ArrayTyID);

	bool useVarName = !varName.empty() && style == LITERAL_OBJ;

	// We only need to split large objects with the LITERAL_OBJ style
	uint32_t numElements = 0;
	if(StructType* ST = dyn_cast<StructType>(t))
	{
		numElements = ST->getNumElements();
		if(numElements > V8MaxLiteralProperties && style!=THIS_OBJ)
		{
			assert(globalDeps.classesUsed().count(cast<StructType>(t)));
			// This is a big object, call the constructor and be done with it
			stream << "new ";
			stream << namegen.getConstructorName(t) << "()";
			return 0;
		}
	}
	else if(ArrayType* AT = dyn_cast<ArrayType>(t))
	{
		// Basic elements, such as numbers and pointers (including nullObj) do not count. Structs and array do.
		if(AT->getElementType()->isStructTy() || AT->getElementType()->isArrayTy())
			numElements = AT->getNumElements();
	}
	bool shouldReturnElementsCount = true;

	if(useVarName && (maxDepth == 0 || ((totalLiteralProperties + numElements) > V8MaxLiteralProperties)))
	{
		// If this struct have more than V8MaxLiteralProperties there is no point in splitting it anyway
		if(numElements <= V8MaxLiteralProperties)
			stream << varName << '=';
		maxDepth = V8MaxLiteralDepth;
		shouldReturnElementsCount = false;
		totalLiteralProperties = 0;
	}

	uint32_t nextMaxDepth = useVarName ? maxDepth - 1 : maxDepth;
	if (StructType* st = dyn_cast<StructType>(t))
	{
		assert(!TypeSupport::hasByteLayout(st));
		StructType* downcastArrayBase = globalDeps.needsDowncastArray(st);
		bool addDowncastArray = downcastArrayBase != NULL;
		if(style == LITERAL_OBJ)
		{
			if(addDowncastArray)
			{
				stream << namegen.getClassName(downcastArrayBase) << '(';
			}
			stream << '{';
		}
		for(uint32_t i=0;i<st->getNumElements();i++)
		{
			Type* element = st->getElementType(i);
			if(i!=0)
			{
				if(style==THIS_OBJ)
					stream << ';' << NewLine;
				else
					stream << ',';
			}
			if(style==THIS_OBJ)
				stream << "this.";
			stream << types.getPrefixCharForMember(PA, st, i) << i;
			if(style==THIS_OBJ)
				stream << '=';
			else
				stream << ':';
			// Create a wrapper array for all members which require REGULAR pointers, if they are not already covered by the downcast array
			TypeAndIndex baseAndIndex(st, i, TypeAndIndex::STRUCT_MEMBER);
			bool restoreMaxDepth = false;
			bool useWrapperArray = types.useWrapperArrayForMember(PA, st, i);
			if (useWrapperArray)
			{
				// We need to do an extra check to break deep literals here
				if(useVarName)
				{
					if(nextMaxDepth == 0)
					{
						stream << varName << '=';
						nextMaxDepth = V8MaxLiteralDepth;
					}
					else
					{
						nextMaxDepth--;
						restoreMaxDepth=true;
						if(element->isStructTy())
							numElements++;
					}
				}
				stream << '[';
			}
			if (element->isPointerTy())
			{
				POINTER_KIND memberPointerKind = PA.getPointerKindForMemberPointer(baseAndIndex);
				bool hasConstantOffset = PA.getConstantOffsetForMember(baseAndIndex);
				if((memberPointerKind == REGULAR || memberPointerKind == SPLIT_REGULAR || memberPointerKind == SPLIT_BYTE_LAYOUT) && hasConstantOffset)
					stream << "nullArray";
				else if (memberPointerKind == SPLIT_REGULAR || memberPointerKind == SPLIT_BYTE_LAYOUT)
				{
					stream << "nullArray";
					if(style==THIS_OBJ)
						stream << ';' << NewLine << "this.";
					else
						stream << ',';
					stream << types.getPrefixCharForMember(PA, st, i) << i << 'o';
					if(style==THIS_OBJ)
						stream << '=';
					else
						stream << ':';
					stream << '0';
					// FIXME: The offset member is not taken into account when deciding if the new-based constructor is required
					// so in rare cases (when the added element makes the struct larger than 8 elements) the slow literal runtime
					// call will be used on V8.
					numElements++;
				}
				else if (memberPointerKind == COMPLETE_OBJECT_AND_PO)
				{
					stream << "null";
					if(!hasConstantOffset)
					{
						if(style==THIS_OBJ)
							stream << ';' << NewLine << "this.";
						else
							stream << ',';
						stream << types.getPrefixCharForMember(PA, st, i) << i << 'b';
						if(style==THIS_OBJ)
							stream << '=';
						else
							stream << ':';
						stream << "null";
						// FIXME: The offset member is not taken into account when deciding if the new-based constructor is required
						// so in rare cases (when the added element makes the struct larger than 8 elements) the slow literal runtime
						// call will be used on V8.
						numElements++;
					}
				}
				else if (memberPointerKind == COMPLETE_OBJECT)
					stream << "null";
				else
					stream << "nullObj";
			}
			else if(TypeSupport::isSimpleType(element, forceTypedArrays))
				compileSimpleType(element);
			else if(style == THIS_OBJ)
				compileComplexType(element, LITERAL_OBJ, varName, nextMaxDepth, 0);
			else
				numElements += compileComplexType(element, LITERAL_OBJ, varName, nextMaxDepth, totalLiteralProperties + numElements);
			if(useWrapperArray)
			{
				if(restoreMaxDepth)
					nextMaxDepth++;
				stream << ']';
			}
		}
		if(style == LITERAL_OBJ)
		{
			stream << '}';
			if(addDowncastArray)
				stream << ')';
		}
		else if(style == THIS_OBJ)
		{
			stream << ';' << NewLine;
			if(addDowncastArray)
			{
				stream << namegen.getClassName(downcastArrayBase) << "(this)";
			}
		}
	}
	else
	{
		assert(style == LITERAL_OBJ);
		ArrayType* at=cast<ArrayType>(t);
		Type* element = at->getElementType();
		assert(!(types.isTypedArrayType(element, forceTypedArrays) && at->getNumElements()>1));
		// Work around V8 limits on literal array larger than 8 elements
		if(at->getNumElements() > 8)
		{
			if(element->isPointerTy())
			{
				assert( globalDeps.needCreatePointerArray() );
				stream << "createPointerArray([],0," << at->getNumElements();
				stream << ',';
				if(PA.getPointerKindForStoredType(element)==COMPLETE_OBJECT)
					stream << "null";
				else
					stream << "nullObj";
				stream << ')';
			}
			else
			{
				assert( globalDeps.dynAllocArrays().count(element) );
				stream <<  namegen.getArrayName(element) << "([],0," << at->getNumElements() << ')';
			}
		}
		else
		{
			stream << '[';
			for(uint64_t i=0;i<at->getNumElements();i++)
			{
				if(i!=0)
					stream << ',';
				if(TypeSupport::isSimpleType(element, forceTypedArrays))
					compileSimpleType(element);
				else
					numElements += compileComplexType(element, LITERAL_OBJ, varName, nextMaxDepth, totalLiteralProperties + numElements);
			}
			stream << ']';
		}
	}
	return shouldReturnElementsCount ? numElements : 0;
}

void CheerpWriter::compileType(Type* t, COMPILE_TYPE_STYLE style, StringRef varName)
{
	if(TypeSupport::isSimpleType(t, forceTypedArrays))
		compileSimpleType(t);
	else
		compileComplexType(t, style, varName, V8MaxLiteralDepth, 0);
}

uint32_t CheerpWriter::compileClassTypeRecursive(const std::string& baseName, StructType* currentType, uint32_t baseCount)
{
	if(currentType->getDirectBase())
	{
		baseCount=compileClassTypeRecursive(baseName,currentType->getDirectBase(),baseCount);
		if(!TypeSupport::hasBasesInfoMetadata(currentType, module))
			return baseCount;
	}
	else
	{
		stream << "a[" << baseCount << "]=" << baseName << ';' << NewLine;
		stream << baseName << ".o=" << baseCount << ';' << NewLine;
		stream << baseName << ".a=a;" << NewLine;
		baseCount++;
	}

	uint32_t firstBase, localBaseCount;
	if(!types.getBasesInfo(currentType, firstBase, localBaseCount))
		return baseCount;
	//baseCount has been already incremented above

	for(uint32_t i=firstBase;i<(firstBase+localBaseCount);i++)
	{
		if(!currentType->getElementType(i)->isStructTy())
			continue;
		SmallString<16> buf;
		llvm::raw_svector_ostream bufStream(buf);
		bufStream << ".a" << i;
		bufStream.flush();
		baseCount=compileClassTypeRecursive(baseName+buf.c_str(), cast<StructType>(currentType->getElementType(i)), baseCount);
	}
	return baseCount;
}

void CheerpWriter::compileClassConstructor(StructType* T)
{
T->dump();
	assert(T->getNumElements() > V8MaxLiteralProperties);
	stream << "function ";
	stream << namegen.getConstructorName(T) << "(){" << NewLine;
	compileComplexType(T, THIS_OBJ, "aSlot", V8MaxLiteralDepth, 0);
	stream << '}' << NewLine;
}

void CheerpWriter::compileClassType(StructType* T)
{
	if(!T->hasName())
	{
		llvm::errs() << "Expected name for struct " << *T << "\n";
		llvm::report_fatal_error("Unsupported code found, please report a bug", false);
		return;
	}
	stream << "function " << namegen.getClassName(T) << "(obj){" << NewLine;

	stream << "var a=[];" << NewLine;
	compileClassTypeRecursive("obj", T, 0);
	stream << "return obj;}" << NewLine;
}

void CheerpWriter::compileArrayClassType(Type* T)
{
	stream << "function ";
	stream << namegen.getArrayName(T);
	stream << "(ret,start,end){" << NewLine;
	stream << "for(var __i__=start;__i__<end;__i__++)" << NewLine;
	stream << "ret[__i__]=";
	compileType(T, LITERAL_OBJ, "ret[__i__]");
	stream << ';' << NewLine << "ret[end]=" << targetData.getTypeAllocSize(T) << ';' << NewLine << "return ret;" << NewLine << '}' << NewLine;
}

void CheerpWriter::compileArrayPointerType()
{
	stream << "function createPointerArray(ret,start,end,elem){for(var __i__=start;__i__<end;__i__++)ret[__i__]=elem;ret[end]=4;return ret;}"
		<< NewLine;
}

