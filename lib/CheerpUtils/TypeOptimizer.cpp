//===-- TypeOptimizer.cpp - Cheerp helper -------------------------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2015 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#include "llvm/Cheerp/Utility.h"
#include "llvm/Cheerp/TypeOptimizer.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/raw_ostream.h"
#include <set>

using namespace llvm;

namespace cheerp
{

const char *TypeOptimizer::getPassName() const {
	return "TypeOptimizer";
}

void TypeOptimizer::addAllBaseTypesForByteLayout(StructType* st, Type* baseType)
{
	if(ArrayType* AT=dyn_cast<ArrayType>(baseType))
		addAllBaseTypesForByteLayout(st, AT->getElementType());
	else if(StructType* ST=dyn_cast<StructType>(baseType))
	{
		// TODO: This is broken for unions inside union. We would need to indirectly reference them.
		for(uint32_t i=0;i<ST->getNumElements();i++)
			addAllBaseTypesForByteLayout(st, ST->getElementType(i));
	}
	else
	{
		// If there is no base type so far, initialize it
		auto it = baseTypesForByteLayout.find(st);
		if(it == baseTypesForByteLayout.end())
			baseTypesForByteLayout.insert(std::make_pair(st, baseType));
		else if (it->second != baseType)
		{
			// The known base type is not the same as the passed one
			it->second = NULL;
		}
	}
}

void TypeOptimizer::gatherAllTypesInfo(const Module& M)
{
	for(const Function& F: M)
	{
		for(const BasicBlock& BB: F)
		{
			for(const Instruction& I: BB)
			{
				if(const IntrinsicInst* II=dyn_cast<IntrinsicInst>(&I))
				{
					if(II->getIntrinsicID()!=Intrinsic::cheerp_downcast)
						continue;
					// If a source type is downcasted with an offset != 0 we can't collapse the type
					// we keep track of this by setting the mapping to an empty vector
					StructType* sourceType = cast<StructType>(II->getOperand(0)->getType()->getPointerElementType());
					if(cast<ConstantInt>(II->getOperand(1))->getZExtValue() != 0)
					{
						downcastSourceToDestinationsMapping[sourceType].clear();
						continue;
					}
					// If the offset is 0 we need to append the destination type to the mapping
					// If the source type is in the map, but the vector is empty it means that we were
					// in the case above, so we don't add the new destType
					StructType* destType = cast<StructType>(II->getType()->getPointerElementType());
					auto it=downcastSourceToDestinationsMapping.find(sourceType);
					if(it != downcastSourceToDestinationsMapping.end() && it->second.empty())
						continue;
					downcastSourceToDestinationsMapping[sourceType].insert(destType);
				}
				else if(const BitCastInst* BC=dyn_cast<BitCastInst>(&I))
				{
					// Find out all the types that bytelayout structs are casted to
					StructType* st = dyn_cast<StructType>(BC->getSrcTy()->getPointerElementType());
					if(!st || !st->hasByteLayout())
						continue;
					addAllBaseTypesForByteLayout(st, BC->getDestTy()->getPointerElementType());
				}
			}
		}
	}
}

/**
	We can only collapse a downcast source if all the possible destinations collapse as well
*/
bool TypeOptimizer::isUnsafeDowncastSource(StructType* st)
{
	auto it=downcastSourceToDestinationsMapping.find(st);
	if(it == downcastSourceToDestinationsMapping.end())
		return false;
	// If the destinations set is empty it means that we have a downcast with an offset != 0
	// and we should not collapse this source
	if(it->second.empty())
		return true;
	// Finally, try to rewrite every destination type, if they all collapse the source will collapse as well
	for(StructType* destSt: it->second)
	{
		const TypeMappingInfo& destStInfo=rewriteType(destSt);
		if(destStInfo.elementMappingKind != TypeMappingInfo::COLLAPSED)
			return true;
	}
	return false;
}

TypeOptimizer::TypeMappingInfo TypeOptimizer::rewriteType(Type* t)
{
	assert(!newStructTypes.count(t));
	auto typeMappingIt=typesMapping.find(t);
	if(typeMappingIt!=typesMapping.end())
	{
		if(typeMappingIt->second.elementMappingKind == TypeMappingInfo::COLLAPSING)
		{
			// When we find a COLLAPSING type, we forward the request if the contained type is a struct
			// otherwise it will set the COLLAPSING_BUT_USED flag, in which case we need to abort the rewrite
			// See also below how the COLLAPSING flag is used
			if(typeMappingIt->second.mappedType->isStructTy())
			{
				assert(typeMappingIt->second.mappedType != t);
				return rewriteType(typeMappingIt->second.mappedType);
			}
			else
				typeMappingIt->second.elementMappingKind = TypeMappingInfo::COLLAPSING_BUT_USED;
		}
		return typeMappingIt->second;
	}
	auto CacheAndReturn = [&](Type* ret, TypeMappingInfo::MAPPING_KIND kind)
	{
		return typesMapping[t] = TypeMappingInfo(ret, kind);
	};
	if(StructType* st=dyn_cast<StructType>(t))
	{
		if(TypeSupport::isClientType(st))
			return CacheAndReturn(st, TypeMappingInfo::IDENTICAL);
		if(TypeSupport::hasByteLayout(st))
		{
			addAllBaseTypesForByteLayout(st, st);
			// If the data of this byte layout struct is always accessed as the same type, we can replace it with an array of that type
			// This is useful for an idiom used by C++ graphics code to have a vector both accessible as named elements and as an array
			// union { struct { double x,y,z; }; double elemets[3]; };
			auto it=baseTypesForByteLayout.find(st);
			assert(it!=baseTypesForByteLayout.end());
			if(it->second == NULL)
				return CacheAndReturn(st, TypeMappingInfo::IDENTICAL);
			// Check that the struct fits exactly N values of the base type
			uint32_t structSize = DL->getTypeAllocSize(st);
			uint32_t elementSize = DL->getTypeAllocSize(it->second);
			if(structSize % elementSize)
				return CacheAndReturn(st, TypeMappingInfo::IDENTICAL);

			// Replace this byte layout struct with an array
			uint32_t numElements = structSize / elementSize;
			Type* newType = ArrayType::get(it->second, numElements);
			return CacheAndReturn(newType, TypeMappingInfo::BYTE_LAYOUT_TO_ARRAY);
		}

		// Generate a new type inconditionally, it may end up being the same as the old one
		StructType* newStruct=StructType::create(st->getContext());
#ifndef NDEBUG
		newStructTypes.insert(newStruct);
#endif
		if(st->hasName())
		{
			SmallString<20> name=st->getName();
			st->setName("obsoletestruct");
			newStruct->setName(name);
		}
		// Tentatively map the type to the newStruct, it may be overridden if the type is collapsed
		typesMapping[t] = TypeMappingInfo(newStruct, TypeMappingInfo::IDENTICAL);

		// Since we can merge arrays of the same type in an struct it is possible that at the end of the process a single type will remain
		TypeMappingInfo::MAPPING_KIND newStructKind = TypeMappingInfo::IDENTICAL;
		// Forge the new element types
		SmallVector<Type*, 4> newTypes;
		bool hasMergedArrays=false;
		std::vector<std::pair<uint32_t, uint32_t>> membersMapping;
		if(st->getNumElements() > 1)
		{
			// We want to merge arrays of the same type in the same object
			// So, for each element type, keep track if there is already an array
			std::unordered_map<Type*, uint32_t> arraysFound;
			uint32_t directBaseLimit=0;
			for(uint32_t i=0;i<st->getNumElements();i++)
			{
				// We can't merge arrats across bases, so when we reach the limit of the previous direct base we
				// reset the merging state and compute a new limit
				if(i==directBaseLimit)
				{
					arraysFound.clear();
					StructType* curBase=st;
					while(curBase->getDirectBase() && curBase->getDirectBase()->getNumElements()>i)
						curBase=curBase->getDirectBase();
					directBaseLimit=curBase->getNumElements();
				}
				Type* elementType=st->getElementType(i);
				Type* rewrittenType=rewriteType(elementType);
				if(ArrayType* at=dyn_cast<ArrayType>(rewrittenType))
				{
					Type* arrayElementType=rewrittenType->getArrayElementType();
					auto arraysFoundIt=arraysFound.find(arrayElementType);
					// An array is already available for this type, just extend it
					if(arraysFoundIt!=arraysFound.end())
					{
						uint32_t typeIndex = arraysFoundIt->second;
						ArrayType* previousArrayType = cast<ArrayType>(newTypes[typeIndex]);
						newTypes[typeIndex] = ArrayType::get(arrayElementType, previousArrayType->getNumElements() + at->getNumElements());
						membersMapping.push_back(std::make_pair(typeIndex, previousArrayType->getNumElements()));
						hasMergedArrays=true;
						continue;
					}
					// Insert this array in the map, we will insert it in the vector just below
					arraysFound[arrayElementType] = newTypes.size();
				}
				membersMapping.push_back(std::make_pair(newTypes.size(), 0));
				// Add the new type
				newTypes.push_back(rewrittenType);
			}
			if(hasMergedArrays)
			{
				assert(!newTypes.empty());
				membersMappingData.insert(std::make_pair(st, membersMapping));
				newStructKind = TypeMappingInfo::MERGED_MEMBER_ARRAYS;
				//if(newTypes.size()==1 && !isPendingStruct)
				//	return CacheAndReturn(newTypes[0], TypeMappingInfo::MERGED_MEMBER_ARRAYS_AND_COLLAPSED);
			}
		}
		else if(st->getNumElements() == 1)
		{
			// We push the original type here, below we will try to collapse the struct to this element
			newTypes.push_back(st->getElementType(0));
		}

		// newTypes may have a single element because st has a single element or because all the elements collapsed into one
		if(newTypes.size() == 1)
		{
			// Stop if the element is just a int8, we may be dealing with an empty struct
			// Empty structs are unsafe as the int8 inside is just a placeholder and will be replaced
			// by a different type in a derived class
			// TODO: If pointers could be collapsed we may have implicit casts between base classes and derived classes
			if(!newTypes[0]->isIntegerTy(8) && !newTypes[0]->isPointerTy() && !TypeSupport::isJSExportedType(newStruct, *module))
			{
				// If this type is an unsafe downcast source and can't be collapse
				// we need to fall through to correctly set the mapped element
				if(!isUnsafeDowncastSource(st))
				{
					// To fix the following case A { B { C { A* } } } -> C { C* }
					// we prime the mapping to the contained element and use the COLLAPSING flag
					typesMapping[st] = TypeMappingInfo(newTypes[0], TypeMappingInfo::COLLAPSING);
					Type* collapsed = rewriteType(newTypes[0]);
					if(typesMapping[st].elementMappingKind != TypeMappingInfo::COLLAPSING_BUT_USED)
					{
						assert(typesMapping[st].elementMappingKind == TypeMappingInfo::COLLAPSING);
						if(newStructKind != TypeMappingInfo::MERGED_MEMBER_ARRAYS)
							return CacheAndReturn(collapsed, TypeMappingInfo::COLLAPSED);
						else
							return CacheAndReturn(collapsed, TypeMappingInfo::MERGED_MEMBER_ARRAYS_AND_COLLAPSED);
					}
					typesMapping[st] = TypeMappingInfo(newStruct, TypeMappingInfo::IDENTICAL);
				}
			}
			// Can't collapse, rewrite the member now
			Type* elementType=newTypes[0];
			Type* rewrittenType=rewriteType(elementType);
			newTypes[0]=rewrittenType;
		}

		StructType* newDirectBase = st->getDirectBase() ? dyn_cast<StructType>(rewriteType(st->getDirectBase()).mappedType) : NULL;
		newStruct->setBody(newTypes, st->isPacked(), newDirectBase);
		pendingStructTypes.erase(t);
		return CacheAndReturn(newStruct, newStructKind);
	}
	if(FunctionType* ft=dyn_cast<FunctionType>(t))
	{
		Type* newReturnType=rewriteType(ft->getReturnType());
		SmallVector<Type*, 4> newParameters;
		for(uint32_t i=0;i<ft->getNumParams();i++)
			newParameters.push_back(rewriteType(ft->getParamType(i)));
		return CacheAndReturn(FunctionType::get(newReturnType, newParameters, ft->isVarArg()), TypeMappingInfo::IDENTICAL);
	}
	if(PointerType* pt=dyn_cast<PointerType>(t))
	{
		Type* elementType = pt->getElementType();
		Type* newType = rewriteType(elementType);
		if(newType->isArrayTy())
		{
			// It's never a good idea to use pointers to array, we may end up creating wrapper arrays for arrays
			return CacheAndReturn(PointerType::get(newType->getArrayElementType(), 0), TypeMappingInfo::POINTER_FROM_ARRAY);
		}
		else if(newType == elementType)
			return CacheAndReturn(pt, TypeMappingInfo::IDENTICAL);
		else
			return CacheAndReturn(PointerType::get(newType, 0), TypeMappingInfo::IDENTICAL);
	}
	if(ArrayType* at=dyn_cast<ArrayType>(t))
	{
		Type* elementType = at->getElementType();
		const TypeMappingInfo& newInfo = rewriteType(elementType);
		Type* newType = newInfo.mappedType;
		if(ArrayType* subArray=dyn_cast<ArrayType>(newType))
		{
			// Flatten arrays of array
			return CacheAndReturn(ArrayType::get(newType->getArrayElementType(), at->getNumElements()*subArray->getNumElements()),
				TypeMappingInfo::FLATTENED_ARRAY);
		}
		else if(newType == elementType)
			return CacheAndReturn(at, TypeMappingInfo::IDENTICAL);
		else
			return CacheAndReturn(ArrayType::get(newType, at->getNumElements()), TypeMappingInfo::IDENTICAL);
	}
	return CacheAndReturn(t, TypeMappingInfo::IDENTICAL);
}

Constant* TypeOptimizer::rewriteConstant(Constant* C)
{
	// Immediately return for globals, we should never try to map their type as they are already rewritten
	if(GlobalVariable* GV=dyn_cast<GlobalVariable>(C))
	{
		assert(globalsMapping.count(GV));
		return globalsMapping[GV];
	}
	else if(isa<GlobalValue>(C))
		return C;
	TypeMappingInfo newTypeInfo = rewriteType(C->getType());
	if(ConstantExpr* CE=dyn_cast<ConstantExpr>(C))
	{
		auto getOriginalGlobalType = [&](Constant* C) -> Type*
		{
			GlobalValue* GV = dyn_cast<GlobalValue>(C);
			if(!GV)
				return C->getType();
			auto it = globalTypeMapping.find(GV);
			if(it == globalTypeMapping.end())
				return C->getType();
			else
				return it->second;
		};
		switch(CE->getOpcode())
		{
			case Instruction::GetElementPtr:
			{
				Constant* ptrOperand = CE->getOperand(0);
				Type* ptrType = getOriginalGlobalType(ptrOperand);
				ptrOperand = rewriteConstant(ptrOperand);
				SmallVector<Value*, 4> newIndexes;
				Type* targetType = rewriteType(CE->getType()->getPointerElementType());
				rewriteGEPIndexes(newIndexes, ptrType, ArrayRef<Use>(CE->op_begin()+1,CE->op_end()), targetType, NULL);
				return ConstantExpr::getGetElementPtr(ptrOperand, newIndexes);
			}
			case Instruction::BitCast:
			{
				Constant* srcOperand = rewriteConstant(CE->getOperand(0));
				return ConstantExpr::getBitCast(srcOperand, newTypeInfo.mappedType);
			}
			case Instruction::IntToPtr:
			{
				return ConstantExpr::getIntToPtr(CE->getOperand(0), newTypeInfo.mappedType);
			}
			default:
			{
				// Get a cloned CE with rewritten operands
				std::vector<Constant*> newOperands;
				for(Use& op: CE->operands())
					newOperands.push_back(rewriteConstant(cast<Constant>(op)));
				return CE->getWithOperands(newOperands);
			}
		}
	}
	else if(C->getType() == newTypeInfo.mappedType)
		return C;
	else if(isa<ConstantAggregateZero>(C))
		return Constant::getNullValue(newTypeInfo.mappedType);
	else if(isa<ConstantPointerNull>(C))
		return ConstantPointerNull::get(cast<PointerType>(newTypeInfo.mappedType));
	else if(isa<UndefValue>(C))
		return UndefValue::get(newTypeInfo.mappedType);
	else if(ConstantStruct* CS=dyn_cast<ConstantStruct>(C))
	{
		// TODO: Handle BYTE_LAYOUT_TO_ARRAY
		if(newTypeInfo.elementMappingKind == TypeMappingInfo::COLLAPSED)
		{
			assert(cast<StructType>(CS->getType())->getNumElements()==1);
			Constant* element = CS->getOperand(0);
			return rewriteConstant(element);
		}
		auto membersMappingIt = membersMappingData.find(CS->getType());
		bool hasMergedArrays = newTypeInfo.elementMappingKind == TypeMappingInfo::MERGED_MEMBER_ARRAYS ||
					newTypeInfo.elementMappingKind == TypeMappingInfo::MERGED_MEMBER_ARRAYS_AND_COLLAPSED;
		assert(!hasMergedArrays || membersMappingIt != membersMappingData.end());
		SmallVector<Constant*, 4> newElements;
		// Check if some of the contained constant structs needs to be merged
		for(uint32_t i=0;i<CS->getNumOperands();i++)
		{
			Constant* element = CS->getOperand(i);
			if(hasMergedArrays && membersMappingIt->second[i].first != (newElements.size()))
			{
				// This element has been remapped to another one. It must be an array
				SmallVector<Constant*, 4> mergedArrayElements;
				Constant* oldMember = newElements[membersMappingIt->second[i].first];
				Constant* newElement = rewriteConstant(element);
				assert(oldMember->getType()->getArrayElementType() == newElement->getType()->getArrayElementType());
				assert(isa<ConstantArray>(oldMember) && isa<ConstantArray>(newElement));
				// Insert all the elements of the existing member
				for(Use& op: oldMember->operands())
					mergedArrayElements.push_back(cast<Constant>(op));
				for(Use& op: newElement->operands())
					mergedArrayElements.push_back(cast<Constant>(op));
				
				ArrayType* mergedType = ArrayType::get(oldMember->getType()->getArrayElementType(), mergedArrayElements.size());
				newElements[membersMappingIt->second[i].first] = ConstantArray::get(mergedType, mergedArrayElements);
			}
			else
			{
				Constant* newElement = rewriteConstant(element);
				newElements.push_back(newElement);
			}
		}
		if(newTypeInfo.elementMappingKind == TypeMappingInfo::MERGED_MEMBER_ARRAYS_AND_COLLAPSED)
		{
			assert(newElements.size() == 1);
			return newElements[0];
		}
		return ConstantStruct::get(cast<StructType>(newTypeInfo.mappedType), newElements);
	}
	else if(ConstantArray* CA=dyn_cast<ConstantArray>(C))
	{
		assert(newTypeInfo.mappedType->isArrayTy());
		SmallVector<Constant*, 4> newElements;
		if(newTypeInfo.elementMappingKind == TypeMappingInfo::FLATTENED_ARRAY)
		{
			//TODO: Implement this
			return Constant::getNullValue(newTypeInfo.mappedType);
		}
		else
		{
			for(uint32_t i=0;i<CA->getNumOperands();i++)
			{
				Constant* element = CA->getOperand(i);
				Constant* newElement = rewriteConstant(element);
				newElements.push_back(newElement);
			}
		}
		return ConstantArray::get(cast<ArrayType>(newTypeInfo.mappedType), newElements);
	}
	else
		assert(false && "Unexpected constant in TypeOptimizer");
	return NULL;
}

void TypeOptimizer::rewriteIntrinsic(Function* F, FunctionType* FT)
{
	// If a type for this intrinsic is collapsed we need to use a differently named intrinsic
	// Make sure that this new intrinsic is also mapped to new types.
	// This lambda returns true if the name has not changed, as in that case we don't need a new intrinsic
	auto fixDepedendentIntrinsic = [&](Intrinsic::ID id, ArrayRef<Type*> Tys) -> bool
	{
		const std::string& intrName = Intrinsic::getName(id, Tys);
		// If the name does not change we only need to fix the type
		if(F->getName() == intrName)
		{
			F->mutateType(FT->getPointerTo());
			return true;
		}
		Function* intrF = F->getParent()->getFunction(intrName);
		// If the intrinsic with the new types is not already defined we will create a new fixed one later on
		if(!intrF || !pendingFunctions.count(intrF))
			return false;
		rewriteFunction(intrF);
		return false;
	};
	SmallVector<Type*, 3> newTys;
	switch(F->getIntrinsicID())
	{
		case Intrinsic::cheerp_upcast_collapsed:
		case Intrinsic::cheerp_cast_user:
		case Intrinsic::cheerp_downcast:
		case Intrinsic::cheerp_reallocate:
		{
			Type* localTys[] = { FT->getReturnType(), FT->getParamType(0)};
			newTys.insert(newTys.end(),localTys,localTys+2);
			break;
		}
		case Intrinsic::cheerp_element_distance:
		{
			Type* localTys[] = { FT->getParamType(0) };
			newTys.insert(newTys.end(),localTys,localTys+1);
			break;
		}
		case Intrinsic::lifetime_start:
		case Intrinsic::lifetime_end:
		{
			Type* localTys[] = { FT->getParamType(1) };
			newTys.insert(newTys.end(),localTys,localTys+1);
			break;
		}
		case Intrinsic::cheerp_allocate:
		{
			Type* localTys[] = { FT->getReturnType() };
			newTys.insert(newTys.end(),localTys,localTys+1);
			break;
		}
		case Intrinsic::cheerp_create_closure:
		{
			Type* localTys[] = { FT->getReturnType(), FT->getParamType(0), FT->getParamType(1) };
			newTys.insert(newTys.end(),localTys,localTys+3);
			break;
		}
		case Intrinsic::memcpy:
		case Intrinsic::memmove:
		{
			Type* localTys[] = { FT->getParamType(0), FT->getParamType(1), FT->getParamType(2) };
			newTys.insert(newTys.end(),localTys,localTys+3);
			break;
		}
	}
	if(!fixDepedendentIntrinsic((Intrinsic::ID)F->getIntrinsicID(), newTys))
	{
		Function* newFunc = Intrinsic::getDeclaration(F->getParent(), (Intrinsic::ID)F->getIntrinsicID(), newTys);
		assert(newFunc != F);
		while(!F->use_empty())
		{
			Use& U = *F->use_begin();
			CallInst* CI=cast<CallInst>(U.getUser());
			assert(U.getOperandNo()==CI->getNumArgOperands());
			CI->setOperand(U.getOperandNo(), newFunc);
		}
	}
}

void TypeOptimizer::rewriteGEPIndexes(SmallVector<Value*, 4>& newIndexes, Type* ptrType, ArrayRef<Use> idxs, Type* targetType, Instruction* insertionPoint)
{
	TypeMappingInfo ptrTypeMappingInfo = rewriteType(ptrType);
	bool addToLastIndex = false;
	auto AddIndex=[&](Value* V)
	{
		if(addToLastIndex)
		{
			if(insertionPoint)
				newIndexes.back() = BinaryOperator::Create(Instruction::Add, newIndexes.back(), V, "", insertionPoint);
			else
			{
				assert(isa<ConstantInt>(newIndexes.back()) && isa<ConstantInt>(V));
				newIndexes.back() = ConstantExpr::getAdd(cast<Constant>(newIndexes.back()), cast<Constant>(V));
			}
		}
		else
			newIndexes.push_back(V);
		addToLastIndex = false;
	};
	//TODO: Move in main loop below
	// With POINTER_FROM_ARRAY we already have a pointer to the first element
	if(ptrTypeMappingInfo.elementMappingKind == TypeMappingInfo::POINTER_FROM_ARRAY)
	{
		// We need to multiply the index by the right number of elements, corresponding to the size of the old type
		uint32_t oldTypeSize = DL->getTypeAllocSize(ptrType->getPointerElementType());
		uint32_t elementSize = DL->getTypeAllocSize(ptrTypeMappingInfo.mappedType->getPointerElementType());
		assert(!(oldTypeSize % elementSize));
		uint32_t numElements=oldTypeSize/elementSize;
		Constant* numElementsC = ConstantInt::get(idxs[0]->getType(), numElements);
		if(insertionPoint)
			AddIndex(BinaryOperator::Create(Instruction::Mul, idxs[0], numElementsC, "", insertionPoint));
		else
		{
			assert(isa<Constant>(idxs[0]));
			AddIndex(ConstantExpr::getMul(cast<Constant>(idxs[0]), numElementsC));
		}
		addToLastIndex=true;
	}
	else
		AddIndex(idxs[0]);
	Type* curType = ptrType->getPointerElementType();
	for(uint32_t i=1;i<idxs.size();i++)
	{
		TypeMappingInfo curTypeMappingInfo = rewriteType(curType);
		switch(curTypeMappingInfo.elementMappingKind)
		{
			case TypeMappingInfo::IDENTICAL:
				AddIndex(idxs[i]);
				break;
			case TypeMappingInfo::COLLAPSED:
				break;
			case TypeMappingInfo::BYTE_LAYOUT_TO_ARRAY:
			{
				assert(isa<StructType>(curType));
				// All the indexes needs to be flattened to a byte offset and then to an array offset
				SmallVector<Value*, 4> nextIndexes;
				Type* Int32Ty = IntegerType::get(curType->getContext(), 32);
				nextIndexes.push_back(ConstantInt::get(Int32Ty, 0));
				// NOTE: We are willingly iterating over 'i' again
				for(;i<idxs.size();i++)
				{
					// TODO: Support dynamic accesses
					assert(isa<ConstantInt>(idxs[i]));
					nextIndexes.push_back(idxs[i]);
				}
				// Forge a pointer type, as DataLayout::getIndexedOffset needs one
				uint32_t byteOffset = DL->getIndexedOffset(curType->getPointerTo(), nextIndexes);
				if(curTypeMappingInfo.mappedType == targetType)
				{
					assert(byteOffset == 0);
					return;
				}
				auto baseTypeIt = baseTypesForByteLayout.find(cast<StructType>(curType));
				assert(baseTypeIt != baseTypesForByteLayout.end() && baseTypeIt->second);
				uint32_t baseTypeSize = DL->getTypeAllocSize(baseTypeIt->second);
				assert(!(byteOffset % baseTypeSize));
				AddIndex(ConstantInt::get(Int32Ty, byteOffset / baseTypeSize));
				// All indexes have been consumed now, we can just return
				return;
			}
			case TypeMappingInfo::FLATTENED_ARRAY:
			{
				// We had something like [ N x [ M x T ] ] which is now [ N*M x T ]
				uint32_t oldTypeSize = DL->getTypeAllocSize(curType->getArrayElementType());
				uint32_t elementSize = DL->getTypeAllocSize(curTypeMappingInfo.mappedType->getArrayElementType());
				assert(!(oldTypeSize % elementSize));
				uint32_t numElements=oldTypeSize/elementSize;
				Constant* numElementsC = ConstantInt::get(idxs[i]->getType(), numElements);
				if(insertionPoint)
					AddIndex(BinaryOperator::Create(Instruction::Mul, idxs[i], numElementsC, "", insertionPoint));
				else
				{
					assert(isa<Constant>(idxs[i]));
					AddIndex(ConstantExpr::getMul(cast<Constant>(idxs[i]), numElementsC));
				}
				addToLastIndex = true;
				break;
			}
			case TypeMappingInfo::MERGED_MEMBER_ARRAYS:
			{
				assert(curType->isStructTy());
				StructType* oldStruct = cast<StructType>(curType);
				uint32_t elementIndex = cast<ConstantInt>(idxs[i])->getZExtValue();
				assert(membersMappingData.count(oldStruct));
				const std::pair<uint32_t, uint32_t>& mappedMember = membersMappingData[oldStruct][elementIndex];
				// The new index is mappedMember.first
				Type* Int32Ty = IntegerType::get(curType->getContext(), 32);
				AddIndex(ConstantInt::get(Int32Ty, mappedMember.first));
				// If mappedMember.second is not zero, also add a new index that can be eventually incremented later
				if(mappedMember.second)
				{
					AddIndex(ConstantInt::get(Int32Ty, mappedMember.second));
					addToLastIndex = true;
				}
				break;
			}
			case TypeMappingInfo::MERGED_MEMBER_ARRAYS_AND_COLLAPSED:
			{
				assert(curType->isStructTy());
				StructType* oldStruct = cast<StructType>(curType);
				uint32_t elementIndex = cast<ConstantInt>(idxs[i])->getZExtValue();
				assert(membersMappingData.count(oldStruct));
				const std::pair<uint32_t, uint32_t>& mappedMember = membersMappingData[oldStruct][elementIndex];
				assert(mappedMember.first == 0);
				Type* Int32Ty = IntegerType::get(curType->getContext(), 32);
				if(mappedMember.second)
				{
					AddIndex(ConstantInt::get(Int32Ty, mappedMember.second));
					addToLastIndex = true;
				}
				break;
			}
			case TypeMappingInfo::COLLAPSING:
			case TypeMappingInfo::COLLAPSING_BUT_USED:
			case TypeMappingInfo::POINTER_FROM_ARRAY:
				assert(false);
				break;
		}
		if(StructType* ST=dyn_cast<StructType>(curType))
			curType = ST->getElementType(cast<ConstantInt>(idxs[i])->getZExtValue());
		else
			curType = curType->getSequentialElementType();
	}
	assert(rewriteType(curType) == targetType);
	if(targetType->isArrayTy())
	{
		// TODO: Fix this in a proper way. Right now only for POINTER_FROM_ARRAY.
		Type* Int32 = IntegerType::get(curType->getContext(), 32);
		Value* Zero = ConstantInt::get(Int32, 0);
		AddIndex(Zero);
	}
}

void TypeOptimizer::rewriteFunction(Function* F)
{
	bool erased = pendingFunctions.erase(F);
	(void)erased;
	assert(erased);
	globalTypeMapping[F] = F->getType();
	// Rewrite the type
	Type* newFuncType = rewriteType(F->getType());
	// Keep track of the original types of local instructions
	std::unordered_map<Value*, Type*> localTypeMapping;
	auto getOriginalOperandType = [&](Value* v) -> Type*
	{
		auto it = localTypeMapping.find(v);
		if(it != localTypeMapping.end())
			return it->second;
		else if(GlobalValue* GV=dyn_cast<GlobalValue>(v))
		{
			assert(globalTypeMapping.count(GV));
			return globalTypeMapping[GV];
		}
		else
			return v->getType();
	};
	auto setOriginalOperandType = [&](Value* v, Type* t) -> void
	{
		localTypeMapping[v] = t;
	};
	// Keep track of instructions which have been remapped
	std::unordered_map<Value*, Value*> localInstMapping;
	auto getMappedOperand = [&](Value* v) -> Value*
	{
		auto it = localInstMapping.find(v);
		if(it != localInstMapping.end())
			return it->second;
		else
			return v;
	};
	auto setMappedOperand = [&](Value* v, Value* m) -> void
	{
		assert(v->getType()->isPointerTy() && m->getType()->isPointerTy());
		localInstMapping[v] = m;
	};
	if(newFuncType!=F->getType())
	{
		if(F->getIntrinsicID())
			rewriteIntrinsic(F, cast<FunctionType>(newFuncType->getPointerElementType()));
		else
			F->mutateType(newFuncType);
		// Change the types of the arguments
		for(Argument& a: F->getArgumentList())
		{
			Type* newArgType=cast<FunctionType>(newFuncType->getPointerElementType())->getParamType(a.getArgNo());
			if(newArgType==a.getType())
				continue;
			setOriginalOperandType(&a, a.getType());
			a.mutateType(newArgType);
		}
	}
	if(F->empty())
		return;
	SmallVector<BasicBlock*, 4> blocksInDFSOrder;
	std::unordered_set<BasicBlock*> usedBlocks;
	blocksInDFSOrder.push_back(&F->getEntryBlock());
	// The size of the vector will increase over time, this is by design
	for(uint32_t i=0;i<blocksInDFSOrder.size();i++)
	{
		BasicBlock* BB = blocksInDFSOrder[i];
		TerminatorInst* term = BB->getTerminator();
		for(uint32_t i=0;i<term->getNumSuccessors();i++)
		{
			BasicBlock* succ = term->getSuccessor(i);
			if(usedBlocks.count(succ))
				continue;
			usedBlocks.insert(succ);
			blocksInDFSOrder.push_back(succ);
		}
	}

	SmallVector<PHINode*, 4> delayedPHIs;
	// Rewrite instructions as needed
	for(BasicBlock* BB: blocksInDFSOrder)
	{
		for(Instruction& I: *BB)
		{
			switch(I.getOpcode())
			{
				default:
					if(I.getType()->isPointerTy())
						llvm::errs() << "INST " << I << "\n";
					assert(!I.getType()->isPointerTy() && "Unexpected instruction in TypeOptimizer");
					break;
				case Instruction::GetElementPtr:
				{
					Value* ptrOperand = I.getOperand(0);
					Type* ptrType = getOriginalOperandType(ptrOperand);
					if(rewriteType(ptrType) != ptrType || rewriteType(I.getType()) != I.getType())
					{
						SmallVector<Value*, 4> newIndexes;
						Type* targetType = rewriteType(I.getType()->getPointerElementType());
						rewriteGEPIndexes(newIndexes, ptrType, ArrayRef<Use>(I.op_begin()+1,I.op_end()), targetType, &I);
						Value* newPtrOperand = ptrOperand;
						if(isa<Instruction>(ptrOperand))
							newPtrOperand = getMappedOperand(ptrOperand);
						else if(isa<GlobalVariable>(ptrOperand))
							newPtrOperand = rewriteConstant(cast<Constant>(ptrOperand));
						else if(isa<Constant>(ptrOperand) && !isa<Function>(ptrOperand))
							newPtrOperand = rewriteConstant(cast<Constant>(ptrOperand));
						GetElementPtrInst* NewInst = GetElementPtrInst::Create(newPtrOperand, newIndexes);
						assert(!NewInst->getType()->getPointerElementType()->isArrayTy());
						NewInst->takeName(&I);
						NewInst->setIsInBounds(cast<GetElementPtrInst>(I).isInBounds());
						setMappedOperand(&I, NewInst);
						break;
					}
					// If the operand and the result types have not changed the indexes do not need any change as well
					// but we still need to check if the type of the GEP itself needs to be updated,
					// so fall through to the below cases. Please note that Call must check for IntrinsicInst for this to work.
				}
				case Instruction::Alloca:
				{
					TypeMappingInfo newInfo = rewriteType(I.getType());
					if(newInfo.mappedType==I.getType())
						break;
					setOriginalOperandType(&I, I.getType());
					if(newInfo.elementMappingKind == TypeMappingInfo::POINTER_FROM_ARRAY)
					{
						// In this case we need to rewrite the allocated type and use that directly
						// Moreover, we need to generate a GEP that will be used instead of this alloca
						Type* newAllocatedType = rewriteType(I.getType()->getPointerElementType());
						Type* newPtrType = PointerType::get(newAllocatedType, 0);
						I.mutateType(newPtrType);
						Type* Int32 = IntegerType::get(I.getType()->getContext(), 32);
						Value* Zero = ConstantInt::get(Int32, 0);
						Value* Indexes[] = { Zero, Zero };
						Instruction* newGEP = GetElementPtrInst::Create(&I, Indexes, "allocadecay");
						setMappedOperand(&I, newGEP);
					}
					else
						I.mutateType(newInfo.mappedType);
					break;
				}
				case Instruction::Call:
				{
					// We need to handle special intrinsics here
					if(IntrinsicInst* II=dyn_cast<IntrinsicInst>(&I))
					{
						if(II->getIntrinsicID() == Intrinsic::cheerp_upcast_collapsed)
						{
							// If the return type is not a struct anymore while the source type is still a
							// struct replace the upcast with a GEP
							Value* ptrOperand = I.getOperand(0);
							Type* curType = getOriginalOperandType(ptrOperand)->getPointerElementType();
							Type* newRetType = rewriteType(I.getType()->getPointerElementType());
							Type* newOpType = rewriteType(curType);
							if(!newRetType->isStructTy() && newOpType->isStructTy())
							{
								Type* Int32 = IntegerType::get(II->getContext(), 32);
								Value* Zero = ConstantInt::get(Int32, 0);
								Value* Indexes[] = { Zero, Zero };
								Value* newPtrOperand = isa<Constant>(ptrOperand) ?
										rewriteConstant(cast<Constant>(ptrOperand)) : getMappedOperand(ptrOperand);
								Instruction* newGEP = GetElementPtrInst::Create(newPtrOperand, Indexes, "gepforupcast");
								setMappedOperand(&I, newGEP);
								break;
							}
						}
					}
					// Fall through to next case
				}
				case Instruction::BitCast:
				case Instruction::ExtractValue:
				case Instruction::IntToPtr:
				case Instruction::Load:
				case Instruction::PHI:
				case Instruction::Ret:
				case Instruction::Select:
				case Instruction::Store:
				case Instruction::VAArg:
				{
					if(I.getType()->isVoidTy())
						break;
					Type* newType = rewriteType(I.getType());
					if(newType==I.getType())
						break;
					setOriginalOperandType(&I, I.getType());
					I.mutateType(newType);
					break;
				}
			}
			// We need to handle pointer PHIs later on, when all instructions are redefined
			if(PHINode* phi = dyn_cast<PHINode>(&I))
			{
				if(phi->getType()->isPointerTy())
				{
					delayedPHIs.push_back(phi);
					continue;
				}
			}
			for(uint32_t i=0;i<I.getNumOperands();i++)
			{
				Value* op=I.getOperand(i);
				if(Constant* C = dyn_cast<Constant>(op))
					I.setOperand(i, rewriteConstant(C));
				else
					I.setOperand(i, getMappedOperand(op));
			}
		}
	}
	for(PHINode* phi: delayedPHIs)
	{
		for(uint32_t i=0;i<phi->getNumIncomingValues();i++)
		{
			Value* op=phi->getIncomingValue(i);
			if(Constant* C = dyn_cast<Constant>(op))
				phi->setIncomingValue(i, rewriteConstant(C));
			else
				phi->setIncomingValue(i, getMappedOperand(op));
		}
	}
	for(auto it: localInstMapping)
	{
		// Insert new instruction
		cast<Instruction>(it.second)->insertAfter(cast<Instruction>(it.first));
		//TODO: This is an hack for POINTER_FROM_ARRAY
		if(isa<AllocaInst>(it.first))
			continue;
		// Delete old instructions
		cast<Instruction>(it.first)->replaceAllUsesWith(UndefValue::get(it.first->getType()));
		cast<Instruction>(it.first)->eraseFromParent();
	}
}

Constant* TypeOptimizer::rewriteGlobal(GlobalVariable* GV)
{
	TypeMappingInfo newInfo = rewriteType(GV->getType());
	globalTypeMapping[GV] = GV->getType();
	if(GV->getType()==newInfo.mappedType)
	{
		assert(!GV->getType()->getPointerElementType()->isArrayTy());
		return GV;
	}
	if(newInfo.elementMappingKind == TypeMappingInfo::POINTER_FROM_ARRAY)
	{
		Type* newAllocatedType = rewriteType(GV->getType()->getPointerElementType());
		Type* newPtrType = PointerType::get(newAllocatedType, 0);
		GV->mutateType(newPtrType);
		Type* Int32 = IntegerType::get(GV->getType()->getContext(), 32);
		Value* Zero = ConstantInt::get(Int32, 0);
		Value* Indexes[] = { Zero, Zero };
		return ConstantExpr::getGetElementPtr(GV, Indexes);
	}
	else
		GV->mutateType(newInfo.mappedType);
	return GV;
}

void TypeOptimizer::rewriteGlobalInit(GlobalVariable* GV)
{
	if(!GV->hasInitializer() || isa<GlobalValue>(GV->getInitializer()))
		return;
	Type* GVType = globalTypeMapping[GV]->getPointerElementType();
	Type* rewrittenType = rewriteType(GVType);
	if(GVType==rewrittenType)
		return;
	// We need to change type, so we have to forge a new initializer
	Constant* rewrittenInit = rewriteConstant(GV->getInitializer());
	GV->setInitializer(rewrittenInit);
}

bool TypeOptimizer::runOnModule(Module& M)
{
	// Get required auxiliary data
	module = &M;
	DataLayoutPass* DLP = getAnalysisIfAvailable<DataLayoutPass>();
	assert(DLP);
	DL = &DLP->getDataLayout();
	assert(DL);
	// Do a preprocessing step to gather data that we can't get inline
	gatherAllTypesInfo(M);
	// Update the type for all global variables
	for(GlobalVariable& GV: M.getGlobalList())
	{
		Constant* rewrittenGlobal=rewriteGlobal(&GV);
		globalsMapping.insert(std::make_pair(&GV, rewrittenGlobal));
	}
	for(Function& F: M)
		pendingFunctions.insert(&F);
	// Rewrite all functions
	while(!pendingFunctions.empty())
		rewriteFunction(*pendingFunctions.begin());
	// Now that all functions are fixes, update the global initializer
	for(GlobalVariable& GV: M.getGlobalList())
		rewriteGlobalInit(&GV);
	for(GlobalAlias& GA: M.getAliasList())
	{
		Type* rewrittenType = rewriteType(GA.getType());
		GA.mutateType(rewrittenType);
	}
	while(!pendingStructTypes.empty())
		rewriteType(*pendingStructTypes.begin());
	assert(pendingFunctions.empty());
	// Reuse pendingFunctions to store intrinsics that should be delete
	for(Function& F: M)
	{
		if(F.getIntrinsicID() && F.use_empty())
			pendingFunctions.insert(&F);
	}
	for(Function* F: pendingFunctions)
		F->eraseFromParent();
	return true;
}

char TypeOptimizer::ID = 0;

}

using namespace cheerp;

INITIALIZE_PASS_BEGIN(TypeOptimizer, "TypeOptimizer", "Optimize struct and array types",
                      false, false)
INITIALIZE_PASS_END(TypeOptimizer, "TypeOptimizer", "Optimize struct and array types",
                    false, false)
