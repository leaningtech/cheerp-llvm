//===-- AllocaMerging.cpp - The Cheerp JavaScript generator ---------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2014-2018 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "CheerpAllocaMerging"
#include <algorithm>
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/Cheerp/AllocaMerging.h"
#include "llvm/Cheerp/GlobalDepsAnalyzer.h"
#include "llvm/Cheerp/PointerAnalyzer.h"
#include "llvm/Cheerp/Registerize.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

STATISTIC(NumAllocaMerged, "Number of alloca which are merged");

namespace cheerp {

void AllocaMergingBase::analyzeBlock(const cheerp::Registerize& registerize, BasicBlock& BB,
				AllocaInfos& allocaInfos)
{
	for(Instruction& I: BB)
	{
		if(I.getOpcode() == Instruction::Alloca)
		{
			AllocaInst* AI = cast<AllocaInst>(&I);
			if(AI->isArrayAllocation())
				continue;
			allocaInfos.push_back(std::make_pair(AI, registerize.getLiveRangeForAlloca(AI)));
		}
	}
}

bool AllocaMerging::areTypesEquivalent(const cheerp::TypeSupport& types, cheerp::PointerAnalyzer& PA, Type* a, Type* b, bool asmjs)
{
	//TODO: Integer types may be equivalent as well
	if(a==b)
		return true;
	else if(asmjs && ((a->isPointerTy()||a->isIntegerTy(32))&&(b->isPointerTy()||b->isIntegerTy(32))))
		return true;
	else if(a->isPointerTy() && b->isPointerTy())
		return true;
	else if(asmjs && a->isFloatTy() && b->isFloatTy())
		return true;
	else if(asmjs && a->isDoubleTy() && b->isDoubleTy())
		return true;
	else if(!asmjs && a->isFloatingPointTy() && b->isFloatingPointTy())
		return true;
	else if(a->isArrayTy() && b->isArrayTy())
	{
		return cast<ArrayType>(a)->getNumElements()==cast<ArrayType>(b)->getNumElements() &&
			areTypesEquivalent(types, PA, a->getArrayElementType(), b->getArrayElementType(), asmjs);
	}
	else if(a->isStructTy() && b->isStructTy())
	{
		// TODO: Byte layout structs with the same size are equivalent
		if(cast<StructType>(a)->hasByteLayout() ||
			cast<StructType>(b)->hasByteLayout())
			return false;
		StructType* stA = cast<StructType>(a);
		StructType* stB = cast<StructType>(b);
		if(stA->getNumElements() != stB->getNumElements())
			return false;
		for(uint32_t i=0;i<stA->getNumElements();i++)
		{
			Type* elementA = stA->getElementType(i);
			Type* elementB = stB->getElementType(i);
			// The types needs to have consistent wrapper arrays
			if(types.useWrapperArrayForMember(PA, stA, i) ^ types.useWrapperArrayForMember(PA, stB, i))
				return false;
			if(!areTypesEquivalent(types, PA, elementA, elementB, asmjs))
				return false;
		}
		return true;
	}
	else
		return false;
}

bool AllocaMerging::runOnFunction(Function& F)
{
	cheerp::PointerAnalyzer & PA = getAnalysis<cheerp::PointerAnalyzer>();
	cheerp::Registerize & registerize = getAnalysis<cheerp::Registerize>();
	cheerp::TypeSupport types(*F.getParent());
	bool asmjs = F.getSection()==StringRef("asmjs");
	AllocaInfos allocaInfos;
	// Gather all the allocas
	for(BasicBlock& BB: F)
		analyzeBlock(registerize, BB, allocaInfos);
	if (allocaInfos.size() < 2)
		return false;
	bool Changed = false;
	BasicBlock& entryBlock=F.getEntryBlock();
	// Look if we can merge allocas of the same type
	for(auto targetCandidate=allocaInfos.begin();targetCandidate!=allocaInfos.end();++targetCandidate)
	{
		AllocaInst* targetAlloca = targetCandidate->first;
		Type* targetType = targetAlloca->getAllocatedType();
		// The range storing the sum of all ranges merged into target
		cheerp::Registerize::LiveRange targetRange(targetCandidate->second);
		// If the range is empty, we have an alloca that we can't analyze
		if (targetRange.empty())
			continue;
		std::vector<AllocaInfos::iterator> mergeSet;
		auto sourceCandidate=targetCandidate;
		++sourceCandidate;
		for(;sourceCandidate!=allocaInfos.end();++sourceCandidate)
		{
			AllocaInst* sourceAlloca = sourceCandidate->first;
			Type* sourceType = sourceAlloca->getAllocatedType();
			// Bail out for non compatible types
			if(!areTypesEquivalent(types, PA, targetType, sourceType, asmjs))
				continue;
			const cheerp::Registerize::LiveRange& sourceRange = sourceCandidate->second;
			// Bail out if this source candidate is not analyzable
			if(sourceRange.empty())
				continue;
			// Bail out if the allocas interfere
			if(targetRange.doesInterfere(sourceRange))
				continue;
			// Add the range to the target range and the source alloca to the mergeSet
			mergeSet.push_back(sourceCandidate);
			PA.invalidate(sourceAlloca);
			targetRange.merge(sourceRange);
		}

		// If the merge set is empty try another target
		if(mergeSet.empty())
			continue;

		PA.invalidate(targetAlloca);

		if(!Changed)
			registerize.invalidateLiveRangeForAllocas(F);

		// Make sure that this alloca is in the entry block
		if(targetAlloca->getParent()!=&entryBlock)
			targetAlloca->moveBefore(entryBlock.begin());
		// We can merge the allocas
		for(const AllocaInfos::iterator& it: mergeSet)
		{
			AllocaInst* allocaToMerge = it->first;
			Instruction* targetVal=targetAlloca;
			if(targetVal->getType()!=allocaToMerge->getType())
			{
				targetVal=new BitCastInst(targetVal, allocaToMerge->getType());
				targetVal->insertAfter(targetAlloca);
			}
			allocaToMerge->replaceAllUsesWith(targetVal);
			allocaToMerge->eraseFromParent();
			if(targetVal != targetAlloca)
				PA.getPointerKind(targetVal);
			allocaInfos.erase(it);
			NumAllocaMerged++;
		}
		PA.getPointerKind(targetAlloca);
		Changed = true;
	}
	if(Changed)
		registerize.computeLiveRangeForAllocas(F);
	return Changed;
}

const char *AllocaMerging::getPassName() const {
	return "AllocaMerging";
}

void AllocaMerging::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addRequired<cheerp::Registerize>();
	AU.addPreserved<cheerp::Registerize>();
	AU.addRequired<cheerp::PointerAnalyzer>();
	AU.addPreserved<cheerp::PointerAnalyzer>();
	AU.addRequired<cheerp::GlobalDepsAnalyzer>();
	AU.addPreserved<cheerp::GlobalDepsAnalyzer>();

	llvm::FunctionPass::getAnalysisUsage(AU);
}

char AllocaMerging::ID = 0;

FunctionPass *createAllocaMergingPass() { return new AllocaMerging(); }

bool AllocaArraysMerging::checkUsesForArrayMerging(AllocaInst* alloca)
{
	for(User* user: alloca->users())
	{
		// GEPs with a single op are indexing an array-of-arrays
		// We don't deal with them
		if (isa<GetElementPtrInst>(user) && user->getNumOperands()>2)
		{
			// Check that we are simply dereferencing the alloca pointer
			ConstantInt* CI=dyn_cast<ConstantInt>(user->getOperand(1));
			if(!CI || !CI->isNullValue())
				return false;
		}
		// BitCast for the lifetime instrinsics and bitcasts of i8 arrays to BL structs are ok
		else if (isa<BitCastInst>(user))
		{
			if(alloca->getAllocatedType()->getArrayElementType()->isIntegerTy(8) &&
				TypeSupport::hasByteLayout(user->getType()->getPointerElementType()))
			{
				return true;
			}
			for(User* bitcastUser: user->users())
			{
				if(IntrinsicInst* II=dyn_cast<IntrinsicInst>(bitcastUser))
				{
					if(II->getIntrinsicID()!=Intrinsic::lifetime_start &&
						II->getIntrinsicID()!=Intrinsic::lifetime_end)
					{
						return false;
					}
				}
				else
					return false;
			}
		}
		else
			return false;
	}
	return true;
}

bool AllocaArraysMerging::runOnFunction(Function& F)
{
	class ArraysToMerge
	{
	private:
		std::map<AllocaInst*, uint32_t> arraysToMerge;
		uint32_t currentOffset;
	public:
		ArraysToMerge():currentOffset(0)
		{
		}
		bool empty() const
		{
			return arraysToMerge.empty();
		}
		std::map<AllocaInst*, uint32_t>::iterator begin()
		{
			return arraysToMerge.begin();
		}
		std::map<AllocaInst*, uint32_t>::iterator end()
		{
			return arraysToMerge.end();
		}
		void add(AllocaInst* a)
		{
			arraysToMerge.insert(std::make_pair(a, currentOffset));
			currentOffset+=cast<ArrayType>(a->getAllocatedType())->getNumElements();
		}
		uint32_t getNewSize() const
		{
			return currentOffset;
		}
	};

	cheerp::PointerAnalyzer & PA = getAnalysis<cheerp::PointerAnalyzer>();
	cheerp::Registerize & registerize = getAnalysis<cheerp::Registerize>();
	cheerp::GlobalDepsAnalyzer & GDA = getAnalysis<cheerp::GlobalDepsAnalyzer>();
	std::list<std::pair<AllocaInst*, cheerp::Registerize::LiveRange>> allocaInfos;
	// Gather all the allocas
	for(BasicBlock& BB: F)
		analyzeBlock(registerize, BB, allocaInfos);
	if (allocaInfos.size() < 2)
		return false;
	bool Changed = false;
	// We can also try to merge arrays of the same type, if only pointers to values are passed around
	while(!allocaInfos.empty())
	{
		// Build a map of array to be merged and their offseet into the new array
		ArraysToMerge arraysToMerge;
		auto targetCandidate = allocaInfos.begin();
		AllocaInst* targetAlloca = targetCandidate->first;
		if(!targetAlloca->getAllocatedType()->isArrayTy() ||
			// Check target uses
			!checkUsesForArrayMerging(targetAlloca))
		{
				allocaInfos.erase(targetCandidate);
				continue;
		}
		Type* targetElementType = targetAlloca->getAllocatedType()->getSequentialElementType();
		auto sourceCandidate=targetCandidate;
		++sourceCandidate;
		// Now that we have computed the sourceCandidate we can invalidate the targetCandidate
		allocaInfos.erase(targetCandidate);
		while(sourceCandidate!=allocaInfos.end())
		{
			AllocaInst* sourceAlloca = sourceCandidate->first;
			// Check that allocas are arrays of the same type
			if(!sourceAlloca->getAllocatedType()->isArrayTy())
			{
				++sourceCandidate;
				continue;
			}
			// Both are arrays, check the types
			if(targetElementType != sourceAlloca->getAllocatedType()->getSequentialElementType())
			{
				++sourceCandidate;
				continue;
			}
			// Verify that the source candidate has supported uses
			if(!checkUsesForArrayMerging(sourceAlloca))
			{
				++sourceCandidate;
				continue;
			}
			// We can merge the source and the target
			// If the set is empty add the target as well
			if(arraysToMerge.empty())
				arraysToMerge.add(targetAlloca);
			arraysToMerge.add(sourceAlloca);
			auto oldCandidate = sourceCandidate;
			++sourceCandidate;
			// Now that we have moved to the next candidate, we can invalidate the old one
			allocaInfos.erase(oldCandidate);
		}
		// If we have a non-empty set of alloca merge them
		if (arraysToMerge.empty())
			continue;

		if(!Changed)
			registerize.invalidateLiveRangeForAllocas(F);
		// Build new alloca
		Type* newAllocaType = ArrayType::get(targetElementType, arraysToMerge.getNewSize());
		// Add the new struct type to the GlobalDepsAnalyzer, it may need the createArray helper
		GDA.visitType(newAllocaType, /*forceTypedArray*/ false);
		AllocaInst* newAlloca = new AllocaInst(newAllocaType, "mergedArray", &(*F.getEntryBlock().begin()));
		Type* indexType = IntegerType::get(newAllocaType->getContext(), 32);
		// Change every use of every merged array with an appropiate GEP
		for(auto it: arraysToMerge)
		{
			AllocaInst* allocaToMerge = it.first;
			uint32_t baseOffset = it.second;
			SmallVector<User*, 4> users(allocaToMerge->users());
			for(User* u: users)
			{
				if(GetElementPtrInst* oldGep = dyn_cast<GetElementPtrInst>(u))
				{
					// Build 2 GEPs, one to reach the first element in the merged array
					// and the other for the rest of the offsets
					SmallVector<Value*, 4> indices;
					// Dereference array
					indices.push_back(ConstantInt::get(indexType, 0));
					// Reach offset
					indices.push_back(ConstantInt::get(indexType, baseOffset));
					Value* gep1 = GetElementPtrInst::Create(newAlloca, indices, "", oldGep);
					// Apply all the old offsets but the first one using a new GEP
					indices.clear();
					indices.insert(indices.begin(), oldGep->idx_begin()+1, oldGep->idx_end());
					Value* gep2 = GetElementPtrInst::Create(gep1, indices, "", oldGep);
					// Replace all uses with gep2
					oldGep->replaceAllUsesWith(gep2);
					PA.invalidate(oldGep);
					oldGep->eraseFromParent();
				}
				else if(BitCastInst* BI=dyn_cast<BitCastInst>(u))
				{
					//Only used for lifetime intrinsics
					Value* newBitCast=new BitCastInst(newAlloca, BI->getType(), "", BI);
					BI->replaceAllUsesWith(newBitCast);
					PA.invalidate(BI);
					BI->eraseFromParent();
				}
				else
					assert(false && "Unexpected use while merging arrays");
			}
			// Kill the alloca itself now
			PA.invalidate(allocaToMerge);
			allocaToMerge->eraseFromParent();
			Changed = true;
		}
	}
	if(Changed)
		registerize.computeLiveRangeForAllocas(F);
	return Changed;
}

const char *AllocaArraysMerging::getPassName() const {
	return "AllocaArraysMerging";
}

void AllocaArraysMerging::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addRequired<cheerp::PointerAnalyzer>();
	AU.addPreserved<cheerp::PointerAnalyzer>();
	AU.addRequired<cheerp::Registerize>();
	AU.addPreserved<cheerp::Registerize>();
	AU.addRequired<cheerp::GlobalDepsAnalyzer>();
	AU.addPreserved<cheerp::GlobalDepsAnalyzer>();

	llvm::FunctionPass::getAnalysisUsage(AU);
}

char AllocaArraysMerging::ID = 0;

FunctionPass *createAllocaArraysMergingPass() { return new AllocaArraysMerging(); }

<<<<<<< HEAD
bool AllocaStoresExtractor::validType(llvm::Type* t, const Module& module)
{
	if(TypeSupport::hasByteLayout(t))
		return false;
	StructType* ST = dyn_cast<StructType>(t);
	if(ST)
	{
		if(ST->getNumElements() > V8MaxLiteralProperties)
			return false;
		if(TypeSupport::isJSExportedType(ST, module))
			return false;
	}
	ArrayType* AT = dyn_cast<ArrayType>(t);
	if(!AT)
		return true;
	// NOTE: This is slightly conservative, we assume double typed arrays are always used
	if(TypeSupport::isTypedArrayType(AT->getElementType(), /*forceTypedArray*/true))
		return false;
	if(AT->getNumElements() > V8MaxLiteralProperties)
		return false;
	return true;
}

bool AllocaStoresExtractor::runOnBasicBlock(BasicBlock& BB, const Module& module)
{
	if(!DL)
	{
		DataLayoutPass* DLP = getAnalysisIfAvailable<DataLayoutPass>();
		assert(DLP);
		DL = &DLP->getDataLayout();
		assert(DL);
		TLI = getAnalysisIfAvailable<TargetLibraryInfo>();
		assert(TLI);
	}
	// Map between insts and the underlying allocas/offsets in bytes
	// NOTE: A negative offset encodes that we can't analyze across this inst, but we still need to account for it to check for escapes
	std::unordered_map<llvm::Instruction*, std::pair<llvm::AllocaInst*, int32_t>> instsToAlloca;
	std::unordered_set<llvm::AllocaInst*> notEscapedAllocas;
	// NOTE: Until the alloca escapes it is actually safe to analyze even across side effects
	//       Even arbitrary code cannot touch an alloca with an unknown address
	for(Instruction& I: BB)
	{
		if(AllocaInst* AI = dyn_cast<AllocaInst>(&I))
		{
			if(AI->isArrayAllocation())
				continue;
			// Only handle types which use the literal representation
			if(!validType(AI->getAllocatedType(), module))
				continue;
			// Put in the same map as GEPs/bitcast to simpify lookups
			instsToAlloca.insert(std::make_pair(AI, std::make_pair(AI, 0)));
			notEscapedAllocas.insert(AI);
			continue;
		}
		else if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(&I))
		{
			// Check if the GEP references directly or indirectly an alloca
			Instruction* opI = dyn_cast<Instruction>(GEP->getOperand(0));
			if(!opI)
				continue;
			auto it = instsToAlloca.find(opI);
			if(it == instsToAlloca.end())
			{
				// Nope, nothing to do with this GEP
				continue;
			}
			// If the operand is already invalid, this GEP also is
			if(it->second.second < 0)
			{
				instsToAlloca.insert(std::make_pair(GEP, it->second));
				continue;
			}
			// Manually traverse the GEP, while
			// 1) Checking that all the offsets are constants
			// 2) Accumulating the total offset
			// 3) Verying that we don't cross a big structs, those are not trackable
			int32_t totalOffset = 0;
			Type* curType = opI->getType();
			for(unsigned i=1;i<GEP->getNumOperands();i++)
			{
				Value* op = GEP->getOperand(i);
				ConstantInt* CI = dyn_cast<ConstantInt>(op);
				if(!CI)
				{
					totalOffset = -1;
					break;
				}
				int32_t index = CI->getSExtValue();
				if(index < 0)
				{
					totalOffset = -1;
					break;
				}

				// Only handle types which use the literal representation
				if(!validType(curType, module))
				{
					totalOffset = -1;
					break;
				}
				if(StructType* ST = dyn_cast<StructType>(curType))
				{
					const StructLayout* SL = DL->getStructLayout( ST );
					totalOffset += SL->getElementOffset(index);
					curType = ST->getElementType(index);
				}
				else
				{
					uint32_t elementSize = DL->getTypeAllocSize(curType->getSequentialElementType());
					totalOffset += elementSize * index;
					curType = curType->getSequentialElementType();
				}
			}
			// If totalOffset is negative we can't analyze across this GEP, but we still need to check for memory escaping it
			if(totalOffset >= 0)
			{
				totalOffset += it->second.second;
			}
			instsToAlloca.insert(std::make_pair(GEP, std::make_pair(it->second.first, totalOffset)));
			continue;
		}
		else if(BitCastInst* BI = dyn_cast<BitCastInst>(&I))
		{
			// Only allow type safe bitcasts, namely the ones that cast to a direct base
			Instruction* opI = dyn_cast<Instruction>(BI->getOperand(0));
			if(!opI)
				continue;
			auto it = instsToAlloca.find(opI);
			if(it == instsToAlloca.end())
			{
				// Nope, nothing to do
				continue;
			}
			// If the operand is already invalid, the bitcast also is
			if(it->second.second < 0)
			{
				instsToAlloca.insert(std::make_pair(BI, it->second));
				continue;
			}
			StructType* srcType = dyn_cast<StructType>(opI->getType());
			StructType* dstType = dyn_cast<StructType>(BI->getType());
			// If either are not structs fall to escaping logic
			if(srcType && dstType)
			{
				bool isDirectBase = false;
				while(StructType* directBase = srcType->getDirectBase())
				{
					if(directBase == dstType)
					{
						isDirectBase = true;
						break;
					}
					srcType = directBase;
				}
				if(isDirectBase)
				{
					instsToAlloca.insert(std::make_pair(BI, it->second));
					continue;
				}
				// Not a direct base cast, fall to escaping logic
			}
		}
		else if(StoreInst* SI = dyn_cast<StoreInst>(&I))
		{
			// If we are storing to a tracked pointer we can remove this store
			// Otherwise we fall through below to the escaping logic
			Instruction* opI = dyn_cast<Instruction>(SI->getPointerOperand());
			if(opI)
			{
				auto it = instsToAlloca.find(opI);
				if(it != instsToAlloca.end())
				{
					// TODO: Improve logic to handle non-constants, we could also allow insts defined above the alloca
					if(it->second.second < 0 || !isa<Constant>(SI->getValueOperand()))
					{
						// This offset/value is not trackable, but it is also not an escape
						// use 'continue' to avoid falling in the escaping logic
						continue;
					}
					// We can only handle floating point values with a fractional part, otherwise we will confuse the type system
					if(ConstantFP* fp = dyn_cast<ConstantFP>(SI->getValueOperand()))
					{
						if(fp->getValueAPF().isInteger())
						{
							continue;
						}
					}
					OffsetToValueMap& map = allocaStores[it->second.first];
					// NOTE: We use the [] operator here, and we might override a previous store.
					// This is fine as we don't handle Loads in this pass, the first load will cause the alloca to escape
					// If this change we need to be more careful here!
					map[it->second.second] = SI->getValueOperand();
					instsToRemove.push_back(SI);
					continue;
				}
			}
		}
		// If any of the tracked values are used by not handled instructions, the corresponding alloca escapes
		for(Value* op: I.operands())
		{
			Instruction* opI = dyn_cast<Instruction>(op);
			if(!opI)
				continue;
			auto it = instsToAlloca.find(opI);
			if(it == instsToAlloca.end())
				continue;
			AllocaInst* escapingAlloca = it->second.first;
			bool erased = notEscapedAllocas.erase(escapingAlloca);
			(void)erased;
			assert(erased);
			// TODO: Maybe add another structure to speed this up
			it = instsToAlloca.begin();
			auto itE = instsToAlloca.end();
			while(it != itE)
			{
				auto prevIt = it;
				++it;
				if(prevIt->second.first == escapingAlloca)
					instsToAlloca.erase(prevIt);
			}
		}
	}
	return false;
}

void AllocaStoresExtractor::destroyStores()
{
	std::set<BasicBlock*> modifiedBlocks;
	// Erase all queued instructions
	for(Instruction* I: instsToRemove)
	{
		modifiedBlocks.insert(I->getParent());
		I->eraseFromParent();
	}
	// Go over insts in the blocks backward to remove all insts without uses
	for(BasicBlock* BB: modifiedBlocks)
	{
		auto it = BB->end();
		--it;
		do
		{
			Instruction* I = &(*it);
			--it;
			if(isInstructionTriviallyDead(I, TLI))
				I->eraseFromParent();
		}
		while(it != BB->begin());
	}
}

bool AllocaStoresExtractor::runOnModule(Module& M)
{
	bool Changed = false;
	for(Function& F: M)
	{
		for(BasicBlock& BB: F)
			Changed |= runOnBasicBlock(BB, M);
	}
	return Changed;
}

const AllocaStoresExtractor::OffsetToValueMap* AllocaStoresExtractor::getValuesForAlloca(const llvm::AllocaInst* AI) const
{
	auto it = allocaStores.find(AI);
	if(it == allocaStores.end())
		return nullptr;
	else
		return &it->second;
}

const char *AllocaStoresExtractor::getPassName() const {
	return "AllocaStoresExtractor";
}

void AllocaStoresExtractor::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addPreserved<cheerp::PointerAnalyzer>();
	AU.addPreserved<cheerp::Registerize>();
	AU.addPreserved<cheerp::GlobalDepsAnalyzer>();
	llvm::ModulePass::getAnalysisUsage(AU);
}

char AllocaStoresExtractor::ID = 0;

ModulePass *createAllocaStoresExtractor() { return new AllocaStoresExtractor(); }

bool ByteLayoutAllocaToByteArray::runOnBasicBlock(BasicBlock& BB)
{
	DataLayoutPass* DLP = getAnalysisIfAvailable<DataLayoutPass>();
	assert(DLP);
	const DataLayout* DL = &DLP->getDataLayout();
	assert(DL);
	bool Changed = false;
	auto it = BB.begin();
	auto itE = BB.end();
	while(it != itE)
	{
		AllocaInst* AI = dyn_cast<AllocaInst>(&(*it));
		++it;
		if(!AI)
			continue;
		if(AI->isArrayAllocation())
			continue;
		StructType* ST = dyn_cast<StructType>(AI->getAllocatedType());
		if(!ST)
			continue;
		if(!ST->hasByteLayout())
			continue;
		// Convert this struct alloca to an i8 array of the same size. These will be merged later on.
		// TODO: Maybe move this pass after AllocaMerging
		uint32_t byteSize = DL->getTypeAllocSize(ST);
		AllocaInst* newI = new AllocaInst(ArrayType::get(IntegerType::get(ST->getContext(), 8), byteSize), "", AI);
		newI->takeName(AI);
		Type* indexType = IntegerType::get(ST->getContext(), 32);
		SmallVector<Value*, 4> indices;
		indices.push_back(ConstantInt::get(indexType, 0));
		indices.push_back(ConstantInt::get(indexType, 0));
		Instruction* newGEP = GetElementPtrInst::Create(newI, indices, "", AI);
		Instruction* newCast = new BitCastInst(newGEP, AI->getType(), "", AI);
		AI->replaceAllUsesWith(newCast);
		AI->eraseFromParent();
		Changed = true;
	}
	return Changed;
}

const char *ByteLayoutAllocaToByteArray::getPassName() const {
	return "ByteLayoutAllocaToByteArray";
}

char ByteLayoutAllocaToByteArray::ID = 0;

BasicBlockPass *createByteLayoutAllocaToByteArrayPass() { return new ByteLayoutAllocaToByteArray(); }

}

using namespace cheerp;

INITIALIZE_PASS_BEGIN(AllocaMerging, "AllocaMerging", "Merge alloca instructions used on non-overlapping ranges",
			false, false)
INITIALIZE_PASS_END(AllocaMerging, "AllocaMerging", "Merge alloca instructions used on non-overlapping ranges",
			false, false)
INITIALIZE_PASS_BEGIN(AllocaStoresExtractor, "AllocaStoresExtractor", "Removes stores to just allocated memory and keeps track of the values separately",
			false, false)
INITIALIZE_PASS_END(AllocaStoresExtractor, "AllocaStoresExtractor", "Removes stores to just allocated memory and keeps track of the values separately",
			false, false)

