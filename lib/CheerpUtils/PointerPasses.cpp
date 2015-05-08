//===-- PointerPasses.cpp - Cheerp pointer optimization passes --------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2014-2015 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "CheerpPointerPasses"
#include "llvm/ADT/Statistic.h"
#include "llvm/Cheerp/GlobalDepsAnalyzer.h"
#include "llvm/Cheerp/PointerAnalyzer.h"
#include "llvm/Cheerp/PointerPasses.h"
#include "llvm/Cheerp/Registerize.h"
#include "llvm/Cheerp/Utility.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <map>

STATISTIC(NumIndirectFun, "Number of indirect functions processed");
STATISTIC(NumAllocasTransformedToArrays, "Number of allocas of values transformed to allocas of arrays");

namespace llvm {

bool AllocaArrays::replaceAlloca(AllocaInst* ai)
{
	const ConstantInt * ci = dyn_cast<ConstantInt>(ai->getArraySize());
	
	if (!ci)
	{
		// Runtime alloca size, can not do nothing here 
		// TODO maybe we can treat this like a malloc?
		return false;
	}

	llvm::Type * at = llvm::ArrayType::get( ai->getAllocatedType(), ci->getZExtValue() );
	AllocaInst * newAi = new AllocaInst( at );
	newAi->insertAfter( ai );
	ai->removeFromParent();
	newAi->takeName(ai);

	GetElementPtrInst * gepZero = nullptr;
	
	for ( User::use_iterator it = ai->use_begin(); it != ai->use_end(); )
	{
		Use & u = *it++;
		
		if ( BitCastInst * bi = dyn_cast<BitCastInst>(u) )
		{
			CastInst * newBi = BitCastInst::Create( bi->getOpcode(), newAi, bi->getDestTy() );
			ReplaceInstWithInst(bi, newBi);
			
			newBi->takeName( bi );
		}
		else if ( GetElementPtrInst * gep = dyn_cast<GetElementPtrInst>(u) )
		{
			SmallVector< Value *, 8 > vals;
			vals.push_back( ConstantInt::getNullValue( llvm::Type::getInt32Ty( gep->getContext() ) ) );
			
			std::copy(gep->idx_begin(), gep->idx_end(), std::back_inserter(vals) );
			
			GetElementPtrInst * newGep = GetElementPtrInst::Create(newAi, vals);
			ReplaceInstWithInst(gep, newGep);
			newGep->takeName( gep );
		}
		else
		{
			if (! gepZero )
			{
				SmallVector< Value *, 8 > vals ( 2, ConstantInt::getNullValue( llvm::Type::getInt32Ty( u->getContext() ) ) );

				gepZero = GetElementPtrInst::Create(newAi, vals, "");
				gepZero->insertAfter(newAi);
			}
			
			assert ( isa<Instruction>(u) );
			
			u.set( gepZero );
		}
	}
	
	assert( ai->use_empty() );
	delete ai;

	return true;
}

bool AllocaArrays::runOnFunction(Function& F)
{
	bool Changed = false;
	cheerp::PointerAnalyzer & PA = getAnalysis<cheerp::PointerAnalyzer>();
	cheerp::Registerize & registerize = getAnalysis<cheerp::Registerize>();

	for ( BasicBlock & BB : F )
	{
		for ( BasicBlock::iterator it = BB.begin(); it != BB.end(); )
		{
			AllocaInst * ai = dyn_cast<AllocaInst>(it++);
			if (! ai ) continue;

			if (PA.getPointerKind(ai) == cheerp::COMPLETE_OBJECT )
			{
				// No need to optimize if it is already a CO
				continue;
			}

			NumAllocasTransformedToArrays++;

			PA.invalidate(ai);
			// Careful, registerize must be invalidated before changing the function
			registerize.invalidateLiveRangeForAllocas(F);
			Changed |= replaceAlloca( ai );
		}
	}
	
	if (Changed)
		registerize.computeLiveRangeForAllocas(F);
	return Changed;
}

const char* AllocaArrays::getPassName() const
{
	return "AllocaArrays";
}

char AllocaArrays::ID = 0;

void AllocaArrays::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addRequired<cheerp::PointerAnalyzer>();
	AU.addPreserved<cheerp::PointerAnalyzer>();
	AU.addRequired<cheerp::Registerize>();
	AU.addPreserved<cheerp::Registerize>();
	AU.addPreserved<cheerp::GlobalDepsAnalyzer>();
	llvm::Pass::getAnalysisUsage(AU);
}

FunctionPass *createAllocaArraysPass() { return new AllocaArrays(); }


const char* IndirectCallOptimizer::getPassName() const
{
	return "IndirectCallOptimizer";
}

char IndirectCallOptimizer::ID = 0;

bool IndirectCallOptimizer::runOnModule(Module & m)
{
	bool Changed = false;
	cheerp::PointerAnalyzer & PA = getAnalysis<cheerp::PointerAnalyzer>();

	for (Module::iterator it = m.begin();it != m.end(); ++it)
	{
		if ( it->hasAddressTaken() &&
		     !it->empty() &&
		     // Check that at least one argument is a regular pointer
		     std::any_of(it->arg_begin(),
				 it->arg_end(),
				 [&](const Argument & arg)
				 {
				 	return arg.getType()->isPointerTy() && (PA.getPointerKind(&arg) == cheerp::REGULAR);
				 }) &&
		     // Check that this function is called *directly* at least one time.
		     std::any_of(it->use_begin(),
				 it->use_end(),
				 [](const Use & u)
				 {
					 return ImmutableCallSite(u.getUser());
				 }) )
		{
			Function * oldFun = it;
			PA.invalidate(oldFun);
			Function * newFun = Function::Create( oldFun->getFunctionType(),
							      oldFun->getLinkage(),
							      Twine("__cheerpindirect", oldFun->getName() ) );
			
			it = m.getFunctionList().insertAfter( it, newFun);
			
			oldFun->replaceAllUsesWith(newFun);
			assert( oldFun->use_empty() );

			SmallVector< Value *, 8 > newFunArgs;
			newFunArgs.reserve ( newFun->arg_size() );
			for ( Function::arg_iterator arg = newFun->arg_begin(); arg != newFun->arg_end(); ++ arg)
				newFunArgs.push_back(arg);
			
			// Fill the new function
			BasicBlock * newBody = BasicBlock::Create( newFun->getContext(), 
								   "entry",
								   newFun );

			CallInst * fwdCall = CallInst::Create( oldFun,
							      newFunArgs,
							      "",
							      newBody);

			if ( fwdCall->getType()->isVoidTy() )
				ReturnInst::Create( newFun->getContext(), newBody );
			else
				ReturnInst::Create( newFun->getContext(), fwdCall, newBody );
			
			// Restore direct calls uses
			for ( Function::use_iterator ui = newFun->use_begin(); ui != newFun->use_end(); )
			{
				Use & u = *ui++;
				User * U = u.getUser();
				
				ImmutableCallSite cs(U);
				if ( (cs.isCall() || cs.isInvoke()) && cs.isCallee(&u) )
				{
					U->setOperand( u.getOperandNo(), oldFun );
				}
			}
			
			assert ( !oldFun->hasAddressTaken() );
			
			NumIndirectFun++;
			Changed = true;
		}
	}
	
	assert( m.alias_empty() );
	
	return Changed;
}

void IndirectCallOptimizer::getAnalysisUsage(AnalysisUsage& AU) const
{
	AU.addRequired<cheerp::PointerAnalyzer>();
	AU.addPreserved<cheerp::PointerAnalyzer>();
	AU.addPreserved<cheerp::GlobalDepsAnalyzer>();
	AU.addPreserved<cheerp::Registerize>();

	llvm::Pass::getAnalysisUsage(AU);
}

ModulePass* createIndirectCallOptimizerPass()
{
	return new IndirectCallOptimizer();
}

class PHIVisitor
{
public:
	typedef std::map<PHINode*, PHINode*> PHIMap;
	PHIVisitor(PHIMap& phiMap):mappedPHIs(phiMap)
	{
	}
	bool visitPHI(PHINode* phi);
	Value* findBase(Instruction* I);
	Value* rewrite(Instruction* I, Value* base);
private:
	std::set<Value*> visited;
	PHIMap& mappedPHIs;
};

Value* PHIVisitor::findBase(Instruction* I)
{
	if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(I))
	{
		if (gep->getNumIndices() == 1)
		{
			Value* ptr=gep->getPointerOperand();
			if (Instruction* ptrI=dyn_cast<Instruction>(ptr))
			{
				Value* base = findBase(ptrI);
				if(base)
					return base;
				else
					return gep;
			}
			else
				return ptr;
		}
	}
	else if(PHINode* phi = dyn_cast<PHINode>(I))
	{
		if(visited.count(phi))
			return phi;
		Value* ret = NULL;
		// Avoid loops down this exploration paths
		// When the PHI is finished it will be removed from the set
		// To be eventually re-entered later on
		// NOTE: Be careful for PHIs which are not part of the loop to be transformed
		visited.insert(phi);
		for (unsigned i=0;i<phi->getNumIncomingValues();i++)
		{
			Value* incomingValue=phi->getIncomingValue(i);
			Instruction* incomingInst=dyn_cast<Instruction>(incomingValue);
			Value* baseCandidate = incomingInst ? findBase(incomingInst) : incomingValue;
			if(visited.count(baseCandidate))
				continue;
			if (baseCandidate == NULL)
			{
				ret = NULL;
				break;
			}
			if (ret == NULL)
				ret = baseCandidate;
			else if (ret != baseCandidate)
			{
				ret = NULL;
				break;
			}
		}
		visited.erase(phi);
		return ret;
	}
	return I;
}

Value* PHIVisitor::rewrite(Instruction* I, Value* base)
{
	if (I==base)
		return NULL;
	if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(I))
	{
		if (gep->getNumIndices() == 1)
		{
			Value* ptr=gep->getPointerOperand();
			Instruction* ptrI=dyn_cast<Instruction>(ptr);
			Value* parentOffset = ptrI ? rewrite(ptrI, base) : NULL;
			Value* thisOffset = *gep->idx_begin();
			if (parentOffset == NULL)
				return thisOffset;
			else
			{
				Value* newIndex=BinaryOperator::Create(BinaryOperator::Add, parentOffset, thisOffset, "geptoindex", gep);
				Value* newGep=GetElementPtrInst::Create(base, newIndex, "geptoindex", gep);
				gep->replaceAllUsesWith(newGep);
				return newIndex;
			}
		}
	}
	else if(PHINode* phi = dyn_cast<PHINode>(I))
	{
		auto it = mappedPHIs.find(phi);
		if (it!=mappedPHIs.end())
			return it->second;
		PHINode* newPHI = PHINode::Create(IntegerType::get(phi->getContext(), 32), phi->getNumIncomingValues(), "geptoindexphi", phi);
		mappedPHIs.insert(std::make_pair(phi, newPHI));
		for (unsigned i=0;i<phi->getNumIncomingValues();i++)
		{
			Value* incomingValue=phi->getIncomingValue(i);
			Instruction* incomingInst=dyn_cast<Instruction>(incomingValue);
			Value* index = incomingInst ? rewrite(incomingInst, base) : NULL;
			if (index == NULL)
				index = ConstantInt::get(newPHI->getType(), 0);
			newPHI->addIncoming(index, phi->getIncomingBlock(i));
		}
		Value* newGep=GetElementPtrInst::Create(base, newPHI, "geptoindex",phi->getParent()->getFirstInsertionPt());
		phi->replaceAllUsesWith(newGep);
		return newPHI;
	}
	return NULL;
}

bool PHIVisitor::visitPHI(PHINode* phi)
{
	Value* base = findBase(phi);
	if (base == NULL)
		return false;
	// We have found a common base for all incoming values.
	// Now we want to build an integer PHI
	rewrite(phi, base);
	return true;
}

bool PointerArithmeticToArrayIndexing::runOnFunction(Function& F)
{
	bool Changed = false;

	PHIVisitor::PHIMap phiMap;
	for ( BasicBlock & BB : F )
	{
		for ( BasicBlock::iterator it = BB.begin(); it != BB.end(); )
		{
			PHINode * phi = dyn_cast<PHINode>(it++);
			if (! phi )
				continue;
			if (! phi->getType()->isPointerTy() )
				continue;
			Changed |= PHIVisitor(phiMap).visitPHI(phi);
		}
	}
	for(auto& it: phiMap)
		it.first->eraseFromParent();
	return Changed;
}

const char* PointerArithmeticToArrayIndexing::getPassName() const
{
	return "PointerArithmeticToArrayIndexing";
}

char PointerArithmeticToArrayIndexing::ID = 0;

void PointerArithmeticToArrayIndexing::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addPreserved<cheerp::GlobalDepsAnalyzer>();
	llvm::Pass::getAnalysisUsage(AU);
}

FunctionPass *createPointerArithmeticToArrayIndexingPass() { return new PointerArithmeticToArrayIndexing(); }

void PointerToImmutablePHIRemoval::hoistBlock(BasicBlock* targetBlock)
{
	SmallVector<BasicBlock*, 4> predBlocks(pred_begin(targetBlock), pred_end(targetBlock));;
	for(BasicBlock* curBlock: predBlocks)
	{
		ValueToValueMapTy valueMap;
		BasicBlock* newBlock = CloneBasicBlock(targetBlock, valueMap, "phirem", targetBlock->getParent());
		// Fix the copied block
		for(Instruction& I: *targetBlock)
		{
			Instruction* mappedI = cast<Instruction>(valueMap[&I]);
			PHINode* phi = dyn_cast<PHINode>(&I);
			if(phi)
			{
				// Override the map
				valueMap[phi] = phi->getIncomingValueForBlock(curBlock);
				mappedI->eraseFromParent();
				continue;
			}
			for(uint32_t i=0;i<I.getNumOperands();i++)
			{
				Value* oldOp = mappedI->getOperand(i);
				if(valueMap[oldOp])
					mappedI->setOperand(i, valueMap[oldOp]);
			}
		}
		// Update the terminator to go to the new block
		TerminatorInst* curTerm = curBlock->getTerminator();
		for(uint32_t j = 0; j < curTerm->getNumSuccessors(); j++)
		{
			if (curTerm->getSuccessor(j) == targetBlock)
				curTerm->setSuccessor(j, newBlock);
		}
	}
	targetBlock->eraseFromParent();
}

bool PointerToImmutablePHIRemoval::runOnFunction(Function& F)
{
	bool Changed = false;

	SmallVector<BasicBlock*, 4> blocks;
	for ( BasicBlock& BB : F )
		blocks.push_back(&BB);
	for ( BasicBlock* BB : blocks )
	{
		for ( BasicBlock::iterator it = BB->begin(); it != BB->end(); )
		{
			PHINode * phi = dyn_cast<PHINode>(it++);
			if (! phi )
				continue;
			Type* phiType = phi->getType();
			if (! phiType->isPointerTy() )
				continue;
			if (! cheerp::TypeSupport::isImmutableType(phiType->getPointerElementType()) )
				continue;
			BasicBlock* parentBlock = phi->getParent();
			if ( parentBlock->getTerminator()->getNumSuccessors() != 0 )
				continue;
			if ( parentBlock->size() > 5 )
				continue;
			hoistBlock(parentBlock);
			Changed = true;
			break;
		}
	}
	return Changed;
}

const char* PointerToImmutablePHIRemoval::getPassName() const
{
	return "PointerToImmutablePHIRemoval";
}

char PointerToImmutablePHIRemoval::ID = 0;

void PointerToImmutablePHIRemoval::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addPreserved<cheerp::GlobalDepsAnalyzer>();
	llvm::Pass::getAnalysisUsage(AU);
}

FunctionPass *createPointerToImmutablePHIRemovalPass() { return new PointerToImmutablePHIRemoval(); }

void FreeAndDeleteRemoval::deleteInstructionAndUnusedOperands(Instruction* I)
{
	SmallVector<Instruction*, 4> operandsToErase;
	for(Value* op: I->operands())
	{
		if(Instruction* opI = dyn_cast<Instruction>(op))
		{
			if(opI->hasOneUse())
				operandsToErase.push_back(opI);
		}
	}
	I->eraseFromParent();
	for(Instruction* I: operandsToErase)
		deleteInstructionAndUnusedOperands(I);
}

bool FreeAndDeleteRemoval::runOnFunction(Function& F)
{
	bool Changed = false;

	for ( BasicBlock& BB : F )
	{
		for ( BasicBlock::iterator it = BB.begin(); it != BB.end(); )
		{
			CallInst * call = dyn_cast<CallInst>(it++);
			if (!call)
				continue;
			Function* F = call->getCalledFunction();
			if(!F)
				continue;
			if(F->getIntrinsicID()==Intrinsic::cheerp_deallocate ||
				F->getName()=="free")
			{
				deleteInstructionAndUnusedOperands(call);
				Changed = true;
			}
		}
	}
	return Changed;
}

const char* FreeAndDeleteRemoval::getPassName() const
{
	return "FreeAndDeleteRemoval";
}

char FreeAndDeleteRemoval::ID = 0;

void FreeAndDeleteRemoval::getAnalysisUsage(AnalysisUsage & AU) const
{
	llvm::Pass::getAnalysisUsage(AU);
}

FunctionPass *createFreeAndDeleteRemovalPass() { return new FreeAndDeleteRemoval(); }

void GEPOptimizer::optimizeGEPsRecursive(OrderedGEPs::iterator begin, OrderedGEPs::iterator end, Value* base, uint32_t startIndex)
{
	std::set<Instruction*> erasedInst;
	assert(begin != end);
	// We know that up to startIndex all indexes are equal
	// Find out how many indexes are equal in all the range and build a GEP with them from the base
	llvm::SmallVector<llvm::Value*, 4> newIndexes;
	uint32_t endIndex = startIndex;
	if(endIndex == 1)
	{
		// It means that we are handling the first index, add it as it is
		// The first index is guaranteed to be the same across the range
		newIndexes.push_back((*begin)->getOperand(1));
		endIndex++;
	}
	else
	{
		// This is an optimized GEP, it will start from the passed base. Add a constant 0.
		newIndexes.push_back(ConstantInt::get(llvm::Type::getInt32Ty(base->getContext()), 0));
	}
	bool indexesAreEqual = true;
	while(indexesAreEqual)
	{
		Value* curOperand = NULL;
		uint32_t rangeSize = 0;
		for(OrderedGEPs::iterator it=begin;;++it)
		{
			if(it!=end)
			{
				if(rangeSize == 0)
				{
					if(endIndex < (*it)->getNumOperands())
						curOperand = (*it)->getOperand(endIndex);
					rangeSize++;
					continue;
				}
				if(endIndex < (*it)->getNumOperands())
				{
					if(curOperand == (*it)->getOperand(endIndex))
					{
						rangeSize++;
						continue;
					}
				}
			}
			// This is the first index which is different in the range.
			indexesAreEqual = false;
//llvm::errs() << "INDEX EQUAL FROM " << startIndex << " TO " << endIndex << " RANGE " << rangeSize << "\n";
//llvm::errs() << "RANGE " << **begin << " TO " << **it << "\n";
			if(rangeSize == 1)
			{
				// If the range has size 1 and we have just started we skip this GEP entirely
 				if(startIndex != 1)
				{
					uint32_t oldIndexCount = newIndexes.size();
					// Create a GEP from the base to all not used yet indexes
					for(uint32_t i=endIndex;i<(*begin)->getNumOperands();i++)
						newIndexes.push_back((*begin)->getOperand(i));
//llvm::errs() << "BASE " << *base << "INDEX COUNT " << newIndexes.size() << " BEGIN " << **begin << "\n";
					assert(!erasedInst.count(*begin));
					Instruction* newGEP = GetElementPtrInst::Create(base, newIndexes, "", *begin);
					newGEP->takeName(*begin);
					(*begin)->replaceAllUsesWith(newGEP);
					erasedInst.insert(*begin);
					(*begin)->eraseFromParent();
//llvm::errs() << "NEW GEP2 " << *newGEP << "\n";
					newIndexes.resize(oldIndexCount);
				}
				if(it==end)
					break;
				begin = it;
				if(endIndex < (*it)->getNumOperands())
					curOperand = (*it)->getOperand(endIndex);
				else
					curOperand = NULL;
				continue;
			}
			newIndexes.push_back(curOperand);
			// This is the first index which is different in the range. Create a GEP now.
			Instruction* newGEP = GetElementPtrInst::Create(base, newIndexes, "optgep");
			newIndexes.pop_back();
			Instruction* insertionPoint = NULL;
			// Compute the insertion point to dominate all users of this GEP in the range
			for(OrderedGEPs::iterator rangeIt = begin; rangeIt != it; ++rangeIt)
			{
				if(insertionPoint==NULL)
				{
					insertionPoint = *rangeIt;
					continue;
				}
				// Check if the current GEP dominates the old insertionPoint
				if(DT->dominates(*rangeIt, insertionPoint))
					insertionPoint = *rangeIt;
				else if(!DT->dominates(insertionPoint, *rangeIt))
				{
					// If the insertionPoint also does not dominate the current GEP
					// we need to find a common dominator for both
					BasicBlock* commonDominator = DT->findNearestCommonDominator(insertionPoint->getParent(), (*rangeIt)->getParent());
					assert(commonDominator);
					insertionPoint = commonDominator->getTerminator();
				}
			}
			assert(insertionPoint);
			newGEP->insertBefore(insertionPoint);
//llvm::errs() << "NEW GEP " << *newGEP << " AFTER " << *insertPoint << "\n";
			if(rangeSize != 1)
			{
//llvm::errs() << "REC FROM " << **begin << " TO " << **it << "\n";
				// Proceed with the range from 'begin' to 'it' 
				optimizeGEPsRecursive(begin, it, newGEP, endIndex+1);
			}
			if(it==end)
				break;
			// Reset the state for the next range
			begin = it;
			curOperand = (*it)->getOperand(endIndex);
			rangeSize = 1;
		}
		newIndexes.push_back(curOperand);
		endIndex++;
	}
}

bool GEPOptimizer::runOnFunction(Function& F)
{
	bool Changed = false;
	DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();

	OrderedGEPs gepsFromBasePointer;

	// Gather all the GEPs
	for ( BasicBlock& BB : F )
	{
		for ( Instruction& I: BB )
		{
			if(!isa<GetElementPtrInst>(I))
				continue;
			if(I.getNumOperands() <= 2)
				continue;
			gepsFromBasePointer.insert(&I);
		}
	}

	// Look for GEPs that have a common base pointer. They should have both the pointer the the first index equal
	// As the GEPs in the map are ordered we know that equal objects are close togheter
	uint32_t rangeLength = 0;
	OrderedGEPs::iterator rangeStart;
	for(auto it=gepsFromBasePointer.begin();;++it)
	{
		if(it!=gepsFromBasePointer.end())
		{
			assert((*it)->getNumOperands() > 2);
			// Check if we need to start a range
			if(rangeLength == 0)
			{
				rangeStart = it;
				rangeLength++;
				continue;
			}
			// Check that the first two operands are the same
			if((*rangeStart)->getOperand(0) == (*it)->getOperand(0) && (*rangeStart)->getOperand(1) == (*it)->getOperand(1))
			{
				rangeLength++;
				continue;
			}
		}

		// End the range here, if the range is longer than 1 we can optimize some GEPs
		if(rangeLength > 1)
		{
			// TODO: Optimize GEPs
//llvm::errs() << "COMMON GEP RANGE " << rangeLength << "\n";
			for(auto it2=rangeStart;it2!=it;++it2)
			{
//llvm::errs() << **it2 << "\n";
			}
			optimizeGEPsRecursive(rangeStart, it, (*rangeStart)->getOperand(0), 1);
		}
		rangeLength = 0;
		if(it==gepsFromBasePointer.end())
			break;
	}
//F.dump();
	//TODO: Last range
	return Changed;
}

const char* GEPOptimizer::getPassName() const
{
	return "GEPOptimizer";
}

char GEPOptimizer::ID = 0;

void GEPOptimizer::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addRequired<DominatorTreeWrapperPass>();
	llvm::Pass::getAnalysisUsage(AU);
}

FunctionPass *createGEPOptimizerPass() { return new GEPOptimizer(); }

}

using namespace llvm;

INITIALIZE_PASS_BEGIN(AllocaArrays, "AllocaArrays", "Transform allocas of REGULAR type to arrays of 1 element",
			false, false)
INITIALIZE_PASS_END(AllocaArrays, "AllocaArrays", "Transform allocas of REGULAR type to arrays of 1 element",
			false, false)
INITIALIZE_PASS_BEGIN(GEPOptimizer, "GEPOptimizer", "Rewrite GEPs in a function to remove redundant object accesses",
			false, false)
INITIALIZE_PASS_DEPENDENCY(DominatorTreeWrapperPass)
INITIALIZE_PASS_END(GEPOptimizer, "GEPOptimizer", "Rewrite GEPs in a function to remove redundant object accesses",
			false, false)
