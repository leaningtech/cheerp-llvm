//===-- PointerPasses.cpp - Cheerp pointer optimization passes --------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2014 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "CheerpPointerPasses"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Cheerp/GlobalDepsAnalyzer.h"
#include "llvm/Cheerp/PointerAnalyzer.h"
#include "llvm/Cheerp/PointerPasses.h"
#include "llvm/Cheerp/Registerize.h"
#include "llvm/Cheerp/Utility.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <set>
#include <map>

STATISTIC(NumIndirectFun, "Number of indirect functions processed");
STATISTIC(NumAllocasTransformedToArrays, "Number of allocas of values transformed to allocas of arrays");

namespace llvm {

bool AllocaArrays::replaceAlloca(AllocaInst* ai)
{
	const ConstantInt * ci = dyn_cast<ConstantInt>(ai->getArraySize());
	
	// Runtime alloca size, convert it to cheerp_allocate 
	if (!ci)
	{
		Module* M = ai->getParent()->getParent()->getParent();
		DataLayout targetData(M);
		Type* int32Ty = IntegerType::getInt32Ty(M->getContext());
		Function* cheerp_allocate = Intrinsic::getDeclaration(M, Intrinsic::cheerp_allocate, ai->getType());

		IRBuilder<> Builder(ai);

		Type* allocTy = ai->getAllocatedType();
		uint32_t elemSize = targetData.getTypeAllocSize(allocTy);
		Value* size = Builder.CreateMul(ai->getArraySize(), ConstantInt::get(int32Ty, elemSize, false)); 
		Instruction* alloc = CallInst::Create(cheerp_allocate, size);
		BasicBlock::iterator ii(ai);
		ReplaceInstWithInst(ai->getParent()->getInstList(), ii, alloc);
		return true;
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
			PA.invalidate(newFun);
			
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
	typedef std::map<PHINode*, Value*> PHIMap;
	typedef std::set<Instruction*> RemoveQueue;
	PHIVisitor(PHIMap& phiMap, RemoveQueue& r):mappedPHIs(phiMap),toRemove(r)
	{
	}
	bool visitPHI(PHINode* phi);
	Value* findBase(Instruction* I);
	Value* rewrite(Instruction* I, Value* base);
private:
	std::set<Value*> visited;
	PHIMap& mappedPHIs;
	RemoveQueue& toRemove;
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
				if(!gep->use_empty())
				{
					Value* newGep=GetElementPtrInst::Create(base, newIndex, "geptoindex", gep);
					gep->replaceAllUsesWith(newGep);
				}
				toRemove.insert(gep);
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
			// If incomingValue is not an instruction it must be a global pointer and the base
			Value* incomingValue=phi->getIncomingValue(i);
			phi->setIncomingValue(i, UndefValue::get(phi->getType()));
			Instruction* incomingInst=dyn_cast<Instruction>(incomingValue);
			Value* index = incomingInst ? rewrite(incomingInst, base) : NULL;
			if (index == NULL)
				index = ConstantInt::get(newPHI->getType(), 0);
			newPHI->addIncoming(index, phi->getIncomingBlock(i));
		}
		Value* newOffset = newPHI;
		if(Value* n=SimplifyInstruction(newPHI))
		{
			newOffset = n;
			newPHI->replaceAllUsesWith(n);
			newPHI->eraseFromParent();
		}
		Value* newGep = NULL;
		if(isa<ConstantInt>(newOffset) && cast<ConstantInt>(newOffset)->getZExtValue()==0)
			newGep=base;
		else
			newGep=GetElementPtrInst::Create(base, newOffset, "geptoindex",phi->getParent()->getFirstInsertionPt());
		phi->replaceAllUsesWith(newGep);
		return newOffset;
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
	if (F.getSection() == StringRef("asmjs"))
		return false;

	PHIVisitor::PHIMap phiMap;
	PHIVisitor::RemoveQueue toRemove;
	for ( BasicBlock & BB : F )
	{
		for ( BasicBlock::iterator it = BB.begin(); it != BB.end(); )
		{
			PHINode * phi = dyn_cast<PHINode>(it++);
			if (! phi )
				continue;
			if (! phi->getType()->isPointerTy() )
				continue;
			assert ( phi->getNumIncomingValues() != 0 );
			// LCSSA may create PHIs with just 1 value or all equal values, kill those
			Value* uniqueVal = phi->getIncomingValue(0);
			for ( unsigned i = 1; i < phi->getNumIncomingValues(); i++)
			{
				// PHIs with as single elements are confusing for the backend, remove them
				Value* newVal = phi->getIncomingValue(i);
				if(newVal == uniqueVal)
					continue;
				uniqueVal = NULL;
				break;
			}
			if(uniqueVal)
			{
				phi->replaceAllUsesWith(uniqueVal);
				phiMap.insert(std::make_pair(phi, uniqueVal));
				Changed |= true;
				continue;
			}
			Changed |= PHIVisitor(phiMap, toRemove).visitPHI(phi);
		}
	}
	for(auto& it: phiMap)
		it.first->eraseFromParent();
	for(Instruction* I: toRemove)
		I->eraseFromParent();
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
	std::unordered_set<BasicBlock*> predBlocks(pred_begin(targetBlock), pred_end(targetBlock));;
	std::map<llvm::Instruction*, llvm::SmallVector<llvm::PHINode*, 4>> newPHIMap;
	
	for(Instruction& I: *targetBlock)
	{
		// If the instruction is used in another block we need to create a PHI for it in every successor
		llvm::SmallVector<Instruction*, 4> outOfBlockUsers;
		for(Use& U: I.uses())
		{
			Instruction* user = cast<Instruction>(U.getUser());
			if(user->getParent() == targetBlock)
				continue;
			outOfBlockUsers.push_back(user);
		}
		for(Instruction* user: outOfBlockUsers)
		{
//llvm::errs() << "OUTOFBLOCK " << *user << "\n";
			// Figure out the right block in which to insert this PHI
			BasicBlock* bestDominator = nullptr;
			TerminatorInst* targetTerm = targetBlock->getTerminator();
			for(uint32_t j = 0; j < targetTerm->getNumSuccessors(); j++)
			{
				BasicBlock* succ = targetTerm->getSuccessor(j);
				if(succ == user->getParent())
				{
					bestDominator = succ;
					break;
				}
/*	succ->getParent()->dump();
llvm::errs() << "SUCC " << *succ << "\n";
llvm::errs() << "PARENT " << *user->getParent() << "\n";
				if(DT->dominates(succ, user->getParent()))
				{
llvm::errs() << "DOMINATED FROM " << *succ << "\n";
					if(!bestDominator || DT->dominates(succ, bestDominator))
						bestDominator = succ;
				}*/
			}
			if(PHINode* phi = dyn_cast<PHINode>(user))
			{
//llvm::errs() << "PHI " << *phi << " NUMOP " << phi->getNumOperands() << "\n";
				for(uint32_t i=0;i<phi->getNumOperands();i++)
				{
					Value* op = phi->getOperand(i);
					if(op != &I)
						continue;
					BasicBlock* incomingBlock = phi->getIncomingBlock(i);
					//llvm::errs() << "OP " << *op << "\n";
					//llvm::errs() << "BLOCK " << *incomingBlock << "\n";
					bool isSuccessor = incomingBlock == targetBlock;
					if(!isSuccessor)
					{
						bestDominator = nullptr;
					}
				}
			}
			if(!bestDominator)
			{
//			llvm::errs() << "BAILOUT\n";	
				for(auto& it1: newPHIMap)
				{
					for(auto it2: it1.second)
					{
						it2->replaceAllUsesWith(it1.first);
						if(it2->getParent())
							it2->eraseFromParent();
						else
							delete it2;
					}
				}
				return;
			}
			// If the user is already a PHI use it again
			if(!isa<PHINode>(user))
			{
//				llvm::errs() << "NEW PHI FOR " << I << "\n";
				llvm::PHINode* newPHI  = PHINode::Create(I.getType(), predBlocks.size(), "newphiforphiremoval");
				newPHIMap[&I].push_back(newPHI);
				assert(bestDominator);
				newPHI->insertBefore(bestDominator->begin());
				user->replaceUsesOfWith(&I, newPHI);
			}
		}
	}
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
			}
			if(newPHIMap.count(&I))
			{
				for(llvm::PHINode* newPHI: newPHIMap[&I])
				{
					assert(valueMap.count(&I));
					newPHI->addIncoming(valueMap[&I], newBlock);
//					llvm::errs() << "ADD INCOMING TO " << *newPHI << "\n";
				}
			}
			if(phi)
				continue;
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
		TerminatorInst* targetTerm = targetBlock->getTerminator();
		for(uint32_t j = 0; j < targetTerm->getNumSuccessors(); j++)
		{
			BasicBlock* succ = targetTerm->getSuccessor(j);
			for(Instruction& I: *succ)
			{
				// Iterate over PHIs and fix them
				PHINode* phi = dyn_cast<PHINode>(&I);
				if(!phi)
					break;
				// PHIs without targetBlock have been inserted above
				if(phi->getBasicBlockIndex(targetBlock)<0)
					continue;
				llvm::Value* oldIncoming = phi->getIncomingValueForBlock(targetBlock);
				if(Instruction* oldIncomingInst = dyn_cast<Instruction>(oldIncoming))
				{
					if(oldIncomingInst->getParent() != targetBlock)
						continue;
//llvm::errs() << " PHI " << *phi << "\n";
//llvm::errs() << "INST " << *oldIncomingInst << "\n";
					assert(valueMap.count(oldIncomingInst));
					oldIncoming = valueMap[oldIncomingInst];
				}
				assert(oldIncoming);
				phi->addIncoming(oldIncoming, newBlock);
			}
		}
	}
	TerminatorInst* targetTerm = targetBlock->getTerminator();
	for(uint32_t j = 0; j < targetTerm->getNumSuccessors(); j++)
	{
		BasicBlock* succ = targetTerm->getSuccessor(j);
		for(Instruction& I: *succ)
		{
			// Iterate over PHIs and fix them
			PHINode* phi = dyn_cast<PHINode>(&I);
			if(!phi)
				break;
			// PHIs without targetBlock have been inserted above
			if(phi->getBasicBlockIndex(targetBlock)<0)
				continue;
			phi->removeIncomingValue(targetBlock);
		}
	}
	for(uint32_t j = 0; j < targetTerm->getNumSuccessors(); j++)
	{
		BasicBlock* succ = targetTerm->getSuccessor(j);
	/*	for(auto& it: newPHIMap)
		{
			PHINode* newPHI = cast<PHINode>(it.second->clone());
			newPHI->insertBefore(succ->begin());
		}*/
//		llvm::errs() << "FIXED BLOCK " << *succ << "\n";
	}
	for(Instruction& I: *targetBlock)
	{
		for(Use& U: I.uses())
		{
			Instruction* user = cast<Instruction>(U.getUser());
			if(user->getParent() == targetBlock)
				continue;
//			llvm::errs() << "BAD USE " << *user <<  " FOR " << I << "\n";
		}
	}
	targetBlock->eraseFromParent();
}

struct SwitchPHIInst
{
	llvm::Instruction* inst;
	std::map<Instruction*, PHINode*> operandsMap;
};

struct SwitchPHIData
{
	std::map<llvm::Instruction*, uint32_t> instMap;
	std::vector<SwitchPHIInst> instData;
	std::vector<PHINode*> phis;
};

bool PointerToImmutablePHIRemoval::mayConvertPHIToSwitch(SwitchPHIData& data, PHINode* phi, uint32_t depth)
{
//llvm::errs() << "CONVERT " << *phi << "\n";
	if(data.instMap.count(phi))
	{
//llvm::errs() << "LOOP " << *phi << "\n";
		return data.instMap[phi] != 0;
	}
	if(depth > 1)
{
//llvm::errs() << "DEPTH\n";
		return false;
}
	data.instMap.insert(std::make_pair(phi, 0));
	uint32_t mapSize = data.instMap.size();
	data.instData.push_back(SwitchPHIInst{phi});
	// Check if the incoming values are supported
	for(Value* op: phi->operands())
	{
		// Check that all ops do not have side effects (calls cannot be delayed)
		Instruction* opI = dyn_cast<Instruction>(op);
		// Constants and arguments are always ok
		if(!opI)
			continue;
		// GEP is ok
		if(opI->getOpcode() == Instruction::GetElementPtr && opI->getNumOperands()>2)
			continue;
		// Alloca is ok if it's in the entry block
		if(opI->getOpcode() == Instruction::Alloca && opI->getParent() == &phi->getParent()->getParent()->getEntryBlock())
			continue;
		if(opI->getOpcode() == Instruction::PHI && mayConvertPHIToSwitch(data, cast<PHINode>(opI), depth+1))
			continue;
//llvm::errs() << "RETURN FALSE ON " << *op << "\n";
		return false;
	}
	// Mark this PHI itself as being convertable
	data.instMap[phi] = mapSize;
	data.phis.push_back(phi);
	// If there is any PHI user make sure that is also convertable
	for(User* U: phi->users())
	{
		if(!isa<LoadInst>(U) && !isa<StoreInst>(U) && !isa<PHINode>(U))
{
//llvm::errs() << "RETURN1 FALSE ON " << *U << "\n";
			return false;
}
		PHINode* userPhi = dyn_cast<PHINode>(U);
		if(!userPhi)
			continue;
		if(!mayConvertPHIToSwitch(data, userPhi, depth+1))
{
//llvm::errs() << "RETURN1 FALSE ON " << *U << "\n";
			return false;
}
	}
	// Assign an index to every incoming value, but PHIs
	for(Value* op: phi->operands())
	{
		Instruction* opI = dyn_cast<Instruction>(op);
		// Constants and arguments are always ok
		if(!opI)
			continue;
		if(opI->getOpcode() == Instruction::PHI)
		{
			if(!data.instMap.count(opI))
{
//llvm::errs() << "RETURN3 FALSE ON " << *opI << "\n";
				return false;
}
			continue;
		}
		if(data.instMap.count(opI))
			continue;
		data.instMap.insert(std::make_pair(opI, data.instData.size()+1));
		//llvm::errs() << data.instMap[opI] << "-1==" << data.instData.size() << "\n";
		assert(data.instMap[opI]-1==data.instData.size());
		data.instData.push_back(SwitchPHIInst{opI});
	}
//	llvm::errs() << "CAN CONVERT " << *phi << "\n";
	return true;
}

void PointerToImmutablePHIRemoval::convertPHIToSwitch(SwitchPHIData& data)
{
//llvm::errs() << "ACTUALLY CONVERT\n";
	DominatorTree* DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
	struct ReplacedPHIData
	{
		PHINode* indexPHI;
		SmallVector<Instruction*, 4> operandsPHIs;
	};
	std::map<PHINode*, ReplacedPHIData> phiNodesMap;
	for(PHINode* phi: data.phis)
	{
		std::map<Instruction*, PHINode*> localOperandsOverride;
		// For each incoming value check if we need to build a PHI for the operands
		SmallVector<BasicBlock*, 4> predBlocks(pred_begin(phi->getParent()), pred_end(phi->getParent()));;
		// Build an int32 PHI that represent the chosen incoming value
		llvm::PHINode* newPHIIndex = PHINode::Create(llvm::Type::getInt32Ty(phi->getContext()), predBlocks.size(), "newphiforphiindex", phi);
		auto& newOperandsPHIs = phiNodesMap.insert(std::make_pair(phi, ReplacedPHIData{newPHIIndex})).first->second.operandsPHIs;
		for(uint32_t i=0;i<phi->getNumOperands();i++)
		{
			Value* incoming = phi->getOperand(i);
			BasicBlock* incomingBlock = phi->getIncomingBlock(i);
			Instruction* incomingI = dyn_cast<Instruction>(incoming);
			if(!incomingI)
			{
				newPHIIndex->addIncoming(UndefValue::get(newPHIIndex->getType()), incomingBlock);
				continue;
			}
			// If the instruction dominates the block we can use it directly, without any additional PHIs
			if(DT->dominates(incomingI, phi->getParent()))
			{
				newOperandsPHIs.push_back(incomingI);
				assert(data.instMap.count(incomingI));
				uint32_t incomingIndex = data.instMap[incomingI] - 1;
				newPHIIndex->addIncoming(ConstantInt::get(newPHIIndex->getType(), incomingIndex), incomingBlock);
				continue;
			}
			if(PHINode* incomingPHI = dyn_cast<PHINode>(incomingI))
			{
//llvm::errs() << "INDIRECT PHI " << *incomingPHI << "\n";
				// Propagate its index
				assert(phiNodesMap.count(incomingPHI));
				auto& replacePHIData = phiNodesMap[incomingPHI];
				newPHIIndex->addIncoming(replacePHIData.indexPHI, incomingBlock);
				// We need to add PHIs for the operands that the the values coming from this PHI may use
				for(Instruction* operandToReplace: replacePHIData.operandsPHIs)
				{
					if(DT->dominates(operandToReplace, phi->getParent()))
						continue;
					llvm::PHINode* newPHI  = PHINode::Create(operandToReplace->getType(), predBlocks.size(), "newphiforindirectphi", phi);
					BasicBlock* curBlock = phi->getIncomingBlock(i);
					for(BasicBlock* predBlock: predBlocks)
					{
						llvm::Value* newIncoming = predBlock == curBlock ? (Value*)operandToReplace : (Value*)UndefValue::get(operandToReplace->getType());
						newPHI->addIncoming(newIncoming, predBlock);
					}
					localOperandsOverride.insert(std::make_pair(operandToReplace, newPHI));
				}
				continue;
			}
//			llvm::errs() << "NEED OP PHIS " << *incomingI << "\n";
			assert(data.instMap.count(incomingI));
			uint32_t incomingIndex = data.instMap[incomingI] - 1;
			newPHIIndex->addIncoming(ConstantInt::get(newPHIIndex->getType(), incomingIndex), incomingBlock);
			assert(incomingIndex < data.instData.size());
			SwitchPHIInst& phiInst = data.instData[incomingIndex];
			// We need to build a PHI for every operand of this operand
			for(Value* op: incomingI->operands())
			{
				Instruction* opI = dyn_cast<Instruction>(op);
				if(!opI)
					continue;
				llvm::PHINode* newPHI  = PHINode::Create(opI->getType(), predBlocks.size(), "newphiforphiremoval", phi);
//llvm::errs() << "ADDING PHI TO INDIRECT LIST " << *newPHI << "\n";
				newOperandsPHIs.push_back(newPHI);
				// This PHI is only used for this specific operand of the incoming value
				BasicBlock* curBlock = phi->getIncomingBlock(i);
				for(BasicBlock* predBlock: predBlocks)
				{
					llvm::Value* newIncoming = predBlock == curBlock ? (Value*)opI : (Value*)UndefValue::get(opI->getType());
					newPHI->addIncoming(newIncoming, predBlock);
				}
				phiInst.operandsMap.insert(std::make_pair(opI,newPHI));
			}
		}
		SmallVector<Instruction*, 4> toDelete;
		for(User* U: phi->users())
		{
			if(isa<PHINode>(U))
				continue;
//			llvm::errs() << "CONVERT USER " << *U << "\n";
			Instruction* I = cast<Instruction>(U);
			// We need to make a switch for the various cases, start by splitting the block
			BasicBlock* parentBlock = I->getParent();
			BasicBlock* tailBlock = parentBlock->splitBasicBlock(I, "phiremovalswitchtail");
			PHINode* userPHI = nullptr;
			if(!I->getType()->isVoidTy() && !I->use_empty())
				userPHI = PHINode::Create(I->getType(), 3, "userphiforremoval", I);
			// Build all the necessary blocks
			// TODO: We should only use the indexes which can come from this PHI!
			SmallVector<BasicBlock*, 4> switchBlocks;
			// Build a new switch case
			SwitchInst* sw = SwitchInst::Create(newPHIIndex, tailBlock, 0);
			for(uint32_t i=0;i<data.instData.size();i++)
			{
				SwitchPHIInst& phiInst = data.instData[i];
				if(isa<PHINode>(phiInst.inst))
					continue;
//llvm::errs() << "NEED A BLOCK FOR " << *phiInst.inst << "\n";
				BasicBlock* newBlock = BasicBlock::Create(parentBlock->getContext(), "phiremovalswitch", parentBlock->getParent());
				// Create a new instruction like the incoming one with replaced operands
				Instruction* newIncomingInst = nullptr;
				if(phiInst.operandsMap.empty())
					newIncomingInst = phiInst.inst;
				else
				{
					newIncomingInst = phiInst.inst->clone();
					newBlock->getInstList().push_back(newIncomingInst);
					for(auto& it: phiInst.operandsMap)
					{
						if(localOperandsOverride.count(it.second))
							newIncomingInst->replaceUsesOfWith(it.first,localOperandsOverride[it.second]);
						else
							newIncomingInst->replaceUsesOfWith(it.first,it.second);
					}
				}
				// Copy the user and replace the operand
				Instruction* newUser = I->clone();
				newBlock->getInstList().push_back(newUser);
				newUser->replaceUsesOfWith(phi, newIncomingInst);
				BranchInst::Create(tailBlock, newBlock);
				sw->addCase(cast<ConstantInt>(ConstantInt::get(newPHIIndex->getType(), i)), newBlock);
				if(userPHI)
					userPHI->addIncoming(newUser, newBlock);
			}
			// TODO: Replace default dest
			if(userPHI)
			{
				userPHI->addIncoming(UndefValue::get(userPHI->getType()), parentBlock);
				I->replaceAllUsesWith(userPHI);
			}
			TerminatorInst* oldTerminator = parentBlock->getTerminator();
			oldTerminator->eraseFromParent();
			parentBlock->getInstList().push_back(sw);
			toDelete.push_back(I);
		}
		for(Instruction* I: toDelete)
		{
			I->eraseFromParent();
		}
	}
	for(PHINode* phi: data.phis)
	{
		phi->replaceAllUsesWith(UndefValue::get(phi->getType()));
		phi->eraseFromParent();
//llvm::errs() << "RESIDUAL USES FOR " << *phi << " " << phi->getNumUses() << "\n";
	}
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
			BasicBlock* parentBlock = phi->getParent();
			if ( parentBlock->getTerminator()->getNumSuccessors() == 0 &&  parentBlock->size() <= 5)
				hoistBlock(parentBlock);
			else
			{
				SwitchPHIData data;
				bool mayConvert = mayConvertPHIToSwitch(data, phi, 0);
				if(mayConvert && F.getName() != "Render_Single_Pass" && F.getName() != "Draw_Sweep")
{
//llvm::errs() << "BEFORE CONVERT " << F << "\n";
					convertPHIToSwitch(data);
}
			}
			Changed = true;
			break;
		}
	}
	if(Changed)
	{
//llvm::errs() << "AFTER HOISTING\n";
		F.dump();
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
	AU.addRequired<DominatorTreeWrapperPass>();
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

	if (F.getSection()==StringRef("asmjs"))
		return false;

	bool isAllGenericJS = true;
	for (const Function& f: *F.getParent())
	{
		if (f.getSection() == StringRef("asmjs"))
		{
			isAllGenericJS = false;
			break;
		}
	}
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
			if(F->getName()=="free" && isAllGenericJS)
			{
				deleteInstructionAndUnusedOperands(call);
				Changed = true;
			}
			else if(F->getIntrinsicID()==Intrinsic::cheerp_deallocate ||
			        F->getIntrinsicID()==Intrinsic::cheerp_deallocate_array)
			{
				Type* ty = call->getOperand(0)->getType();
				assert(isa<PointerType>(ty));
				Type* elemTy = cast<PointerType>(ty)->getElementType();
				if (isAllGenericJS || (!cheerp::TypeSupport::isAsmJSPointer(ty) && elemTy->isAggregateType())) {
					deleteInstructionAndUnusedOperands(call);
					Changed = true;
				}
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

Instruction* DelayAllocas::findCommonInsertionPoint(AllocaInst* AI, DominatorTree* DT, Instruction* currentInsertionPoint, Instruction* user)
{
	if(!currentInsertionPoint || DT->dominates(user, currentInsertionPoint))
	{
		if(PHINode* phi = dyn_cast<PHINode>(user))
		{
			// It must dominate all incoming blocks that has the value as an incoming value
			for(unsigned i = 0; i < phi->getNumIncomingValues(); i++)
			{
				if(phi->getIncomingValue(i) != AI)
					continue;
				BasicBlock* incomingBlock = phi->getIncomingBlock(i);
				currentInsertionPoint = findCommonInsertionPoint(AI, DT, currentInsertionPoint, incomingBlock->getTerminator());
			}
			return currentInsertionPoint;
		}
		else
			return user;
	}
	else if(DT->dominates(currentInsertionPoint, user))
		return currentInsertionPoint;
	else // Find a common dominator
	{
		BasicBlock* common = DT->findNearestCommonDominator(currentInsertionPoint->getParent(),user->getParent());
		return common->getTerminator();
	}
}

bool DelayAllocas::runOnFunction(Function& F)
{
	// We apply this pass only on genericjs functions
	if (F.getSection()==StringRef("asmjs"))
		return false;
	bool Changed = false;
	LoopInfo* LI = &getAnalysis<LoopInfo>();
	DominatorTree* DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
	cheerp::Registerize * registerize = getAnalysisIfAvailable<cheerp::Registerize>();

	std::map<AllocaInst*, Instruction*> movedAllocaMaps;
	for ( BasicBlock& BB : F )
	{
		for ( BasicBlock::iterator it = BB.begin(); it != BB.end(); ++it)
		{
			AllocaInst* AI=dyn_cast<AllocaInst>(it);
			if (!AI || AI->use_empty())
				continue;
			// Delay the alloca as much as possible by putting it in the dominator block of all the uses
			// Unless that block is in a loop, then put it above the loop
			Instruction* currentInsertionPoint = NULL;
			for(User* U: AI->users())
				currentInsertionPoint = findCommonInsertionPoint(AI, DT, currentInsertionPoint, cast<Instruction>(U));
			Loop* loop=LI->getLoopFor(currentInsertionPoint->getParent());
			if(loop)
			{
				while(loop->getParentLoop())
					loop = loop->getParentLoop();
				BasicBlock* loopHeader = loop->getHeader();
				// We need to put the alloca in the dominator of the loop
				BasicBlock* loopDominator = NULL;
				for(auto it = pred_begin(loopHeader);it != pred_end(loopHeader); ++it)
				{
					if(!loopDominator)
						loopDominator = *it;
					else if(DT->dominates(loopDominator, *it))
						; //Nothing to do
					else if(DT->dominates(*it, loopDominator))
						loopDominator = *it;
					else // Find a common dominator
						loopDominator = DT->findNearestCommonDominator(loopDominator, *it);
				}
				currentInsertionPoint = loopDominator->getTerminator();
			}
			movedAllocaMaps.insert(std::make_pair(AI, currentInsertionPoint));
			if(!Changed && registerize)
				registerize->invalidateLiveRangeForAllocas(F);
			Changed = true;
		}
	}
	for(auto& it: movedAllocaMaps)
		it.first->moveBefore(it.second);
	if(Changed && registerize)
		registerize->computeLiveRangeForAllocas(F);
	return Changed;
}

const char* DelayAllocas::getPassName() const
{
	return "DelayAllocas";
}

char DelayAllocas::ID = 0;

void DelayAllocas::getAnalysisUsage(AnalysisUsage & AU) const
{
	AU.addPreserved<cheerp::PointerAnalyzer>();
	AU.addPreserved<cheerp::Registerize>();
	AU.addPreserved<cheerp::GlobalDepsAnalyzer>();
	AU.addRequired<DominatorTreeWrapperPass>();
	AU.addRequired<LoopInfo>();
	AU.addPreserved<LoopInfo>();
	llvm::Pass::getAnalysisUsage(AU);
}

FunctionPass *createDelayAllocasPass() { return new DelayAllocas(); }

}

using namespace llvm;

INITIALIZE_PASS_BEGIN(AllocaArrays, "AllocaArrays", "Transform allocas of REGULAR type to arrays of 1 element",
			false, false)
INITIALIZE_PASS_END(AllocaArrays, "AllocaArrays", "Transform allocas of REGULAR type to arrays of 1 element",
			false, false)

INITIALIZE_PASS_BEGIN(DelayAllocas, "DelayAllocas", "Moves allocas as close as possible to the actual users",
			false, false)
INITIALIZE_PASS_END(DelayAllocas, "DelayAllocas", "Moves allocas as close as possible to the actual users",
			false, false)

INITIALIZE_PASS_BEGIN(FreeAndDeleteRemoval, "FreeAndDeleteRemoval", "Remove free and delete calls of genericjs objects",
			false, false)
INITIALIZE_PASS_END(FreeAndDeleteRemoval, "FreeAndDeleteRemoval", "Remove free and delete calls of genericjs objects",
			false, false)

INITIALIZE_PASS_BEGIN(PointerToImmutablePHIRemoval, "PointerToImmutablePHIRemoval", "Moves allocas as close as possible to the actual users",
			false, false)
INITIALIZE_PASS_END(PointerToImmutablePHIRemoval, "PointerToImmutablePHIRemoval", "Moves allocas as close as possible to the actual users",
			false, false)
