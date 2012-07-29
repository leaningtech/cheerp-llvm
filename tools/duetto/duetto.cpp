//===-- llc.cpp - Implement the LLVM Native Code Generator ----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is the llc code generator driver. It provides a convenient
// command-line interface for generating native assembly-language code
// or C code, given LLVM bitcode.
//
//===----------------------------------------------------------------------===//

#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Support/IRReader.h"
#include "llvm/CodeGen/LinkAllAsmWriterComponents.h"
#include "llvm/CodeGen/LinkAllCodegenComponents.h"
#include "llvm/MC/SubtargetFeature.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Support/IRBuilder.h"
#include <memory>
#include <iostream>
using namespace llvm;
using namespace std;

// General options for llc.  Other pass-specific options are specified
// within the corresponding llc passes, and target-specific options
// and back-end code generation options are specified with the target machine.
//
static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::init("-"));

static cl::opt<std::string>
OutputFilename("o", cl::desc("Output filename"), cl::value_desc("filename"));

// Determine optimization level.
static cl::opt<char>
OptLevel("O",
         cl::desc("Optimization level. [-O0, -O1, -O2, or -O3] "
                  "(default = '-O2')"),
         cl::Prefix,
         cl::ZeroOrMore,
         cl::init(' '));

static cl::opt<std::string>
TargetTriple("mtriple", cl::desc("Override target triple for module"));

static cl::opt<std::string>
MArch("march", cl::desc("Architecture to generate code for (see --version)"));

static cl::opt<std::string>
MCPU("mcpu",
  cl::desc("Target a specific cpu type (-mcpu=help for details)"),
  cl::value_desc("cpu-name"),
  cl::init(""));

static cl::list<std::string>
MAttrs("mattr",
  cl::CommaSeparated,
  cl::desc("Target specific attributes (-mattr=help for details)"),
  cl::value_desc("a1,+a2,-a3,..."));

static cl::opt<Reloc::Model>
RelocModel("relocation-model",
             cl::desc("Choose relocation model"),
             cl::init(Reloc::Default),
             cl::values(
            clEnumValN(Reloc::Default, "default",
                       "Target default relocation model"),
            clEnumValN(Reloc::Static, "static",
                       "Non-relocatable code"),
            clEnumValN(Reloc::PIC_, "pic",
                       "Fully relocatable, position independent code"),
            clEnumValN(Reloc::DynamicNoPIC, "dynamic-no-pic",
                       "Relocatable external references, non-relocatable code"),
            clEnumValEnd));

static cl::opt<llvm::CodeModel::Model>
CMModel("code-model",
        cl::desc("Choose code model"),
        cl::init(CodeModel::Default),
        cl::values(clEnumValN(CodeModel::Default, "default",
                              "Target default code model"),
                   clEnumValN(CodeModel::Small, "small",
                              "Small code model"),
                   clEnumValN(CodeModel::Kernel, "kernel",
                              "Kernel code model"),
                   clEnumValN(CodeModel::Medium, "medium",
                              "Medium code model"),
                   clEnumValN(CodeModel::Large, "large",
                              "Large code model"),
                   clEnumValEnd));

static cl::opt<bool>
RelaxAll("mc-relax-all",
  cl::desc("When used with filetype=obj, "
           "relax all fixups in the emitted object file"));

cl::opt<TargetMachine::CodeGenFileType>
FileType("filetype", cl::init(TargetMachine::CGFT_AssemblyFile),
  cl::desc("Choose a file type (not all types are supported by all targets):"),
  cl::values(
       clEnumValN(TargetMachine::CGFT_AssemblyFile, "asm",
                  "Emit an assembly ('.s') file"),
       clEnumValN(TargetMachine::CGFT_ObjectFile, "obj",
                  "Emit a native object ('.o') file [experimental]"),
       clEnumValN(TargetMachine::CGFT_Null, "null",
                  "Emit nothing, for performance testing"),
       clEnumValEnd));

cl::opt<bool> NoVerify("disable-verify", cl::Hidden,
                       cl::desc("Do not verify input module"));

cl::opt<bool> DisableDotLoc("disable-dot-loc", cl::Hidden,
                            cl::desc("Do not use .loc entries"));

cl::opt<bool> DisableCFI("disable-cfi", cl::Hidden,
                         cl::desc("Do not use .cfi_* directives"));

cl::opt<bool> EnableDwarfDirectory("enable-dwarf-directory", cl::Hidden,
    cl::desc("Use .file directives with an explicit directory."));

static cl::opt<bool>
DisableRedZone("disable-red-zone",
  cl::desc("Do not emit code that uses the red zone."),
  cl::init(false));

static cl::opt<bool>
EnableFPMAD("enable-fp-mad",
  cl::desc("Enable less precise MAD instructions to be generated"),
  cl::init(false));

static cl::opt<bool>
PrintCode("print-machineinstrs",
  cl::desc("Print generated machine code"),
  cl::init(false));

static cl::opt<bool>
DisableFPElim("disable-fp-elim",
  cl::desc("Disable frame pointer elimination optimization"),
  cl::init(false));

static cl::opt<bool>
DisableFPElimNonLeaf("disable-non-leaf-fp-elim",
  cl::desc("Disable frame pointer elimination optimization for non-leaf funcs"),
  cl::init(false));

static cl::opt<bool>
DisableExcessPrecision("disable-excess-fp-precision",
  cl::desc("Disable optimizations that may increase FP precision"),
  cl::init(false));

static cl::opt<bool>
EnableUnsafeFPMath("enable-unsafe-fp-math",
  cl::desc("Enable optimizations that may decrease FP precision"),
  cl::init(false));

static cl::opt<bool>
EnableNoInfsFPMath("enable-no-infs-fp-math",
  cl::desc("Enable FP math optimizations that assume no +-Infs"),
  cl::init(false));

static cl::opt<bool>
EnableNoNaNsFPMath("enable-no-nans-fp-math",
  cl::desc("Enable FP math optimizations that assume no NaNs"),
  cl::init(false));

static cl::opt<bool>
EnableHonorSignDependentRoundingFPMath("enable-sign-dependent-rounding-fp-math",
  cl::Hidden,
  cl::desc("Force codegen to assume rounding mode can change dynamically"),
  cl::init(false));

static cl::opt<bool>
GenerateSoftFloatCalls("soft-float",
  cl::desc("Generate software floating point library calls"),
  cl::init(false));

static cl::opt<llvm::FloatABI::ABIType>
FloatABIForCalls("float-abi",
  cl::desc("Choose float ABI type"),
  cl::init(FloatABI::Default),
  cl::values(
    clEnumValN(FloatABI::Default, "default",
               "Target default float ABI type"),
    clEnumValN(FloatABI::Soft, "soft",
               "Soft float ABI (implied by -soft-float)"),
    clEnumValN(FloatABI::Hard, "hard",
               "Hard float ABI (uses FP registers)"),
    clEnumValEnd));

static cl::opt<bool>
DontPlaceZerosInBSS("nozero-initialized-in-bss",
  cl::desc("Don't place zero-initialized symbols into bss section"),
  cl::init(false));

static cl::opt<bool>
EnableGuaranteedTailCallOpt("tailcallopt",
  cl::desc("Turn fastcc calls into tail calls by (potentially) changing ABI."),
  cl::init(false));

static cl::opt<bool>
DisableTailCalls("disable-tail-calls",
  cl::desc("Never emit tail calls"),
  cl::init(false));

static cl::opt<unsigned>
OverrideStackAlignment("stack-alignment",
  cl::desc("Override default stack alignment"),
  cl::init(0));

static cl::opt<bool>
EnableRealignStack("realign-stack",
  cl::desc("Realign stack if needed"),
  cl::init(true));

static cl::opt<bool>
DisableSwitchTables(cl::Hidden, "disable-jump-tables",
  cl::desc("Do not generate jump tables."),
  cl::init(false));

static cl::opt<std::string>
TrapFuncName("trap-func", cl::Hidden,
  cl::desc("Emit a call to trap function rather than a trap instruction"),
  cl::init(""));

static cl::opt<bool>
EnablePIE("enable-pie",
  cl::desc("Assume the creation of a position independent executable."),
  cl::init(false));

static cl::opt<bool>
SegmentedStacks("segmented-stacks",
  cl::desc("Use segmented stacks if possible."),
  cl::init(false));


// GetFileNameRoot - Helper function to get the basename of a filename.
static inline std::string
GetFileNameRoot(const std::string &InputFilename) {
  std::string IFN = InputFilename;
  std::string outputFilename;
  int Len = IFN.length();
  if ((Len > 2) &&
      IFN[Len-3] == '.' &&
      ((IFN[Len-2] == 'b' && IFN[Len-1] == 'c') ||
       (IFN[Len-2] == 'l' && IFN[Len-1] == 'l'))) {
    outputFilename = std::string(IFN.begin(), IFN.end()-3); // s/.bc/.s/
  } else {
    outputFilename = IFN;
  }
  return outputFilename;
}

static tool_output_file *GetOutputStream(const char *TargetName,
                                         Triple::OSType OS,
                                         const char *ProgName) {
  // If we don't yet have an output filename, make one.
  if (OutputFilename.empty()) {
    if (InputFilename == "-")
      OutputFilename = "-";
    else {
      OutputFilename = GetFileNameRoot(InputFilename);

      switch (FileType) {
      case TargetMachine::CGFT_AssemblyFile:
        if (TargetName[0] == 'c') {
          if (TargetName[1] == 0)
            OutputFilename += ".cbe.c";
          else if (TargetName[1] == 'p' && TargetName[2] == 'p')
            OutputFilename += ".cpp";
          else
            OutputFilename += ".s";
        } else
          OutputFilename += ".s";
        break;
      case TargetMachine::CGFT_ObjectFile:
        if (OS == Triple::Win32)
          OutputFilename += ".obj";
        else
          OutputFilename += ".o";
        break;
      case TargetMachine::CGFT_Null:
        OutputFilename += ".null";
        break;
      }
    }
  }

  // Decide if we need "binary" output.
  bool Binary = false;
  switch (FileType) {
  case TargetMachine::CGFT_AssemblyFile:
    break;
  case TargetMachine::CGFT_ObjectFile:
  case TargetMachine::CGFT_Null:
    Binary = true;
    break;
  }

  // Open the file.
  std::string error;
  unsigned OpenFlags = 0;
  if (Binary) OpenFlags |= raw_fd_ostream::F_Binary;
  tool_output_file *FDOut = new tool_output_file(OutputFilename.c_str(), error,
                                                 OpenFlags);
  if (!error.empty()) {
    errs() << error << '\n';
    delete FDOut;
    return 0;
  }

  return FDOut;
}

class DuettoWriter
{
private:
	bool isBuiltinConstructor(const char* s, const std::string& typeName);
	bool isBuiltinType(const std::string& typeName, std::string& builtinName);
	void baseSubstitutionForBuiltin(User* i, Instruction* old, AllocaInst* source);
public:
	void rewriteServerMethod(Module& M, Function& F);
	void rewriteClientMethod(Function& F);
	void rewriteNativeObjectsConstructors(Module& M, Function& F);
	/*
	 * Return true if callInst has been rewritten and it must be deleted
	 */
	bool rewriteIfNativeConstructorCall(Module& M, Instruction* i, AllocaInst* newI,
					    Instruction* callInst, Function* called,
					    const std::string& builtinTypeName,
					    SmallVector<Value*, 4>& initialArgs);
	void rewriteNativeAllocationUsers(Module& M,SmallVector<Instruction*,4>& toRemove,
							Instruction* allocation, Type* t,
							const std::string& builtinTypeName);
	Function* getMeta(Function& F, Module& M, int index);
	Constant* getSkel(Function& F, Module& M, StructType* mapType);
	Function* getStub(Function& F, Module& M);
	void makeClient(Module* M);
	void makeServer(Module* M);
};

void DuettoWriter::rewriteServerMethod(Module& M, Function& F)
{
	std::cerr << "CLIENT: Deleting body of server function " << (std::string)F.getName() << std::endl;
	F.deleteBody();
	//Create a new basic in the function, since everything has been deleted
	BasicBlock* bb=BasicBlock::Create(M.getContext(),"entry",&F);

	SmallVector<Value*, 4> args;
	args.reserve(F.arg_size()+1);
	Constant* nameConst = ConstantDataArray::getString(M.getContext(), F.getName());
	llvm::Constant *Zero = llvm::Constant::getNullValue(Type::getInt32Ty(M.getContext()));
	llvm::Constant *Zeros[] = { Zero, Zero };

	GlobalVariable *nameGV = new llvm::GlobalVariable(M, nameConst->getType(), true,
			GlobalVariable::PrivateLinkage, nameConst, ".str");

	Constant* ptrNameConst = ConstantExpr::getGetElementPtr(nameGV, Zeros);
	args.push_back(ptrNameConst);
	for(Function::arg_iterator it=F.arg_begin();it!=F.arg_end();++it)
		args.push_back(&(*it));
	Function* stub=getStub(F,M);

	//Detect if the first two parameters are in the wrong order, this may
	//happen when the return value is a complex type and becomes an argument
	llvm::Value* firstArg = stub->arg_begin();
	llvm::Value* secondArg = (++stub->arg_begin());
	if(stub->arg_size()>1 && !(args[0]->getType()==firstArg->getType() &&
		args[1]->getType()==secondArg->getType()))
	{
		std::cerr << "Inverting first two parameters" << std::endl;
		llvm::Value* tmp;
		tmp=args[0];
		args[0]=args[1];
		args[1]=tmp;
	}

	assert(stub->arg_size()==1 || (args[0]->getType()==firstArg->getType() &&
		args[1]->getType()==secondArg->getType()));

	Value* skelFuncCall=CallInst::Create(stub,args,"",bb);
	if(skelFuncCall->getType()->isVoidTy())
		ReturnInst::Create(M.getContext(),bb);
	else
		ReturnInst::Create(M.getContext(),skelFuncCall,bb);
}

bool DuettoWriter::isBuiltinConstructor(const char* s, const std::string& typeName)
{
	if(strncmp(s,"_ZN",3)!=0)
		return false;
	const char* tmp=s+3;
	char* endPtr;
	int nsLen=strtol(tmp, &endPtr, 10);
	tmp=endPtr;
	if(nsLen==0 || (strncmp(tmp,"client",nsLen)!=0))
	{
		return false;
	}

	tmp+=nsLen;
	int classLen=strtol(tmp, &endPtr, 10);
	tmp=endPtr;

	if(classLen==0 || typeName.compare(0, std::string::npos, tmp, classLen)!=0)
		return false;

	tmp+=classLen;

	if(strncmp(tmp, "C1", 2)!=0)
		return false;

	return true;
}

void DuettoWriter::baseSubstitutionForBuiltin(User* i, Instruction* old, AllocaInst* source)
{
	Instruction* userInst=dyn_cast<Instruction>(i);
	assert(userInst);
	LoadInst* loadI=new LoadInst(source, "duettoPtrLoad", userInst);
	userInst->replaceUsesOfWith(old, loadI);
}

/*
 * Check if a type is builtin and return the type name
 */
bool DuettoWriter::isBuiltinType(const std::string& typeName, std::string& builtinName)
{
	//The type name is not mangled in C++ style, but in LLVM style
	if(typeName.compare(0,14,"class.client::")!=0)
		return false;
	builtinName=typeName.substr(14);
	return true;
}

bool DuettoWriter::rewriteIfNativeConstructorCall(Module& M, Instruction* i, AllocaInst* newI, Instruction* callInst,
						  Function* called,const std::string& builtinTypeName,
						  SmallVector<Value*, 4>& initialArgs)
{
	//A constructor call does have a name, it's non virtual!
	if(called==NULL)
		return false;
	//To be a candidate for substitution it must have an empty body
	if(!called->empty())
		return false;
	const char* funcName=called->getName().data();
	if(!isBuiltinConstructor(funcName, builtinTypeName))
		return false;
	//Verify that this contructor is for the current alloca
	if(callInst->getOperand(0)!=i)
		return false;
	std::cerr << "Rewriting constructor for type " << builtinTypeName << std::endl;

	FunctionType* initialType=called->getFunctionType();
	SmallVector<Type*, 4> initialArgsTypes(initialType->param_begin()+1,
			initialType->param_end());
	FunctionType* newFunctionType=FunctionType::get(*initialType->param_begin(),
			initialArgsTypes, false);
	//Morph into a different call
	//For some builtins we have special support. For the rest we use a default implementation
	std::string duettoBuiltinCreateName;
	if(builtinTypeName=="String" || builtinTypeName=="Array")
		duettoBuiltinCreateName=std::string("_duettoCreateBuiltin")+funcName;
	else
		duettoBuiltinCreateName="default_duettoCreateBuiltin_"+builtinTypeName;
	Function* duettoBuiltinCreate=cast<Function>(M.getOrInsertFunction(duettoBuiltinCreateName,
			newFunctionType));
	CallInst* newCall=CallInst::Create(duettoBuiltinCreate,
			initialArgs, "duettoCreateCall", callInst);
	StoreInst* storeI=new StoreInst(newCall, newI, callInst);
	return true;
}

void DuettoWriter::rewriteNativeAllocationUsers(Module& M, SmallVector<Instruction*,4>& toRemove,
						Instruction* i, Type* t,
						const std::string& builtinTypeName)
{
	//Instead of allocating the type, allocate a pointer to the type
	AllocaInst* newI=new AllocaInst(PointerType::getUnqual(t),"duettoPtrAlloca",i);
	toRemove.push_back(i);

	Instruction::use_iterator it=i->use_begin();
	Instruction::use_iterator itE=i->use_end();
	SmallVector<User*, 4> users(it,itE);
	//Loop over the uses and look for constructors call
	for(unsigned j=0;j<users.size();j++)
	{
		Instruction* userInst = dyn_cast<Instruction>(users[j]);
		if(userInst==NULL)
		{
			std::cerr << "Unsupported non instruction user of builtin alloca" << std::endl;
			baseSubstitutionForBuiltin(users[j], i, newI);
			continue;
		}
		switch(userInst->getOpcode())
		{
			case Instruction::Call:
			{
				CallInst* callInst=static_cast<CallInst*>(userInst);
				//Ignore the last argument, since it's not part of the real ones
				SmallVector<Value*, 4> initialArgs(callInst->op_begin()+1,callInst->op_end()-1);
				bool ret=rewriteIfNativeConstructorCall(M, i, newI, callInst,
									callInst->getCalledFunction(),builtinTypeName,
									initialArgs);
				if(ret)
					toRemove.push_back(callInst);
				else
					baseSubstitutionForBuiltin(callInst, i, newI);
				break;
			}
			case Instruction::Invoke:
			{
				InvokeInst* invokeInst=static_cast<InvokeInst*>(userInst);
				SmallVector<Value*, 4> initialArgs(invokeInst->op_begin()+1,invokeInst->op_end()-3);
				bool ret=rewriteIfNativeConstructorCall(M, i, newI, invokeInst,
									invokeInst->getCalledFunction(),builtinTypeName,
									initialArgs);
				if(ret)
				{
					toRemove.push_back(invokeInst);
					//We need to add a branch to the success label of the invoke call
					BranchInst* branchInst=BranchInst::Create(invokeInst->getNormalDest(),invokeInst);
				}
				else
					baseSubstitutionForBuiltin(invokeInst, i, newI);
				break;
			}
			default:
			{
				userInst->dump();
				std::cerr << "Unsupported opcode for builtin alloca" << std::endl;
				baseSubstitutionForBuiltin(users[j], i, newI);
				break;
			}
		}
	}
}

void DuettoWriter::rewriteNativeObjectsConstructors(Module& M, Function& F)
{
	//Vector of the instructions to be removed in the second pass
	SmallVector<Instruction*, 4> toRemove;

	Function::iterator B=F.begin();
	Function::iterator BE=F.end();
	for(;B!=BE;++B)
	{
		BasicBlock::iterator I=B->begin();
		BasicBlock::iterator IE=B->end();
		for(;I!=IE;++I)
		{
			if(I->getOpcode()==Instruction::Alloca)
			{
				AllocaInst* i=cast<AllocaInst>(&(*I));
				Type* t=i->getAllocatedType();

				std::string builtinTypeName;
				if(!t->isStructTy() || !isBuiltinType((std::string)t->getStructName(), builtinTypeName))
					continue;
				rewriteNativeAllocationUsers(M,toRemove,i,t,builtinTypeName);
			}
			else if(I->getOpcode()==Instruction::Call)
			{
				CallInst* i=cast<CallInst>(&(*I));
				//Check if the function is the C++ new
				Function* called=i->getCalledFunction();
				if(called==NULL)
					continue;
				if(called->getName()!="_Znwm")
					continue;
				//Ok, it's a new, find if the only use is a bitcast
				//in such case we assume that the allocation was for the target type
				Instruction::use_iterator it=i->use_begin();
				if(i->getNumUses()>1)
					continue;
				BitCastInst* bc=dyn_cast<BitCastInst>(*it);
				if(bc==NULL)
					continue;
				Type* t=bc->getDestTy()->getContainedType(0);
				std::string builtinTypeName;
				if(!t->isStructTy() || !isBuiltinType((std::string)t->getStructName(), builtinTypeName))
					continue;
				rewriteNativeAllocationUsers(M,toRemove,bc,t,builtinTypeName);
			}
		}
	}

	//Remove the instructions in backward order to avoid dependency issues
	for(int i=toRemove.size();i>0;i--)
	{
		toRemove[i-1]->eraseFromParent();
	}
}

void DuettoWriter::makeClient(Module* M)
{
	SmallVector<Function*, 4> toRemove;

	Module::iterator F=M->begin();
	Module::iterator FE=M->end();
	for (; F != FE;)
	{
		Function& current=*F;
		++F;
		//Make stubs out of server side code
		//Make sure custom attributes are removed, they
		//may confuse emscripten
		if(current.hasFnAttr(Attribute::Server))
			rewriteServerMethod(*M, current);
		else if(current.hasFnAttr(Attribute::ServerSkel))
		{
			//Purge them away
			toRemove.push_back(&current);
		}
		else
			rewriteNativeObjectsConstructors(*M, current);
		current.removeFnAttr(Attribute::Client);
		current.removeFnAttr(Attribute::Server);
	}
	Module::named_metadata_iterator mdIt=M->named_metadata_begin();
	Module::named_metadata_iterator mdEnd=M->named_metadata_end();
	for(; mdIt!=mdEnd;)
	{
		NamedMDNode& current=*mdIt;
		++mdIt;
		M->eraseNamedMetadata(&current);
	}
	for(unsigned i=0;i<toRemove.size();i++)
		toRemove[i]->eraseFromParent();
}

void DuettoWriter::rewriteClientMethod(Function& F)
{
	std::cerr << "SERVER: Deleting body of client function " << (std::string)F.getName() << std::endl;
	F.deleteBody();
}

Constant* DuettoWriter::getSkel(Function& F, Module& M, StructType* mapType)
{
	LLVMContext& C = M.getContext();
	Function* skelFunc=getMeta(F,M,0);
	//Make the function external, it should be visible from the outside
	Constant* nameConst = ConstantDataArray::getString(C, F.getName());
	
	llvm::Constant *Zero = llvm::Constant::getNullValue(Type::getInt32Ty(C));
	llvm::Constant *Zeros[] = { Zero, Zero };

	GlobalVariable *nameGV = new llvm::GlobalVariable(M, nameConst->getType(), true,
			GlobalVariable::PrivateLinkage, nameConst, ".str");

	Constant* ptrNameConst = ConstantExpr::getGetElementPtr(nameGV, Zeros);
	vector<Constant*> structFields;
	structFields.push_back(ptrNameConst);
	structFields.push_back(skelFunc);
	return ConstantStruct::get(mapType, structFields);
}

Function* DuettoWriter::getMeta(Function& F, Module& M, int index)
{
	llvm::Twine skelName=F.getName()+"_duettoSkel";
	cout << "SERVER: Generating skeleton for " << (std::string)F.getName() << endl;
	NamedMDNode* meta=M.getNamedMetadata(skelName);

	Value* val=meta->getOperand(0)->getOperand(index);
	Function* skelFunc=dyn_cast<llvm::Function>(val);
	assert(skelFunc);
	return skelFunc;
}

Function* DuettoWriter::getStub(Function& F, Module& M)
{
	return getMeta(F,M,1);
}

void DuettoWriter::makeServer(Module* M)
{
	vector<Function*> serverFunction;
	Module::iterator F=M->begin();
	Module::iterator FE=M->end();
	for (; F != FE;)
	{
		Function& current=*F;
		++F;
		//Delete client side code and
		//save aside the function that needs a skel
		if(current.hasFnAttr(Attribute::Client))
			rewriteClientMethod(current);
		else if(current.hasFnAttr(Attribute::Server))
			serverFunction.push_back(&current);
	}

	//Count the function we have to work on
	LLVMContext& C=M->getContext();
	//Add a global structure for name and function pairs
	Type* bytePtrType = Type::getInt8PtrTy(C);
	vector<Type*> funcTypes;
	funcTypes.push_back(bytePtrType);
	funcTypes.push_back(bytePtrType);
	FunctionType* FT=FunctionType::get(Type::getVoidTy(C), funcTypes, false);
	vector<Type*> structTypes;
	structTypes.push_back(Type::getInt8PtrTy(C));
	structTypes.push_back(PointerType::getUnqual(FT));
	StructType* mapType=StructType::create(C, structTypes);
	vector<Constant*> funcs;

	for(unsigned int i=0;i<serverFunction.size();i++)
	{
		Constant* funcMap=getSkel(*serverFunction[i], *M, mapType);
		funcs.push_back(funcMap);
	}

	Constant* nulls[] = { ConstantPointerNull::get(static_cast<PointerType*>(structTypes[0])),
				ConstantPointerNull::get(static_cast<PointerType*>(structTypes[1]))};
	Constant* nullEntry = ConstantStruct::get(mapType, nulls);
	funcs.push_back(nullEntry);

	ArrayType* arrayType=ArrayType::get(mapType, funcs.size());
	Constant* mapConst = ConstantArray::get(arrayType, funcs);
	GlobalVariable* mapVar = new GlobalVariable(*M, arrayType, true,
			GlobalVariable::ExternalLinkage, mapConst, "duettoFuncMap");
}

// main - Entry point for the duetto double target compiler.
//
int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);

  // Enable debug stream buffering.
  EnableDebugBuffering = true;

  LLVMContext &Context = getGlobalContext();
  llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

  // Initialize targets first, so that --version shows registered targets.
  InitializeAllTargets();
  InitializeAllTargetMCs();
  InitializeAllAsmPrinters();
  InitializeAllAsmParsers();

  // Register the target printer for --version.
  cl::AddExtraVersionPrinter(TargetRegistry::printRegisteredTargetsForVersion);

  cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

  // Load the module to be compiled...
  SMDiagnostic Err;
  std::auto_ptr<Module> M;

  M.reset(ParseIRFile(InputFilename, Err, Context));
  if (M.get() == 0) {
    Err.print(argv[0], errs());
    return 1;
  }
  Module* clientMod = M.get();
  //First of all kill the llvm.used global var
  GlobalVariable* g=clientMod->getGlobalVariable("llvm.used");
  if(g)
	  g->eraseFromParent();
  Module* serverMod = CloneModule(clientMod);

  DuettoWriter writer;
  writer.makeClient(clientMod);
  writer.makeServer(serverMod);

  std::string ClientOutputFilename = GetFileNameRoot(InputFilename) + "-client-base.bc";

  std::string errorInfo;
  raw_fd_ostream ClientOut(ClientOutputFilename.c_str(),errorInfo);
  std::cerr << errorInfo << std::endl;

  WriteBitcodeToFile(clientMod, ClientOut);

  ClientOut.close();

  const std::string nativeTriple=sys::getDefaultTargetTriple();
  std::cout << "Compiling for " << nativeTriple << std::endl;
  const Target* theTarget = TargetRegistry::lookupTarget(nativeTriple, errorInfo);
  
  TargetOptions options;
  TargetMachine* target=theTarget->createTargetMachine(nativeTriple, "", "", options,
                                          Reloc::Static, CodeModel::Default, CodeGenOpt::None);
  assert(target);
  // Build up all of the passes that we want to do to the module.
  PassManager PM;

  // Add the target data from the target machine, if it exists, or the module.
  if (const TargetData *TD = target->getTargetData())
    PM.add(new TargetData(*TD));
  else
    PM.add(new TargetData(serverMod));

  std::string ServerOutputFilename = GetFileNameRoot(InputFilename) + "-server.o";

  raw_fd_ostream ServerOut(ServerOutputFilename.c_str(),errorInfo);
  std::cerr << errorInfo << std::endl;
  {
    formatted_raw_ostream FOS(ServerOut);

    // Ask the target to add backend passes as necessary.
    if (target->addPassesToEmitFile(PM, FOS, TargetMachine::CGFT_ObjectFile, NoVerify)) {
      errs() << argv[0] << ": target does not support generation of this"
             << " file type!\n";
      return 1;
    }

    // Before executing passes, print the final values of the LLVM options.
    cl::PrintOptionValues();

    PM.run(*serverMod);
  }
  ServerOut.close();

  /*// If we are supposed to override the target triple, do so now.
  if (!TargetTriple.empty())
    mod.setTargetTriple(Triple::normalize(TargetTriple));

  if (TheTriple.getTriple().empty())
    TheTriple.setTriple(sys::getDefaultTargetTriple());

  } else {
    std::string Err;
    TheTarget = TargetRegistry::lookupTarget(TheTriple.getTriple(), Err);
    if (TheTarget == 0) {
      errs() << argv[0] << ": error auto-selecting target for module '"
             << Err << "'.  Please use the -march option to explicitly "
             << "pick a target.\n";
      return 1;
    }
  }

  // Package up features to be passed to target/subtarget
  std::string FeaturesStr;
  if (MAttrs.size()) {
    SubtargetFeatures Features;
    for (unsigned i = 0; i != MAttrs.size(); ++i)
      Features.AddFeature(MAttrs[i]);
    FeaturesStr = Features.getString();
  }

  CodeGenOpt::Level OLvl = CodeGenOpt::Default;
  switch (OptLevel) {
  default:
    errs() << argv[0] << ": invalid optimization level.\n";
    return 1;
  case ' ': break;
  case '0': OLvl = CodeGenOpt::None; break;
  case '1': OLvl = CodeGenOpt::Less; break;
  case '2': OLvl = CodeGenOpt::Default; break;
  case '3': OLvl = CodeGenOpt::Aggressive; break;
  }

  TargetOptions Options;
  Options.LessPreciseFPMADOption = EnableFPMAD;
  Options.PrintMachineCode = PrintCode;
  Options.NoFramePointerElim = DisableFPElim;
  Options.NoFramePointerElimNonLeaf = DisableFPElimNonLeaf;
  Options.NoExcessFPPrecision = DisableExcessPrecision;
  Options.UnsafeFPMath = EnableUnsafeFPMath;
  Options.NoInfsFPMath = EnableNoInfsFPMath;
  Options.NoNaNsFPMath = EnableNoNaNsFPMath;
  Options.HonorSignDependentRoundingFPMathOption =
      EnableHonorSignDependentRoundingFPMath;
  Options.UseSoftFloat = GenerateSoftFloatCalls;
  if (FloatABIForCalls != FloatABI::Default)
    Options.FloatABIType = FloatABIForCalls;
  Options.NoZerosInBSS = DontPlaceZerosInBSS;
  Options.GuaranteedTailCallOpt = EnableGuaranteedTailCallOpt;
  Options.DisableTailCalls = DisableTailCalls;
  Options.StackAlignmentOverride = OverrideStackAlignment;
  Options.RealignStack = EnableRealignStack;
  Options.DisableJumpTables = DisableSwitchTables;
  Options.TrapFuncName = TrapFuncName;
  Options.PositionIndependentExecutable = EnablePIE;
  Options.EnableSegmentedStacks = SegmentedStacks;

  std::auto_ptr<TargetMachine>
    target(TheTarget->createTargetMachine(TheTriple.getTriple(),
                                          MCPU, FeaturesStr, Options,
                                          RelocModel, CMModel, OLvl));
  assert(target.get() && "Could not allocate target machine!");
  TargetMachine &Target = *target.get();

  if (DisableDotLoc)
    Target.setMCUseLoc(false);

  if (DisableCFI)
    Target.setMCUseCFI(false);

  if (EnableDwarfDirectory)
    Target.setMCUseDwarfDirectory(true);

  if (GenerateSoftFloatCalls)
    FloatABIForCalls = FloatABI::Soft;

  // Disable .loc support for older OS X versions.
  if (TheTriple.isMacOSX() &&
      TheTriple.isMacOSXVersionLT(10, 6))
    Target.setMCUseLoc(false);

  // Figure out where we are going to send the output...
  // Build up all of the passes that we want to do to the module.
  PassManager PM;

  // Add the target data from the target machine, if it exists, or the module.
  if (const TargetData *TD = Target.getTargetData())
    PM.add(new TargetData(*TD));
  else
    PM.add(new TargetData(&mod));

  // Override default to generate verbose assembly.
  Target.setAsmVerbosityDefault(true);

  if (RelaxAll) {
    if (FileType != TargetMachine::CGFT_ObjectFile)
      errs() << argv[0]
             << ": warning: ignoring -mc-relax-all because filetype != obj";
    else
      Target.setMCRelaxAll(true);
  }

  {
    formatted_raw_ostream FOS(Out->os());

    // Ask the target to add backend passes as necessary.
    if (Target.addPassesToEmitFile(PM, FOS, FileType, NoVerify)) {
      errs() << argv[0] << ": target does not support generation of this"
             << " file type!\n";
      return 1;
    }

    // Before executing passes, print the final values of the LLVM options.
    cl::PrintOptionValues();

    PM.run(mod);
  }

  // Declare success.
  Out->keep();*/

  return 0;
}
