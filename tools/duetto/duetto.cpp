//===-- duetto.cpp - The Duetto code splitter -----------------------------===//
//
//	Copyright 2011-2012 Leaning Technlogies
//===----------------------------------------------------------------------===//

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/PassManager.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Duetto/Utils.h"
#include <memory>
#include <iostream>
using namespace llvm;
using namespace std;

static cl::opt<std::string>
InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::init("-"));

static cl::opt<std::string>
OutputFilename("o", cl::desc("Output filename"), cl::value_desc("filename"));

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

class DuettoWriter
{
public:
	void rewriteServerMethod(Module& M, Function& F);
	void rewriteClientMethod(Function& F);
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
		if(current.hasFnAttribute(Attribute::Server))
			rewriteServerMethod(*M, current);
		else
			DuettoUtils::rewriteNativeObjectsConstructors(*M, current);
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
		if(current.hasFnAttribute(Attribute::Client))
			rewriteClientMethod(current);
		else if(current.hasFnAttribute(Attribute::Server))
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
  if (const DataLayout *TD = target->getDataLayout())
    PM.add(new DataLayout(*TD));
  else
    PM.add(new DataLayout(serverMod));

  std::string ServerOutputFilename = GetFileNameRoot(InputFilename) + "-server.o";

  raw_fd_ostream ServerOut(ServerOutputFilename.c_str(),errorInfo);
  std::cerr << errorInfo << std::endl;
  {
    formatted_raw_ostream FOS(ServerOut);

    // Ask the target to add backend passes as necessary.
    if (target->addPassesToEmitFile(PM, FOS, TargetMachine::CGFT_ObjectFile)) {
      errs() << argv[0] << ": target does not support generation of this"
             << " file type!\n";
      return 1;
    }

    // Before executing passes, print the final values of the LLVM options.
    cl::PrintOptionValues();

    PM.run(*serverMod);
  }
  ServerOut.close();
  return 0;
}
