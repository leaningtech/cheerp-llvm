//===-- JSInterop.cpp - The Cheerp JavaScript generator -------------===//
//
//                     Cheerp: The C++ compiler for the Web
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
// Copyright 2015-2018 Leaning Technologies
//
//===----------------------------------------------------------------------===//

#include "llvm/Cheerp/Writer.h"
#include "llvm/IR/InlineAsm.h"

#include <numeric>

using namespace llvm;
using namespace cheerp;

void CheerpWriter::addExportedFreeFunctions(std::vector<StringRef>& namesList, const NamedMDNode* namedNode)
{
	for ( NamedMDNode::const_op_iterator it = namedNode->op_begin(); it != namedNode->op_end(); ++ it )
	{
		const MDNode * node = *it;
		const Function * f = cast<Function>(cast<ConstantAsMetadata>(node->getOperand(0))->getValue());
		// Currently we assign the function to the mangled name, it works better with extern "C" functions
		stream << "var " << f->getName() << '=' << namegen.getName(f) << ';' << NewLine;
		namesList.push_back(f->getName());
	}
}

uint32_t CheerpWriter::countJsParameters(const llvm::Function* F, bool isStatic) const
{
	uint32_t ret = 0;
	auto it = F->arg_begin();
	auto itE = F->arg_end();
	if(!isStatic)
	{
		// The this parameter is implicit
		++it;
	}
	while(it != itE)
	{
		if(it->getType()->isPointerTy() && PA.getPointerKind(&(*it)) == SPLIT_REGULAR)
			ret+=2;
		else
			ret+=1;
		++it;
	}
	return ret;
}

std::vector<StringRef> CheerpWriter::compileClassesExportedToJs()
{
	std::vector<StringRef> exportedNames;
	//Look for metadata which ends in _methods. They are lists
	//of exported methods for JS layout classes
	for( const NamedMDNode& namedNode: module.named_metadata())
	{
		StringRef name = namedNode.getName();

		if(name == "jsexported_methods")
		{
			addExportedFreeFunctions(exportedNames, &namedNode);
			continue;
		}

		if (!name.endswith("_methods") || !name.startswith("class.") )
			continue;

		auto structAndName = TypeSupport::getJSExportedTypeFromMetadata(name, module);
		StructType* t = structAndName.first;
		StringRef jsClassName = structAndName.second;

		auto getMethodName = [&](const MDNode * node) -> StringRef
		{
			assert( isa<Function>(cast<ConstantAsMetadata>(node->getOperand(0))->getValue()) );

			StringRef mangledName = cast<Function>(cast<ConstantAsMetadata>(node->getOperand(0))->getValue())->getName();

			demangler_iterator dmg(mangledName);
			if ( *dmg++ != jsClassName )
				assert( false && "[[jsexport]]: method should be in class" );

			StringRef functionName = *dmg++;

			assert( dmg == demangler_iterator() );
			return functionName;
		};
		auto isStaticMethod = [&](const MDNode * node) -> bool {
			assert(node->getNumOperands() >= 2);
			assert( isa<ConstantInt>(cast<ConstantAsMetadata>(node->getOperand(1))->getValue()) );
			bool isStatic = cast<ConstantInt>(cast<ConstantAsMetadata>(node->getOperand(1))->getValue())->getZExtValue();
			return isStatic;
		};

		//TODO many things to check.. For. ex C1/C2/C3, names collisions, template classes!
		auto isConstructor = [&](const MDNode * node ) -> bool
		{
			return getMethodName(node).startswith("C1");
		};

		auto constructor = std::find_if(namedNode.op_begin(), namedNode.op_end(), isConstructor );

		//First compile the constructor
		if (constructor == namedNode.op_end() )
		{
			llvm::report_fatal_error( Twine("Class: ", jsClassName).concat(" does not define a constructor!") );
			return exportedNames;
		}

		if ( std::find_if( std::next(constructor), namedNode.op_end(), isConstructor ) != namedNode.op_end() )
		{
			llvm::report_fatal_error( Twine("More than one constructor defined for class: ", jsClassName) );
			return exportedNames;
		}

		const MDNode* node = *constructor;
		const Function * f = cast<Function>(cast<ConstantAsMetadata>(node->getOperand(0))->getValue());

		exportedNames.push_back(jsClassName);

		stream << "function " << jsClassName << '(';
		uint32_t fwdArgsCount = countJsParameters(f, /*isStatic*/false);
		for(uint32_t i=0;i<fwdArgsCount;i++)
		{
			if(i!=0)
				stream << ",";
			stream << 'a' << i;
		}
		stream << "){" << NewLine;
		compileType(t, THIS_OBJ);
		//We need to manually add the self pointer
		stream << ';' << NewLine << "this.d=[this];" << NewLine;

		// Special argument for only allocating the object, without calling the
		// C++ constructor
		stream << "if (arguments.length===1&&arguments[0]===undefined){" << NewLine
			<< "return;" << NewLine
			<< "}" << NewLine;
		compileOperand(f);
		stream << '(';
		if(PA.getPointerKind(&*f->arg_begin())==COMPLETE_OBJECT)
			stream << "this";
		else
			stream << "{d:this.d,o:0}";

		for(uint32_t i=0;i<fwdArgsCount;i++)
			stream << ",a" << i;
		stream << ");" << NewLine << "}" << NewLine;

		assert( globalDeps.isReachable(f) );

		//Then compile other methods and add them to the prototype
		for ( NamedMDNode::const_op_iterator it = namedNode.op_begin(); it != namedNode.op_end(); ++ it )
		{
			if ( isConstructor(*it) )
				continue;

			StringRef methodName = getMethodName(*it);
			bool isStatic = isStaticMethod(*it);

			const MDNode * node = *it;
			const Function * f = cast<Function>(cast<ConstantAsMetadata>(node->getOperand(0))->getValue());

			stream << jsClassName;
			if (!isStatic)
				stream << ".prototype";
			stream << '.' << methodName << "=function (";
			uint32_t fwdArgsCount = countJsParameters(f, isStatic);
			for(uint32_t i=0;i<fwdArgsCount;i++)
			{
				if(i!=0)
					stream << ",";
				stream << 'a' << i;
			}
			stream << "){" << NewLine << "return ";
			compileOperand(f);
			stream << '(';
			// If the method is not static, the first argument is the implicit `this`
			if(!isStatic)
			{
				if(PA.getPointerKind(&*f->arg_begin())==COMPLETE_OBJECT)
					stream << "this";
				else
					stream << "{d:this.d,o:0}";
				if(fwdArgsCount)
					stream << ",";
			}
			for(uint32_t i=0;i<fwdArgsCount;i++)
			{
				if(i!=0)
					stream << ",";
				stream << 'a' << i;
			}
			stream << ");" << NewLine << "};" << NewLine;

			assert( globalDeps.isReachable(f) );
		}
	}
	return exportedNames;
}

void CheerpWriter::compileInlineAsm(const CallInst& ci)
{
	const InlineAsm* a=cast<InlineAsm>(ci.getCalledValue());
	// NOTE: We ignore the constraint string here, since the frontend ensures that only "r" is allowed
	StringRef str = a->getAsmString();
	bool needsParamIndex = false;
	int paramIndex = 0;
	auto constraints = a->ParseConstraints();
	// TODO: support output parameters in the template string
	int numOutputs = std::accumulate(constraints.begin(), constraints.end(),
		0, [](int acc, const llvm::InlineAsm::ConstraintInfo& c) {
			return acc + (c.Type == InlineAsm::isOutput);
		});
	auto getInputParamIndex = [&](int p) {
		if (p - numOutputs < 0) {
			llvm::report_fatal_error("Cheerp: Output operands in the asm template are not supported");
		}
		return p - numOutputs;
	};
	for(unsigned i=0;i<str.size();i++)
	{
		if(needsParamIndex)
		{
			if(str[i] >= '0' && str[i] <= '9')
			{
				if(paramIndex == -1)
					paramIndex = 0;
				paramIndex *= 10;
				paramIndex += str[i] - '0';
			}
			else if(paramIndex == -1)
			{
				// Not even 1 digit after the $, it's an escape
				stream << str[i];
				needsParamIndex = false;
			}
			else
			{
				// Parameter parsed, do not forget to output this char as well
				compileOperand(ci.getOperand(getInputParamIndex(paramIndex)));
				stream << str[i];
				needsParamIndex = false;
			}
		}
		else if(str[i] == '$')
		{
			needsParamIndex = true;
			paramIndex = -1;
		}
		else
			stream << str[i];
	}
	if(needsParamIndex)
	{
		// The string ends with a parameter index, do not forget it
		compileOperand(ci.getOperand(getInputParamIndex(paramIndex)));
	}
}
