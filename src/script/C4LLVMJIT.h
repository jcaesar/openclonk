/*
 * OpenClonk, http://www.openclonk.org
 *
 * Copyright (c) 2001-2009, RedWolf Design GmbH, http://www.clonk.de/
 * Copyright (c) 2009-2016, The OpenClonk Team and contributors
 *
 * Distributed under the terms of the ISC license; see accompanying file
 * "COPYING" for details.
 *
 * "Clonk" is a registered trademark of Matthes Bender, used with permission.
 * See accompanying file "TRADEMARK" for details.
 *
 * To redistribute this file separately, substitute the full license texts
 * for the above references.
 */

// Copied together from different versions of the Kaleidoscope tutorial,
// e.g. https://github.com/AndySomogyi/cayman/blob/aaa809c/src/llvm_orc_initial.cpp

#ifndef C4JIT_H
#define C4JIT_H

#include "llvm/ADT/STLExtras.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/RuntimeDyld.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/ExecutionEngine/Orc/CompileUtils.h"
#include "llvm/ExecutionEngine/JITSymbol.h"
#include "llvm/ExecutionEngine/Orc/IRCompileLayer.h"
#include <llvm/ExecutionEngine/Orc/IRTransformLayer.h>
#include "llvm/ExecutionEngine/Orc/LambdaResolver.h"
#include "llvm/ExecutionEngine/Orc/ObjectLinkingLayer.h"
#include "llvm/ExecutionEngine/Orc/GlobalMappingLayer.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Mangler.h"
#include "llvm/Support/DynamicLibrary.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include <algorithm>
#include <memory>
#include <string>
#include <vector>

// Straight steal from C4.
class C4JIT {
public:
	typedef std::unique_ptr<llvm::Module> ModulePtr;
	typedef std::function<ModulePtr(ModulePtr)> OptimizeF;
	typedef llvm::orc::ObjectLinkingLayer<> ObjLayerT;
	typedef llvm::orc::IRCompileLayer<ObjLayerT> CompileLayerT;
	typedef llvm::orc::IRTransformLayer<CompileLayerT, OptimizeF> OptimizeLayerT;
	typedef llvm::orc::GlobalMappingLayer<OptimizeLayerT> GlobalMappingLayerT;
	typedef GlobalMappingLayerT::ModuleSetHandleT ModuleHandle;
private:
	std::unique_ptr<llvm::TargetMachine> TM;
	const llvm::DataLayout DL;
	ObjLayerT ObjectLayer;
	CompileLayerT CompileLayer;
	OptimizeLayerT OptimizeLayer;
	GlobalMappingLayerT MappingLayer;
public:

	decltype(TM) selectTarget() {
		static bool has_initialized = false;
		if(!has_initialized) {
			llvm::InitializeNativeTarget();
			llvm::InitializeNativeTargetAsmPrinter();
			llvm::InitializeNativeTargetAsmParser();
			has_initialized = true;
		}
		llvm::EngineBuilder eb;
		std::string err;
		eb.setErrorStr(&err);
		auto target = eb.selectTarget();
		if (!target) Log(err.c_str());
		assert(target);
		return std::unique_ptr<llvm::TargetMachine>(target);
	}

	C4JIT() : 
		TM(selectTarget()),
		DL(TM->createDataLayout()),
		CompileLayer(ObjectLayer, llvm::orc::SimpleCompiler(*TM)), 
		OptimizeLayer(CompileLayer, [this](ModulePtr M) { return optimizeModule(std::move(M)); }),
		MappingLayer(OptimizeLayer)
	{}

	llvm::TargetMachine &getTargetMachine() { return *TM; }

	ModuleHandle addModule(ModulePtr M) {
		auto Resolver = llvm::orc::createLambdaResolver(
			[&](const std::string &Name) {
				if (auto Sym = MappingLayer.findSymbol(Name, false))
					return Sym;
				if (auto Sym = CompileLayer.findSymbol(Name, false))
					return Sym;
				return llvm::JITSymbol(nullptr);
			},
			[&](const std::string &Name) {
				// If it can't be resolved locally, it can be resolved. Go away.
				return llvm::JITSymbol(nullptr);
			}
		);

		// Build a singlton module set to hold our module.
		std::vector<ModulePtr> Ms;
		Ms.push_back(std::move(M));

		// Add the set to the JIT with the resolver we created above and a newly
		// created SectionMemoryManager.
		return MappingLayer.addModuleSet(std::move(Ms),
			std::make_unique<llvm::SectionMemoryManager>(),
			std::move(Resolver));
	}

	llvm::JITSymbol findSymbol(llvm::StringRef Name, bool mangle = false) {
		if (mangle) {
			std::string MangledName;
			llvm::raw_string_ostream MangledNameStream(MangledName);
			llvm::Mangler::getNameWithPrefix(MangledNameStream, Name, DL);
			return MappingLayer.findSymbol(MangledNameStream.str(), true);
		} else
			return MappingLayer.findSymbol(Name, true);
	}

	void removeModule(ModuleHandle H) {
		MappingLayer.removeModuleSet(H);
	}
	void addGlobalMapping(llvm::StringRef fn, llvm::JITTargetAddress Addr) {
		MappingLayer.setGlobalMapping(fn, Addr);
	}
	void addGlobalMapping(llvm::Function* fn, llvm::JITTargetAddress Addr) {
		MappingLayer.setGlobalMapping(fn->getName(), Addr);
	}
	template<typename... T>
	auto makeModule(T&&... t) {
		auto mod = std::make_unique<llvm::Module>(std::forward<T>(t)...);
		mod->setDataLayout(DL);
		return mod;
	}
private:
	ModulePtr optimizeModule(ModulePtr module) {
		llvm::PassManagerBuilder PMBuilder;
		PMBuilder.BBVectorize = true;
		PMBuilder.SLPVectorize = true;
		PMBuilder.VerifyInput = true;
		PMBuilder.VerifyOutput = true;
		PMBuilder.OptLevel = 2;

		llvm::legacy::FunctionPassManager perFunctionPasses(module.get());
		PMBuilder.populateFunctionPassManager(perFunctionPasses);
		perFunctionPasses.doInitialization();

		for (llvm::Function &function : *module)
			perFunctionPasses.run(function);

		perFunctionPasses.doFinalization();

		llvm::legacy::PassManager perModulePasses;
		PMBuilder.populateModulePassManager(perModulePasses);
		perModulePasses.run(*module);

		module->dump();
		return module;
	}
};

#endif
