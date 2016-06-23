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

#include "C4Include.h"
#include "script/C4AulCompiler.h"

#include <inttypes.h>

#include "script/C4Aul.h"
#include "script/C4AulParse.h"
#include "script/C4AulScriptFunc.h"
#include "script/C4ScriptHost.h"

#define C4AUL_Inherited     "inherited"
#define C4AUL_SafeInherited "_inherited"
#define C4AUL_DebugBreak    "__debugbreak"

#undef NDEBUG
#include <assert.h>

#include <llvm/Analysis/Passes.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/JIT.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/PassManager.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Transforms/Scalar.h>
using llvm::Module; using llvm::BasicBlock; using llvm::IRBuilder; using llvm::getGlobalContext; using llvm::FunctionType; using llvm::ExecutionEngine; using llvm::EngineBuilder; using llvm::FunctionPassManager; using llvm::APInt; using llvm::ConstantInt; using llvm::ConstantStruct; using llvm::AllocaInst; using llvm::StructType; using llvm::Constant; using llvm::CmpInst; using llvm::PHINode;
typedef llvm::Function llvmFunction;
typedef llvm::Type llvmType;
typedef llvm::Value llvmValue;
using std::unique_ptr; using std::make_unique;

static std::string vstrprintf(const char *format, va_list args)
{
	va_list argcopy;
	va_copy(argcopy, args);
	int size = vsnprintf(nullptr, 0, format, argcopy);
	if (size < 0)
		throw std::invalid_argument("invalid argument to strprintf");
	va_end(argcopy);
	std::string s;
	s.resize(size + 1);
	size = vsnprintf(&s[0], s.size(), format, args);
	assert(size >= 0);
	s.resize(size);
	return s;
}

static std::string strprintf(const char *format, ...)
{
	va_list args;
	va_start(args, format);
	std::string s = vstrprintf(format, args);
	va_end(args);
	return s;
}

static std::string FormatCodePosition(const C4ScriptHost *source_host, const char *pos, const C4ScriptHost *target_host = nullptr, const C4AulScriptFunc *func = nullptr)
{
	std::string s;
	if (func && func->GetFullName())
	{
		s += strprintf(" (in %s", func->GetFullName().getData());
		if (source_host && pos)
			s += ", ";
		else
			s += ")";
	}
	if (source_host && pos)
	{
		if (!func || !func->GetFullName())
			s += " (";

		int line = SGetLine(source_host->GetScript(), pos);
		int col = SLineGetCharacters(source_host->GetScript(), pos);

		s += strprintf("%s:%d:%d)",
			source_host->GetFilePath(),
			line, col
		);
	}
	if (target_host && source_host != target_host)
	{
		s += strprintf(" (as #appendto/#include to %s)", target_host->ScriptName.getData());
	}
	return s;
}

template<class... T>
static void Warn(const C4ScriptHost *target_host, const C4ScriptHost *host, const char *SPos, const C4AulScriptFunc *func, const char *msg, T &&...args)
{
	std::string message = "WARNING: ";

	message += sizeof...(T) > 0 ? strprintf(msg, std::forward<T>(args)...) : msg;
	message += FormatCodePosition(host, SPos, target_host, func);

	++::ScriptEngine.warnCnt;
	DebugLog(message.c_str());
}

template<class... T>
static void Warn(const C4ScriptHost *target_host, const C4ScriptHost *host, const ::aul::ast::Node *n, const C4AulScriptFunc *func, const char *msg, T &&...args)
{
	return Warn(target_host, host, n->loc, func, msg, std::forward<T>(args)...);
}
template<class... T>
static void Warn(const C4ScriptHost *target_host, const C4ScriptHost *host, const std::nullptr_t &, const C4AulScriptFunc *func, const char *msg, T &&...args)
{
	return Warn(target_host, host, static_cast<const char*>(nullptr), func, msg, std::forward<T>(args)...);
}

template<class... T>
static C4AulParseError Error(const C4ScriptHost *target_host, const C4ScriptHost *host, const char *SPos, const C4AulScriptFunc *func, const char *msg, T &&...args)
{
	std::string message = sizeof...(T) > 0 ? strprintf(msg, std::forward<T>(args)...) : msg;

	message += FormatCodePosition(host, SPos, target_host, func);
	return C4AulParseError(static_cast<C4ScriptHost*>(nullptr), message.c_str());
}

template<class... T>
static C4AulParseError Error(const C4ScriptHost *target_host, const C4ScriptHost *host, const ::aul::ast::Node *n, const C4AulScriptFunc *func, const char *msg, T &&...args)
{
	return Error(target_host, host, n->loc, func, msg, std::forward<T>(args)...);
}
template<class... T>
static C4AulParseError Error(const C4ScriptHost *target_host, const C4ScriptHost *host, const std::nullptr_t &, const C4AulScriptFunc *func, const char *msg, T &&...args)
{
	return Error(target_host, host, static_cast<const char*>(nullptr), func, msg, std::forward<T>(args)...);
}

class C4AulCompiler::PreparseAstVisitor : public ::aul::DefaultRecursiveVisitor
{
	// target_host: The C4ScriptHost on which compilation is done
	C4ScriptHost *target_host = nullptr;
	// host: The C4ScriptHost where the script actually resides in
	C4ScriptHost *host = nullptr;
	// Fn: The C4AulScriptFunc that is currently getting parsed
	C4AulScriptFunc *Fn = nullptr;

public:
	PreparseAstVisitor(C4ScriptHost *host, C4ScriptHost *source_host, C4AulScriptFunc *func = nullptr) : target_host(host), host(source_host), Fn(func) {}

	virtual ~PreparseAstVisitor() {}

	using DefaultRecursiveVisitor::visit;
	virtual void visit(const ::aul::ast::RangeLoop *n) override;
	virtual void visit(const ::aul::ast::VarDecl *n) override;
	virtual void visit(const ::aul::ast::FunctionDecl *n) override;
	virtual void visit(const ::aul::ast::CallExpr *n) override;
	virtual void visit(const ::aul::ast::ParExpr *n) override;
	virtual void visit(const ::aul::ast::AppendtoPragma *n) override;
	virtual void visit(const ::aul::ast::IncludePragma *n) override;
};

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::RangeLoop *n)
{
	const char *cname = n->var.c_str();
	if (n->scoped_var)
	{
		Fn->VarNamed.AddName(cname);
	}
	else
	{
		// Loop variable not explicitly declared here. Look it up in
		// the function and warn if it hasn't been declared at all.
		if (Fn->VarNamed.GetItemNr(cname) == -1)
		{
			Warn(target_host, host, n, Fn, "Implicit declaration of the loop variable in a for-in loop is deprecated: %s", cname);
			Fn->VarNamed.AddName(cname);
		}
	}
	DefaultRecursiveVisitor::visit(n);
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::VarDecl *n)
{
	if (n->constant && n->scope != ::aul::ast::VarDecl::Scope::Global)
	{
		Warn(target_host, host, n, Fn, "Non-global variables cannot be constant");
	}
	for (const auto &var : n->decls)
	{
		const char *cname = var.name.c_str();
		switch (n->scope)
		{
		case ::aul::ast::VarDecl::Scope::Func:
			{
				assert(Fn && "function-local var declaration outside of function");
				if (!Fn)
					throw Error(target_host, host, n, Fn, "internal error: function-local var declaration outside of function");

				if (target_host->Engine->GlobalNamedNames.GetItemNr(cname) >= 0 || target_host->Engine->GlobalConstNames.GetItemNr(cname) >= 0)
					Warn(target_host, host, n, Fn, "function-local variable hides a global variable: %s", cname);
				C4String *s = ::Strings.FindString(cname);
				if (s && target_host->GetPropList()->HasProperty(s))
					Warn(target_host, host, n, Fn, "function-local variable hides an object-local variable: %s", cname);
				Fn->VarNamed.AddName(cname);
				break;
			}
		case ::aul::ast::VarDecl::Scope::Object:
			{
		//		if (host->Engine->GlobalNamedNames.GetItemNr(cname) >= 0 || host->Engine->GlobalConstNames.GetItemNr(cname) >= 0)
		//			Warn(target_host, host, n, Fn, "object-local variable hides a global variable: %s", cname);
		//		C4String *s = ::Strings.RegString(cname);
		//		if (target_host->GetPropList()->HasProperty(s))
		//			Warn(target_host, host, n, Fn, "object-local variable declared multiple times: %s", cname);
		//		else
		//			target_host->GetPropList()->SetPropertyByS(s, C4VNull);
				break;
			}
		case ::aul::ast::VarDecl::Scope::Global:
		//	assert(!Fn && "global var declaration inside function");
		//	if (Fn)
		//		throw Error(target_host, host, n, Fn, "internal error: global var declaration inside function");

		//	if (host->Engine->GlobalNamedNames.GetItemNr(cname) >= 0 || host->Engine->GlobalConstNames.GetItemNr(cname) >= 0)
		//		Warn(target_host, host, n, Fn, "global variable declared multiple times: %s", cname);
		//	if (n->constant)
		//		host->Engine->GlobalConstNames.AddName(cname);
		//	else
		//		host->Engine->GlobalNamedNames.AddName(cname);
			break;
		}
	}

	DefaultRecursiveVisitor::visit(n);
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::FunctionDecl *n)
{
	// create script fn
	C4PropListStatic *Parent = n->is_global ? target_host->Engine->GetPropList() : target_host->GetPropList();
	const char *cname = n->name.c_str();

	assert(!Fn);

	// Look up the overloaded function before adding the overloading one
	C4AulFunc *parent_func = Parent->GetFunc(cname);

	Fn = new C4AulScriptFunc(Parent, target_host, cname, n->loc);
	for (const auto &param : n->params)
	{
		Fn->AddPar(param.name.c_str());
	}
	if (n->has_unnamed_params)
		Fn->ParCount = C4AUL_MAX_Par;

	// Add function to def/engine
	Fn->SetOverloaded(parent_func);
	Parent->SetPropertyByS(Fn->Name, C4VFunction(Fn));

	DefaultRecursiveVisitor::visit(n);

	Fn = nullptr;
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::CallExpr *n)
{
	if (n->append_unnamed_pars && Fn->ParCount != C4AUL_MAX_Par)
	{
		Fn->ParCount = C4AUL_MAX_Par;
	}
	DefaultRecursiveVisitor::visit(n);
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::ParExpr *n)
{
	if (Fn->ParCount != C4AUL_MAX_Par)
	{
		Warn(target_host, host, n, Fn, "using Par() inside a function forces it to take variable arguments");
		Fn->ParCount = C4AUL_MAX_Par;
	}
	DefaultRecursiveVisitor::visit(n);
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::AppendtoPragma *n)
{
	if (n->what.empty())
		host->Appends.emplace_back("*");
	else
		host->Appends.emplace_back(n->what.c_str());
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::IncludePragma *n)
{
	host->Includes.emplace_back(n->what.c_str());
}

class C4AulCompiler::CodegenAstVisitor : public ::aul::DefaultRecursiveVisitor
{
private:
	C4AulScriptFunc *Fn = nullptr;
	// target_host: The C4ScriptHost on which compilation is done
	C4ScriptHost *target_host = nullptr;
	// host: The C4ScriptHost where the script actually resides in
	C4ScriptHost *host = nullptr;

	// LLVM stuff necessary for compilations
	Module* mod; // owned by execution engine
	ExecutionEngine* executionengine;
	unique_ptr<FunctionPassManager> funcpassmgr;
	unique_ptr<IRBuilder<>> m_builder;

	// TODO: If there are more declarations like these, out-source them in a namespace or whatnot.
	llvmFunction *LLVMEngineFunctionCallByPFunc;
public:
	CodegenAstVisitor(C4ScriptHost *host, C4ScriptHost *source_host) : target_host(host), host(source_host) { init(); }
	explicit CodegenAstVisitor(C4AulScriptFunc *func) : Fn(func), target_host(func->pOrgScript), host(target_host) { init(); }

	virtual ~CodegenAstVisitor() {}

	using DefaultRecursiveVisitor::visit;
	//virtual void visit(const ::aul::ast::Noop *) override;
	//virtual void visit(const ::aul::ast::StringLit *n) override;
	//virtual void visit(const ::aul::ast::IntLit *n) override;
	//virtual void visit(const ::aul::ast::BoolLit *n) override;
	//virtual void visit(const ::aul::ast::ArrayLit *n) override;
	//virtual void visit(const ::aul::ast::ProplistLit *n) override;
	//virtual void visit(const ::aul::ast::NilLit *n) override;
	//virtual void visit(const ::aul::ast::ThisLit *n) override;
	//virtual void visit(const ::aul::ast::VarExpr *n) override;
	//virtual void visit(const ::aul::ast::UnOpExpr *n) override;
	//virtual void visit(const ::aul::ast::BinOpExpr *n) override;
	//virtual void visit(const ::aul::ast::SubscriptExpr *n) override;
	//virtual void visit(const ::aul::ast::SliceExpr *n) override;
	virtual void visit(const ::aul::ast::CallExpr *n) override;
	//virtual void visit(const ::aul::ast::ParExpr *n) override;
	//virtual void visit(const ::aul::ast::Block *n) override;
	//virtual void visit(const ::aul::ast::Return *n) override;
	//virtual void visit(const ::aul::ast::ForLoop *n) override;
	//virtual void visit(const ::aul::ast::RangeLoop *n) override;
	//virtual void visit(const ::aul::ast::DoLoop *n) override;
	//virtual void visit(const ::aul::ast::WhileLoop *n) override;
	//virtual void visit(const ::aul::ast::Break *n) override;
	//virtual void visit(const ::aul::ast::Continue *n) override;
	//virtual void visit(const ::aul::ast::If *n) override;
	//virtual void visit(const ::aul::ast::VarDecl *n) override;
	virtual void visit(const ::aul::ast::FunctionDecl *n) override;

	void DumpLLVM() { mod->dump(); }
	void CompileScriptFunc(C4AulScriptFunc *func, const ::aul::ast::Function *def);
private:
	template<class... T>
	C4AulParseError Error(const std::string msg, T &&...args)
	{
		return ::Error(target_host, host, static_cast<const char*>(nullptr), Fn, msg.c_str(), std::forward<T>(args)...);
	}
	template<class... T>
	C4AulParseError Error(const ::aul::ast::Node *n, const std::string msg, T &&...args)
	{
		return ::Error(target_host, host, n, Fn, msg.c_str(), std::forward<T>(args)...);
	}
	template<typename T>
	T* checkCompile(T* t) {
		if(!t)
			throw Error("Internal Error: unexpected empty llvm result");
		return t;
	}

	void init();
	void FnDecls();

	llvmValue* constLLVMPointer(void * ptr);
};


void C4AulCompiler::Preparse(C4ScriptHost *host, C4ScriptHost *source_host, const ::aul::ast::Script *script)
{
	PreparseAstVisitor v(host, source_host);
	v.visit(script);
}

void C4AulCompiler::Compile(C4ScriptHost *host, C4ScriptHost *source_host, const ::aul::ast::Script *script)
{
	fprintf(stderr, "parsing %s...\n", source_host->FilePath.getData());
	CodegenAstVisitor v(host, source_host);
	v.visit(script);
	v.DumpLLVM();
}

void C4AulCompiler::Compile(C4AulScriptFunc *func, const ::aul::ast::Function *def)
{
	assert(!"I'm unsure what this function should do or when it is called…"); // TODO
	//CodegenAstVisitor v(func);
	//v.CompileScriptFunc(func, def);
}

void C4AulCompiler::CodegenAstVisitor::init()
{
	llvm::InitializeNativeTarget();
	mod = new Module("mm", getGlobalContext()); // TODO: name
	std::string err;
	executionengine = EngineBuilder(mod).setErrorStr(&err).create();
	if(!executionengine)
		throw Error("Could not create Execution Engine: " + err);
	executionengine->DisableSymbolSearching();
	funcpassmgr = make_unique<FunctionPassManager>(mod);
	mod->setDataLayout(executionengine->getDataLayout());
	funcpassmgr->add(new llvm::DataLayoutPass(mod));
	funcpassmgr->add(llvm::createBasicAliasAnalysisPass());
	funcpassmgr->add(llvm::createInstructionCombiningPass());
	funcpassmgr->add(llvm::createReassociatePass());
	funcpassmgr->add(llvm::createGVNPass());
	funcpassmgr->add(llvm::createCFGSimplificationPass());
	funcpassmgr->add(llvm::createDeadStoreEliminationPass());
	funcpassmgr->add(llvm::createInstructionCombiningPass());
	funcpassmgr->doInitialization();
	executionengine->addModule(mod);

	FnDecls();
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::FunctionDecl *n)
{
	fprintf(stderr, "compiling %s\n", n->name.c_str());
	m_builder = make_unique<IRBuilder<>>(getGlobalContext());
	llvmFunction* lf = mod->getFunction(n->name); // TODO: GetMangledName?
	if(!lf)
		throw Error(n, "internal error: unable to find function definition for %s", n->name.c_str());
	BasicBlock* bb = BasicBlock::Create(getGlobalContext(), "entrybb", lf);
	m_builder->SetInsertPoint(bb);

	C4PropListStatic *Parent = n->is_global ? target_host->Engine->GetPropList() : target_host->GetPropList();
	C4AulFunc *f = Parent->GetFunc(n->name.c_str());
	while (f)
	{
		if (f->SFunc() && f->SFunc()->pOrgScript == host && f->Parent == Parent)
		{
			if (Fn)
				Warn(target_host, host, n, Fn, "function declared multiple times");
			Fn = f->SFunc();
		}
		f = f->SFunc() ? f->SFunc()->OwnerOverloaded : 0;
	}

	assert(Fn && "CodegenAstVisitor: unable to find function definition");
	if (!Fn)
		throw Error(n, "internal error: unable to find function definition for %s", n->name.c_str());

	// If this isn't a global function, but there is a global one with
	// the same name, and this function isn't overloading a different
	// one, add the global function to the overload chain
	if (!n->is_global && !Fn->OwnerOverloaded)
	{
		C4AulFunc *global_parent = target_host->Engine->GetFunc(Fn->GetName());
		if (global_parent)
			Fn->SetOverloaded(global_parent);
	}

	n->body->accept(this);

	// TODO: nil return with correct return type
	m_builder->CreateRet(nullptr);

	//f->dump();
	llvm::verifyFunction(*lf);

	Fn = nullptr;

}

llvmValue* C4AulCompiler::CodegenAstVisitor::constLLVMPointer(void * ptr)
{
	llvmValue* ic = ConstantInt::get(getGlobalContext(), APInt(sizeof(ptr) * CHAR_BIT, reinterpret_cast<size_t>(ptr), false));
	return m_builder->CreateIntToPtr(ic, llvmType::getInt8PtrTy(getGlobalContext()));
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::CallExpr *n)
{
	const char *cname = n->callee.c_str();

	if (n->context)
		n->context->accept(this);
	for (const auto &arg : n->args)
		arg->accept(this); /* TODO: Save result. Current object context might also become a parameter */

	C4AulFunc *callee = nullptr;


	// TODO: Special handling for overloading
	if (n->callee == C4AUL_Inherited || n->callee == C4AUL_SafeInherited)
	{
		throw Error(n, "Call to inherited not supported yet.");
	}


	unsigned int fn_argc = C4AUL_MAX_Par;
	// Functions without explicit context can be resolved directly
	if (!n->context)
	{
		if (!callee)
			callee = Fn->Parent->GetFunc(cname);
		if (!callee)
			callee = target_host->Engine->GetFunc(cname);

		if (callee)
			fn_argc = callee->GetParCount();
		else
			throw Error(n, "called function not found: '%s'", cname);

		if (n->args.size() > fn_argc)
		{
			// Pop off any args that are over the limit
			Warn(target_host, host, n->args[fn_argc].get(), Fn,
					"call to %s passes %d parameters, of which only %d are used", cname, n->args.size(), fn_argc);
		}
	}
	else
		throw Error(n, "Call to '%s': context (->) not supported yet.", cname);

	// TODO: return the value
	C4AulScriptFunc *sf = callee->SFunc();
	if (sf)
	{
		assert(sf->llvmFunc);
		checkCompile(m_builder->CreateCall(sf->llvmFunc, std::vector<llvmValue*>{}));
	}
	else
	{
		checkCompile(m_builder->CreateCall(LLVMEngineFunctionCallByPFunc, std::vector<llvmValue*>{
			constLLVMPointer(callee), // TODO: Create named constants or annotate in some other way to ease reading the IR a bit…
			ConstantInt::get(getGlobalContext(), APInt(32, callee->GetParCount(), false))
		}));
	}

}

#define LLVM_PFUNC_CALL "$LLVMAulPFuncCall"

// TODO: Right place for this?
extern "C" {
	void LLVMAulPFuncCall(uint8_t * func_i8, uint32_t par_count, ...)
	{
		C4AulFunc *func = reinterpret_cast<C4AulFunc *>(func_i8);

		std::vector<C4Value> pars(func->GetParCount()); // Values initialized to zero
		va_list par_list;
		va_start(par_list, par_count);
		for(uint32_t i = 0; i < std::max<uint32_t>(par_count, func->GetParCount()); ++i); // TODO
		va_end(par_list);
		if(par_count != 0)
			throw C4AulExecError(FormatString("Calling Engine functions with parameters is not yet supported. (in call of \"%s\")", func->GetName()).getData());

		C4Value rv = func->Exec(nullptr /* TODO: Context. */, pars.data(), false);
		// return rv
	}

}

void C4AulCompiler::CodegenAstVisitor::FnDecls() {
	auto llvmvoid = llvmType::getVoidTy(getGlobalContext());

	// Calling engine functions
	FunctionType *efct = FunctionType::get(llvmvoid, std::vector<llvmType*>{
			llvmType::getInt8PtrTy(getGlobalContext()), // "Note that LLVM does not permit pointers to void (void*) [...]. Use i8* instead."
			llvmType::getInt32Ty(getGlobalContext())
		}, true);
	LLVMEngineFunctionCallByPFunc = checkCompile(llvmFunction::Create(efct, llvmFunction::ExternalLinkage, LLVM_PFUNC_CALL, mod));
	executionengine->addGlobalMapping(LLVMEngineFunctionCallByPFunc, reinterpret_cast<void*>(LLVMAulPFuncCall));

	// Declarations for script functions
	for(auto func: ::ScriptEngine.FuncLookUp) {
		C4AulScriptFunc *sf = func->SFunc();
		if(!sf)
			continue;
		FunctionType *ft = FunctionType::get(llvmvoid, {}, false); // TODO: parameter types
		sf->llvmFunc = checkCompile(llvmFunction::Create(ft, llvmFunction::ExternalLinkage, func->GetName(), mod));
	}


}
