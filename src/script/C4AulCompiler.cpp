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

#include <unordered_map>

#include <llvm/Analysis/Passes.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/ExecutionEngine/JIT.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/PassManager.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Transforms/Scalar.h>
using llvm::Module; using llvm::BasicBlock; using llvm::IRBuilder; using llvm::getGlobalContext; using llvm::FunctionType; using llvm::ExecutionEngine; using llvm::EngineBuilder; using llvm::FunctionPassManager; using llvm::APInt; using llvm::ConstantInt; using llvm::ConstantStruct; using llvm::AllocaInst; using llvm::StructType; using llvm::Constant; using llvm::CmpInst;
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

namespace C4V_Type_LLVM {
	static const size_t int_len = 32;
	static const size_t bool_len = 1;
	static const size_t variant_member_count = 2;

	/* variant */
	static size_t getVariantTypeSize() { return sizeof(C4V_Type) * CHAR_BIT; } // Type tag bit count
	static size_t getVariantVarSize() { return sizeof(C4V_Data) * CHAR_BIT; }
	static llvmType* getVariantTypeLLVMType() { return llvmType::getIntNTy(getGlobalContext(), getVariantTypeSize()); }
	static llvmType* getVariantVarLLVMType() { return llvmType::getIntNTy(getGlobalContext(), getVariantVarSize()); }
	static llvm::StructType* getVariantType(bool packed = false) {
		auto tv = std::vector<llvmType*>{
			getVariantTypeLLVMType(), getVariantVarLLVMType()
		};
		assert(tv.size() == variant_member_count);
		return StructType::get(getGlobalContext(), tv, packed);
	}
	typedef struct __attribute__((packed)) {
		C4V_Type typetag;
		C4V_Data data;
	} PackedVariant;
	static llvmType* get(C4V_Type t) {
		switch(t) {
			case C4V_Nil: assert(!"TODO"); return nullptr;
			case C4V_Int: return llvmType::getIntNTy(getGlobalContext(), int_len);
			case C4V_Bool: return llvmType::getIntNTy(getGlobalContext(), bool_len);
			case C4V_PropList:
			case C4V_String:
			case C4V_Array:
			case C4V_Function:
			case C4V_Any:
				return getVariantType();
			default:
				assert(!"TODO");
		}
	}
	Constant* LLVMTypeTag(C4V_Type type) {
    	return ConstantInt::get(getGlobalContext(), APInt(getVariantTypeSize(), type, false));
	}
	llvmValue* defaultVariant(C4V_Type type, bool packed = false) {
		// TODO: Not so sure about this. Revise whether this should work for C4V_Function or just always return a C4V_Nil…
		auto cv = std::vector<Constant *>{
			ConstantInt::get(getGlobalContext(), APInt(getVariantTypeSize(), type, false)),
			ConstantInt::get(getGlobalContext(), APInt(getVariantVarSize(), 0, false))
		};
		assert(getVariantType()->getNumElements() == cv.size());
		return ConstantStruct::get(getVariantType(packed), cv);
	}
	llvmValue* defaultValue(C4V_Type type) {
		switch(type) {
			case C4V_Int: return ConstantInt::get(getGlobalContext(), APInt(int_len, 0, true));
			case C4V_Bool: return ConstantInt::get(getGlobalContext(), APInt(bool_len, 0, false));
			default: return defaultVariant(C4V_Nil);
		}
	}
}

class C4AulCompiler::CodegenAstVisitor : public ::aul::DefaultRecursiveVisitor
{
private:
	class C4CompiledValue
	{
	private:
		C4V_Type valType;
		llvmValue *llvmVal;

		const ::aul::ast::Node *n;
		const CodegenAstVisitor *compiler;

	public:
		C4CompiledValue(const C4V_Type &valType, llvmValue *llvmVal, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler);
		llvmValue *getInt() const;
		llvmValue *getBool() const;
		llvmValue *getString() const;
		llvmValue *getArray() const;
		llvmValue *getPropList() const;
		llvmValue *getVariant() const;
		llvmValue *getValue(C4V_Type t) const;

		static unique_ptr<C4CompiledValue> defaultVal(const C4V_Type type, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler)
		{
			return make_unique<C4CompiledValue>(type, C4V_Type_LLVM::defaultValue(type), n, compiler);
		}
	};

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
	llvmFunction *LLVMEngineValueConversionFunc;
	unique_ptr<C4CompiledValue> tmp_expr; // result from recursive expression code generation

	class AulVariable
	{
	private:
		llvmValue *addr;
		CodegenAstVisitor* cgv;
	public:
		AulVariable(std::string name, ::aul::ast::VarDecl::Scope scope, CodegenAstVisitor* cgv, unique_ptr<C4CompiledValue> defaultVal = nullptr);
		unique_ptr<C4CompiledValue> load(const ::aul::ast::Node *n) {
			return make_unique<C4CompiledValue>(C4V_Any, cgv->m_builder->CreateLoad(addr), n, cgv);
		}
		void store(C4CompiledValue& rv) {
			cgv->m_builder->CreateStore(rv.getValue(C4V_Any), addr);
		}
	};
	std::unordered_map<std::string,AulVariable> fn_var_scope;

public:
	CodegenAstVisitor(C4ScriptHost *host, C4ScriptHost *source_host) : target_host(host), host(source_host) { init(); }
	explicit CodegenAstVisitor(C4AulScriptFunc *func) : Fn(func), target_host(func->pOrgScript), host(target_host) { init(); }

	virtual ~CodegenAstVisitor() {}

	using DefaultRecursiveVisitor::visit;
	//virtual void visit(const ::aul::ast::Noop *) override;
	//virtual void visit(const ::aul::ast::StringLit *n) override;
	virtual void visit(const ::aul::ast::IntLit *n) override;
	virtual void visit(const ::aul::ast::BoolLit *n) override;
	//virtual void visit(const ::aul::ast::ArrayLit *n) override;
	//virtual void visit(const ::aul::ast::ProplistLit *n) override;
	//virtual void visit(const ::aul::ast::NilLit *n) override;
	//virtual void visit(const ::aul::ast::ThisLit *n) override;
	//virtual void visit(const ::aul::ast::VarExpr *n) override;
	virtual void visit(const ::aul::ast::UnOpExpr *n) override;
	virtual void visit(const ::aul::ast::BinOpExpr *n) override;
	//virtual void visit(const ::aul::ast::SubscriptExpr *n) override;
	//virtual void visit(const ::aul::ast::SliceExpr *n) override;
	virtual void visit(const ::aul::ast::CallExpr *n) override;
	//virtual void visit(const ::aul::ast::ParExpr *n) override;
	//virtual void visit(const ::aul::ast::Block *n) override;
	virtual void visit(const ::aul::ast::Return *n) override;
	//virtual void visit(const ::aul::ast::ForLoop *n) override;
	//virtual void visit(const ::aul::ast::RangeLoop *n) override;
	//virtual void visit(const ::aul::ast::DoLoop *n) override;
	//virtual void visit(const ::aul::ast::WhileLoop *n) override;
	//virtual void visit(const ::aul::ast::Break *n) override;
	//virtual void visit(const ::aul::ast::Continue *n) override;
	//virtual void visit(const ::aul::ast::If *n) override;
	//virtual void visit(const ::aul::ast::VarDecl *n) override;
	virtual void visit(const ::aul::ast::FunctionDecl *n) override;

	void DumpLLVM() const { mod->dump(); }
	void CompileScriptFunc(C4AulScriptFunc *func, const ::aul::ast::Function *def);
private:
	template<class... T>
	C4AulParseError Error(const std::string msg, T &&...args) const
	{
		return ::Error(target_host, host, static_cast<const char*>(nullptr), Fn, msg.c_str(), std::forward<T>(args)...);
	}
	template<class... T>
	C4AulParseError Error(const ::aul::ast::Node *n, const std::string msg, T &&...args) const
	{
		return ::Error(target_host, host, n, Fn, msg.c_str(), std::forward<T>(args)...);
	}
	template<typename T>
	T* checkCompile(T* t) const {
		if(!t)
			throw Error("Internal Error: unexpected empty llvm result");
		return t;
	}

	void init();
	void FnDecls();

	llvmValue* constLLVMPointer(void * ptr);
	llvmValue* buildInt(int i) const {
		return llvm::ConstantInt::get(getGlobalContext(), APInt(32, i, true));
	}
	llvmValue* buildBool(bool b) const {
		return llvm::ConstantInt::get(getGlobalContext(), APInt(1, (int) b, true));
	}
	BasicBlock* CreateBlock() const { assert(Fn); return BasicBlock::Create(getGlobalContext(), "anon", Fn->llvmFunc); }
	BasicBlock* CurrentBlock() const { return m_builder->GetInsertBlock(); }
	void SetInsertPoint(BasicBlock* bb) const { return m_builder->SetInsertPoint(bb); }
	/* TODO: I'm not so sure I'm happy that these are const */
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

C4AulCompiler::CodegenAstVisitor::C4CompiledValue::C4CompiledValue(const C4V_Type &valType, llvmValue *llvmVal, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler) : valType(valType), llvmVal(llvmVal), n(n), compiler(compiler)
{
	compiler->checkCompile(llvmVal);
}

C4AulCompiler::CodegenAstVisitor::AulVariable::AulVariable(std::string name, ::aul::ast::VarDecl::Scope scope, CodegenAstVisitor* cgv, unique_ptr<C4CompiledValue> defaultVal)
	: cgv(cgv)
{
	switch(scope) {
		case ::aul::ast::VarDecl::Scope::Func:
			addr = cgv->checkCompile(cgv->m_builder->CreateAlloca(C4V_Type_LLVM::get(C4V_Any), 0, name));
			break;
		default:
			throw cgv->Error("Sorry, only function-scope variables supported so far.");
	}
	assert(cgv);
	if(defaultVal) {
		store(*defaultVal);
	} else {
		cgv->m_builder->CreateStore(C4V_Type_LLVM::defaultValue(C4V_Nil), addr);
	}
}

extern "C" {
	C4V_Data InternalValueConversionFunc(C4V_Type_LLVM::PackedVariant var, C4V_Type t) {
		// TODO: do something sensible (including throwing a proper RuntimeError, if necessary)
		throw "Type conversion not implemented yet";
	}
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getInt() const
{
	auto& bld = *compiler->m_builder;
	switch(valType) {
		case C4V_Int: return llvmVal;
		case C4V_Bool: return compiler->checkCompile(bld.CreateZExt(llvmVal, C4V_Type_LLVM::get(C4V_Int)));
		case C4V_Nil: return compiler->buildInt(0);
		case C4V_Any: {
			auto inttt = C4V_Type_LLVM::LLVMTypeTag(C4V_Int);
			llvmValue* typetag = compiler->checkCompile(bld.CreateExtractValue(llvmVal, {0}));
			// We could probably do some nifty hacks based on C4V_Nil == 0 and C4V_Bool = 2 to also convert those in LLVM, but at this point I consider that premature optimization.
			llvmValue* direct = bld.CreateExtractValue(llvmVal, {1});
			llvmValue* match = compiler->checkCompile(bld.CreateICmp(CmpInst::ICMP_EQ, typetag, inttt));
			BasicBlock* orig = compiler->CurrentBlock();
			BasicBlock* mismatch = compiler->CreateBlock();
			BasicBlock* cont = compiler->CreateBlock();
			bld.CreateCondBr(match, cont, mismatch);
			compiler->SetInsertPoint(mismatch);
			// Yay, we need to pack the struct…
			llvmValue* packed = C4V_Type_LLVM::defaultVariant(C4V_Nil/*hopefully overwritten*/, true);
			for (unsigned int i = 0; i < C4V_Type_LLVM::variant_member_count; i++) {
				packed = bld.CreateInsertValue(packed, bld.CreateExtractValue(llvmVal, {i}), {i});
			}
			llvmValue* convd = compiler->checkCompile(bld.CreateCall(compiler->LLVMEngineValueConversionFunc, std::vector<llvmValue*>{packed, inttt}));
			bld.CreateBr(cont);
			compiler->SetInsertPoint(cont);
			llvm::PHINode *pn = bld.CreatePHI(C4V_Type_LLVM::getVariantVarLLVMType(), 2);
			pn->addIncoming(direct, orig);
			pn->addIncoming(convd, mismatch);
			return compiler->checkCompile(bld.CreateTruncOrBitCast(pn, C4V_Type_LLVM::get(C4V_Int)));
			// Please try not to duplicate this and instead write a function that executes this…

		}
		default: throw compiler->Error(n, "Error: value cannot be converted to Int!");
	}
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getArray() const
{
	if(valType == C4V_Array)
	{
		return llvmVal;
	} else {
		throw compiler->Error(n, "Error: value is not an Array!");
	} 
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getPropList() const
{
	if(valType == C4V_PropList)
	{
		return llvmVal;
	} else {
		throw compiler->Error(n, "Error: value is not a PropList!");
	} 
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getString() const
{
	if(valType == C4V_String)
	{
		return llvmVal;
	} else {
		throw compiler->Error(n, "Error: value is not a String!");
	} 
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getBool() const
{
	if(valType == C4V_Bool)
	{
		return llvmVal;
	} else if(valType == C4V_Int) {
		return compiler->m_builder->CreateICmpNE(llvmVal, compiler->buildInt(0));
	} else {
		throw compiler->Error(n, "Error: value is not a Bool!");
	} 
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getVariant() const
{
	switch(valType) {
		case C4V_Bool: // fall through
		case C4V_Int:
			return compiler->m_builder->CreateInsertValue(C4V_Type_LLVM::defaultVariant(valType),
				compiler->m_builder->CreateZExt(llvmVal, C4V_Type_LLVM::getVariantVarLLVMType()),
				{1});
		case C4V_Nil:
			return C4V_Type_LLVM::defaultVariant(C4V_Nil); // Don't care about the value part
		case C4V_Any:
			return llvmVal;
		default:
			assert(!"Everything can be converted to variant");
			throw compiler->Error(n, "Internal error: Could not convert value to generic!");
	}
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getValue(C4V_Type t) const
{
	switch(t) {
		case C4V_Int: return getInt();
		case C4V_Bool: return getBool();
		case C4V_Any: return getVariant();
		default: assert(!"TODO");
	}
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

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::IntLit *n)
{
	fprintf(stderr, "compiling %d\n", n->value);

	tmp_expr = make_unique<C4CompiledValue>(C4V_Int, buildInt(n->value), n, this);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::BoolLit *n)
{
	fprintf(stderr, "compiling %s\n", n->value ? "True":"False");

	tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, buildBool(n->value), n, this);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::UnOpExpr *n)
{
	// TODO: for which type of expression should we call 'visit'?
	n->operand->accept(this);
	unique_ptr<C4CompiledValue> operand = std::move(tmp_expr);
	// TODO: what is the semantics of n->op? Which value corresponds to which symbol?

	switch(C4ScriptOpMap[n->op].Code) {
		case AB_Neg:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateNeg(tmp_expr->getInt(), "tmp_neg"), n, this);
		case AB_Not:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, m_builder->CreateNot(tmp_expr->getBool(), "tmp_not"), n, this);
		case AB_BitNot:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateNot(tmp_expr->getInt(), "tmp_bit_not"), n, this);
		default: return; // TODO;
	}

}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::BinOpExpr *n)
{
	// TODO: for which type of expression should we call 'visit'?
	n->lhs->accept(this);
	unique_ptr<C4CompiledValue> left  = std::move(tmp_expr);
	n->rhs->accept(this);
	unique_ptr<C4CompiledValue> right = std::move(tmp_expr);
	// TODO: what is the semantics of n->op? Which value corresponds to which symbol?
	
	switch(C4ScriptOpMap[n->op].Code) {
		case AB_Sum:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateAdd(left->getInt(), right->getInt(), "tmp_add"), n, this);
			break;
		case AB_Sub:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateSub(left->getInt(), right->getInt(), "tmp_sub"), n, this);
			break;
		case AB_Mul:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateMul(left->getInt(), right->getInt(), "tmp_mul"), n, this);
			break;
		case AB_Div:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateSDiv(left->getInt(), right->getInt(), "tmp_div"), n, this);
			break;
		case AB_Mod:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateSRem(left->getInt(), right->getInt(), "tmp_mod"), n, this);
			break;
		case AB_Pow:
			// TODO
			break;
		case AB_LeftShift:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateShl(left->getInt(), right->getInt(), "tmp_shl"), n, this);
			break;
		case AB_RightShift:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateLShr(left->getInt(), right->getInt(), "tmp_shr"), n, this);
			break;
		case AB_LessThan:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, m_builder->CreateICmpSLT(left->getInt(), right->getInt(), "tmp_lt"), n, this);
			break;
		case AB_LessThanEqual:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, m_builder->CreateICmpSLE(left->getInt(), right->getInt(), "tmp_le"), n, this);
			break;
		case AB_GreaterThan:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, m_builder->CreateICmpSGT(left->getInt(), right->getInt(), "tmp_gt"), n, this);
			break;
		case AB_GreaterThanEqual:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, m_builder->CreateICmpSGE(left->getInt(), right->getInt(), "tmp_ge"), n, this);
			break;
		case AB_Equal:
			// TODO: implement for C4V_Any
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, m_builder->CreateICmpEQ(left->getInt(), right->getInt(), "tmp_eq"), n, this);
			break;
		case AB_NotEqual:
			// TODO: implement for C4V_Any
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, m_builder->CreateICmpNE(left->getInt(), right->getInt(), "tmp_neq"), n, this);
			break;
		case AB_BitAnd:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateAnd(left->getInt(), right->getInt(), "tmp_and"), n, this);
			break;
		case AB_BitXOr:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateXor(left->getInt(), right->getInt(), "tmp_xor"), n, this);
			break;
		case AB_BitOr:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateOr(left->getInt(), right->getInt(), "tmp_or"), n, this);
			break;
		case AB_JUMPAND:
		{
			// Beware! Not functional yet!
			llvm::Function *currentFun = m_builder->GetInsertBlock()->getParent();

			BasicBlock *evaluate_right_block = BasicBlock::Create(getGlobalContext(), "tmp_jmpand_eval_r", currentFun);
			BasicBlock *fail_early_block     = BasicBlock::Create(getGlobalContext(), "tmp_jmpand_fail");
			BasicBlock *merge_block          = BasicBlock::Create(getGlobalContext(), "tmp_jmpand_merge");
			m_builder->CreateCondBr(left->getBool(), evaluate_right_block, fail_early_block);

			m_builder->SetInsertPoint(evaluate_right_block);
			llvmValue *evaluate_right_value = right->getBool();
			m_builder->CreateBr(merge_block);
			// Code generation of right expression could have changed the block (for example if there was another JUMPAND expression embedded). Update the block to be on the safe side.
			evaluate_right_block = m_builder->GetInsertBlock();

			currentFun->getBasicBlockList().push_back(fail_early_block);
			m_builder->SetInsertPoint(fail_early_block);

			llvmValue *fail_early_value = buildBool(false);
			m_builder->CreateBr(merge_block);
			fail_early_block = m_builder->GetInsertBlock();

			currentFun->getBasicBlockList().push_back(merge_block);
			m_builder->SetInsertPoint(merge_block);

			llvm::PHINode *pn = m_builder->CreatePHI(llvm::IntegerType::get(getGlobalContext(), 32), 2, "tmp_jmpand");
			pn->addIncoming(evaluate_right_value, evaluate_right_block);
			pn->addIncoming(fail_early_value, fail_early_block);

			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, pn, n, this);
		break;
		}
		default: /* silence warning. TODO */ break;
	}
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
	llvmFunction::arg_iterator argit = lf->arg_begin();
	for (int i = 0; i != Fn->GetParCount(); ++i, ++argit) {
		std::string vname;
		if (i < Fn->ParNamed.iSize) {
			vname = Fn->ParNamed.GetItemUnsafe(i);
		} else {
			char fdst[20];
			snprintf(fdst, 20, "par$%d", i);
			vname = fdst;
		}
		auto par = make_unique<C4CompiledValue>(Fn->GetParType()[i], argit, n, this);
		fn_var_scope.insert({{vname, AulVariable(vname, ::aul::ast::VarDecl::Scope::Func, this, move(par))}});
	}
	for (int i = 0; i < Fn->VarNamed.iSize; i++) {
		const char *vname = Fn->VarNamed.GetItemUnsafe(i);
		fn_var_scope.insert({{vname, AulVariable(vname, ::aul::ast::VarDecl::Scope::Func, this)}}); // Caveat: Might do nothing if a parameter with the same name exists. Shouldn't matter…
	}
	assert(argit == lf->arg_end());

	n->body->accept(this);

	// TODO: nil return with correct return type
	m_builder->CreateRet(nullptr);

	//f->dump();
	llvm::verifyFunction(*lf);

	Fn = nullptr;
	fn_var_scope.clear();
	tmp_expr.reset(); // I'd rather get nullpointer errors than stuff failing inside llvm…
}

llvmValue* C4AulCompiler::CodegenAstVisitor::constLLVMPointer(void * ptr)
{
	llvmValue* ic = ConstantInt::get(getGlobalContext(), APInt(sizeof(ptr) * CHAR_BIT, reinterpret_cast<size_t>(ptr), false));
	return m_builder->CreateIntToPtr(ic, llvmType::getInt8PtrTy(getGlobalContext()));
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::CallExpr *n)
{
	const char *cname = n->callee.c_str();
	std::vector<unique_ptr<C4CompiledValue>> arg_vals;

	if (n->context)
		n->context->accept(this);
	for (const auto &arg : n->args) {
		arg->accept(this);
		assert(tmp_expr);
		arg_vals.push_back(move(tmp_expr));
	}

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

	assert(!tmp_expr);
	C4AulScriptFunc *sf = callee->SFunc();
	if (sf)
	{
		assert(sf->llvmFunc);
		while (arg_vals.size() > static_cast<size_t>(sf->GetParCount()))
			arg_vals.pop_back();
		while (arg_vals.size() < static_cast<size_t>(sf->GetParCount()))
			arg_vals.push_back(C4CompiledValue::defaultVal(sf->GetParType()[arg_vals.size()], n, this));
		assert(sf->GetParCount() == static_cast<int>(arg_vals.size()));
		std::vector<llvmValue*> llvm_args(arg_vals.size(), nullptr);
		for(int i = 0; i < sf->GetParCount(); i++)
			llvm_args[i] = arg_vals[i]->getValue(sf->GetParType()[i]);
		assert(sf->GetRetType() != C4V_Nil); // For now, I don't know how to deal with that
		auto llvmret = checkCompile(m_builder->CreateCall(sf->llvmFunc, llvm_args));
		tmp_expr = make_unique<C4CompiledValue>(sf->GetRetType(), llvmret, n, this);
	}
	else
	{
		checkCompile(m_builder->CreateCall(LLVMEngineFunctionCallByPFunc, std::vector<llvmValue*>{
			constLLVMPointer(callee), // TODO: Create named constants or annotate in some other way to ease reading the IR a bit…
			ConstantInt::get(getGlobalContext(), APInt(32, callee->GetParCount(), false))
		}));
	}
	// assert(tmp_expr); // TODO: Once we have all return values…

}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::Return *n)
{
	// Note: There doesn't seem to be a good way to find out whether this is return; or return (foobar);
	tmp_expr.reset();
	n->value->accept(this);
	if(!tmp_expr)
		tmp_expr = C4CompiledValue::defaultVal(C4V_Nil, n, this);
	m_builder->CreateRet(tmp_expr->getValue(Fn->GetRetType()));
	// TODO: We might have to finish the current block and create a new one to make sure stuff that gets compiled after the return is fine, e.g. in if(foo) { return; /* branch instruction compiled here */} (unlikely, but I want this tested!)
}

#define LLVM_PFUNC_CALL "$LLVMAulPFuncCall"
#define LLVM_VARTYPE_CONV "$LLVMVarTypeConv"

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
		// TODO: return rv
	}

}

void C4AulCompiler::CodegenAstVisitor::FnDecls() {
	auto llvmvoid = llvmType::getVoidTy(getGlobalContext());

	// Calling engine functions
	FunctionType *efct = FunctionType::get(llvmvoid, std::vector<llvmType*>{
			llvmType::getInt8PtrTy(getGlobalContext()), // "Note that LLVM does not permit pointers to void (void*) [...]. Use i8* instead."
			llvmType::getInt32Ty(getGlobalContext())
		}, true/*varargs*/);
	LLVMEngineFunctionCallByPFunc = checkCompile(llvmFunction::Create(efct, llvmFunction::ExternalLinkage, LLVM_PFUNC_CALL, mod));
	executionengine->addGlobalMapping(LLVMEngineFunctionCallByPFunc, reinterpret_cast<void*>(LLVMAulPFuncCall));

	// Converting between runtime types
	FunctionType *vct = FunctionType::get(
		C4V_Type_LLVM::getVariantVarLLVMType(),
		std::vector<llvmType*>{	C4V_Type_LLVM::getVariantType(true/*packed*/), C4V_Type_LLVM::getVariantTypeLLVMType()  },
		false
	);
	LLVMEngineValueConversionFunc = checkCompile(llvmFunction::Create(vct, llvmFunction::ExternalLinkage, LLVM_VARTYPE_CONV, mod));
	executionengine->addGlobalMapping(LLVMEngineValueConversionFunc, reinterpret_cast<void*>(InternalValueConversionFunc));

	// Declarations for script functions
	for(const auto& func: ::ScriptEngine.FuncLookUp) {
		C4AulScriptFunc *sf = func->SFunc();
		if(!sf)
			continue;
		std::vector<llvmType*> parTypes;
		for(int i = 0; i < sf->GetParCount(); ++i)
			parTypes.push_back(C4V_Type_LLVM::get(sf->GetParType()[i]));
		FunctionType *ft = FunctionType::get(C4V_Type_LLVM::get(sf->GetRetType()), parTypes, false); // TODO: parameter types
		sf->llvmFunc = checkCompile(llvmFunction::Create(ft, llvmFunction::ExternalLinkage, func->GetName(), mod));
		int i = 0;
		for (llvmFunction::arg_iterator argit = sf->llvmFunc->arg_begin(); i < sf->ParNamed.iSize; ++argit, ++i) {
			argit->setName(sf->ParNamed.GetItemUnsafe(i));
		}

	}
}

static_assert(C4AUL_MAX_Par <= std::numeric_limits<int>::max(), "Use of int in loops iterating over parameters."); // I mean… yeah. This is pretty much given.
