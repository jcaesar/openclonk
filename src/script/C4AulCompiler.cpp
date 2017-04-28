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

/*

Implementation notes:

 1. Passing structs or similar around between C++ and LLVM-generated code was troublesome on tests (even packed).
    Therefore, parameters are passed as two (pointers to) arrays of length C4V_MAX_Par+1, one of C4V_Type, the other of C4V_Value.
	The object context is written to element 0 of these arrays at the start of functions and not touched by anything except the function itself.
	Storing the return value in element 1 of those arrays suggested itself.

	Some care has to be taken when filling those arrays. After starting to fill the arrays, no other code generation should be invoked.
	This is because even calls like getVariant might start to generate code, which might want to use the parameter_array(s).

 2. Dealing with refcounting for ValueArray and friends would be annoying from within LLVM.
	Deletions can instead be done at the end of a tick.
    Therefore, C4RefCnt'ed objects shall not be stored in LLVM values that survive ticks. (global constants, etc.)
	(Alternatively, refcounting would have to be done for those.)

 3. The Preparse AST visitor runs a local type inference, disregarding any separation of the variable by different areas or learned types of other variables.
    Running something like the w-Algorithm or Abstract Interpretation would be nice.

 */

#include "C4Include.h"
#include "script/C4AulCompiler.h"

#include <inttypes.h>

#include "script/C4Aul.h"
#include "script/C4AulParse.h"
#include "script/C4AulScriptFunc.h"
#include "script/C4ScriptHost.h"
#include "script/C4LLVMJIT.h"
#include "script/C4LLVMTypeMagic.h"
#include "script/C4ValueMagic.h"

#define C4AUL_Inherited     "inherited"
#define C4AUL_SafeInherited "_inherited"
#define C4AUL_DebugBreak    "__debugbreak"

#undef NDEBUG
#include <assert.h>

#include <unordered_map>

#include <llvm/Analysis/Passes.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Transforms/Scalar.h>
using llvm::BasicBlock; using llvm::IRBuilder; using llvm::FunctionType; using llvm::ExecutionEngine; using llvm::EngineBuilder; using llvm::legacy::FunctionPassManager; using llvm::APInt; using llvm::ConstantInt; using llvm::ConstantStruct; using llvm::AllocaInst; using llvm::StructType; using llvm::Constant; using llvm::CmpInst;
typedef llvm::Function llvmFunction;
typedef llvm::Type llvmType;
typedef llvm::Value llvmValue;
using std::unique_ptr; using llvm::make_unique;

template<typename T, typename U>
std::vector<T>& operator <<(std::vector<T>& to, const U& from) {
	to.insert(to.end(), from.begin(), from.end());
	return to;
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
	return Error(target_host, host, n ? n->loc : nullptr, func, msg, std::forward<T>(args)...);
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

	template<typename T> void DRVv(T n) { DefaultRecursiveVisitor::visit(n); };
	// Type getting
	C4V_Type expr_type = C4V_Nil;
	std::unordered_map<std::string,C4V_Type> known_types;
	void CheckVariableAccess(const ::aul::ast::Node* n, C4V_Type t)
	{
		auto ven = dynamic_cast<const ::aul::ast::VarExpr*>(n);
		if(ven)
			HasVariableAccess(ven->identifier, t);
	}
	void HasVariableAccess(std::string name, C4V_Type t) {
		auto it = known_types.find(name);
		if (it == known_types.end())
			known_types.emplace(name, t);
		else if (it->second != t)
			it->second = C4V_Any;
	}


public:
	PreparseAstVisitor(C4ScriptHost *host, C4ScriptHost *source_host, C4AulScriptFunc *func = nullptr) : target_host(host), host(source_host), Fn(func) {}
	explicit PreparseAstVisitor(C4AulScriptFunc *func) : Fn(func), target_host(func->pOrgScript), host(target_host) {}

	virtual ~PreparseAstVisitor() {}

	using DefaultRecursiveVisitor::visit;
	virtual void visit(const ::aul::ast::RangeLoop *n) override;
	virtual void visit(const ::aul::ast::VarDecl *n) override;
	virtual void visit(const ::aul::ast::FunctionDecl *n) override;
	virtual void visit(const ::aul::ast::CallExpr *n) override;
	virtual void visit(const ::aul::ast::ParExpr *n) override;
	virtual void visit(const ::aul::ast::AppendtoPragma *n) override;
	virtual void visit(const ::aul::ast::IncludePragma *n) override;

	virtual void visit(const ::aul::ast::StringLit *n) override { DRVv(n); expr_type = C4V_String; }
	virtual void visit(const ::aul::ast::IntLit *n) override { DRVv(n); expr_type = C4V_Int; }
	virtual void visit(const ::aul::ast::BoolLit *n) override { DRVv(n); expr_type = C4V_Bool; }
	virtual void visit(const ::aul::ast::ArrayLit *n) override { DRVv(n); expr_type = C4V_Array; }
	virtual void visit(const ::aul::ast::ProplistLit *n) override { DRVv(n); expr_type = C4V_PropList; }
	virtual void visit(const ::aul::ast::NilLit *n) override { DRVv(n); expr_type = C4V_Nil; }
	virtual void visit(const ::aul::ast::ThisLit *n) override { DRVv(n); expr_type = C4V_PropList; }
	virtual void visit(const ::aul::ast::VarExpr *n) override { DRVv(n); expr_type = C4V_Any; }
	virtual void visit(const ::aul::ast::UnOpExpr *n) override;
	virtual void visit(const ::aul::ast::BinOpExpr *n) override;
	virtual void visit(const ::aul::ast::AssignmentExpr *n) override;
	virtual void visit(const ::aul::ast::SubscriptExpr *n) override { DRVv(n); expr_type = C4V_Any; }
	virtual void visit(const ::aul::ast::SliceExpr *n) override { DRVv(n); expr_type = C4V_Array; }
	virtual void visit(const ::aul::ast::FunctionExpr *n) override { DRVv(n); expr_type = C4V_Function; /* TODO: test */ }
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
	HasVariableAccess(n->var, C4V_Any);
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
		if (var.init)
			var.init->accept(this);
		else
			expr_type = C4V_Any;
		HasVariableAccess(cname, expr_type);
	}
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::FunctionDecl *n)
{
	known_types.clear();
	// create script fn
	C4PropListStatic *Parent = n->is_global ? target_host->Engine->GetPropList() : target_host->GetPropList();
	const char *cname = n->name.c_str();

	assert(!Fn);

	// Look up the overloaded function before adding the overloading one
	C4AulFunc *parent_func = Parent->GetFunc(cname);

	Fn = new C4AulScriptFunc(Parent, target_host, cname, n->loc);
	for (const auto &param : n->params)
	{
		auto pname = param.name.c_str();
		Fn->AddPar(pname, param.type);
		HasVariableAccess(pname, param.type);
	}
	if (n->has_unnamed_params)
		Fn->ParCount = C4AUL_MAX_Par;

	// Add function to def/engine
	Fn->SetOverloaded(parent_func);
	Parent->SetPropertyByS(Fn->Name, C4VFunction(Fn));

	DefaultRecursiveVisitor::visit(n);

	Fn->var_type_hints = move(known_types);

	Fn = nullptr;

	for(const auto& kt: known_types) {
		fprintf(stderr, "%s: knowing: %s is %s\n", cname, kt.first.c_str(), GetC4VName(kt.second));
	}
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::CallExpr *n)
{
	expr_type = C4V_Any;
	if (n->append_unnamed_pars && Fn->ParCount != C4AUL_MAX_Par)
	{
		Fn->ParCount = C4AUL_MAX_Par;
	}
	DefaultRecursiveVisitor::visit(n);
	expr_type = C4V_Any;
}

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::ParExpr *n)
{
	expr_type = C4V_Any;
	if (Fn->ParCount != C4AUL_MAX_Par)
	{
		Warn(target_host, host, n, Fn, "using Par() inside a function forces it to take variable arguments");
		Fn->ParCount = C4AUL_MAX_Par;
	}
	DefaultRecursiveVisitor::visit(n);
	expr_type = C4V_Any;
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

void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::UnOpExpr *n)
{
	DRVv(n);
	auto opr = C4ScriptOpMap[n->op];
	expr_type = opr.RetType;
	switch (opr.Code) {
		case AB_Inc: case AB_Dec:
			assert(opr.Type1 == opr.RetType);
			CheckVariableAccess(&*n->operand, opr.RetType);
		break;
		default: break;
	}
}
void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::BinOpExpr *n)
{
	DRVv(n);
	auto opr = C4ScriptOpMap[n->op];
	switch (opr.Code) {
		case AB_JUMPAND: case AB_JUMPOR:
			assert(opr.RetType != C4V_Any && "C4ScriptOpMap seems wrong. Remove this ugly hack when correct."); // TODO
			expr_type = C4V_Any;
			break;
		default:
			expr_type = opr.RetType;
			break;
	}
}
void C4AulCompiler::PreparseAstVisitor::visit(const ::aul::ast::AssignmentExpr *n)
{
	n->lhs->accept(this);
	n->rhs->accept(this);
	CheckVariableAccess(&*n->lhs, expr_type);

}

namespace C4V_Type_LLVM {
	static const size_t int_len = 32;
	static const size_t bool_len = 1;
	static const size_t variant_member_count = 2;

	/* variant */
	static size_t getVariantTypeSize() { return sizeof(C4V_Type) * CHAR_BIT; } // Type tag bit count
	static size_t getVariantVarSize() { return sizeof(C4V_Data) * CHAR_BIT; }
	static llvmType* getVariantTypeLLVMType() { return llvmType::getIntNTy(llvmcontext, getVariantTypeSize()); }
	static llvmType* getVariantVarLLVMType() { return llvmType::getIntNTy(llvmcontext, getVariantVarSize()); }
	static llvm::StructType* getVariantType() {
		auto tv = std::vector<llvmType*>{
			getVariantTypeLLVMType(), getVariantVarLLVMType()
		};
		assert(tv.size() == variant_member_count);
		return StructType::get(llvmcontext, tv, false);
	}
	static llvmType* get(C4V_Type t) {
		switch(t) {
			case C4V_Nil: assert(!"TODO"); return nullptr;
			case C4V_Int: return llvmType::getIntNTy(llvmcontext, int_len);
			case C4V_Bool: return llvmType::getIntNTy(llvmcontext, bool_len);
			case C4V_PropList:
			case C4V_Object:
			case C4V_Effect:
			case C4V_Def:
			case C4V_String:
			case C4V_Array:
			case C4V_Function:
				return getVariantVarLLVMType();
			case C4V_Any:
				return getVariantType();
			default:
				assert(!"TODO");
		}
	}
	Constant* LLVMTypeTag(C4V_Type type) {
    	return ConstantInt::get(llvmcontext, APInt(getVariantTypeSize(), type, false));
	}
	llvmValue* defaultVariant(C4V_Type type) {
		// TODO: Not so sure about this. Revise whether this should work for C4V_Function or just always return a C4V_Nil…
		auto cv = std::vector<Constant *>{
			ConstantInt::get(llvmcontext, APInt(getVariantTypeSize(), type, false)),
			ConstantInt::get(llvmcontext, APInt(getVariantVarSize(), 0, false))
		};
		assert(getVariantType()->getNumElements() == cv.size());
		return ConstantStruct::get(getVariantType(), cv);
	}
	llvmValue* defaultValue(C4V_Type type) {
		switch(type) {
			case C4V_Int:
				return ConstantInt::get(llvmcontext, APInt(int_len, 0, true));
			case C4V_Bool:
				return ConstantInt::get(llvmcontext, APInt(bool_len, 0, false));
			case C4V_PropList:
			case C4V_String:
			case C4V_Array:
			case C4V_Function:
				return ConstantInt::get(llvmcontext, APInt(getVariantVarSize(), 0, false));
			default:
				return defaultVariant(C4V_Nil);
		}
	}
	typedef std::array<llvmValue*,variant_member_count> UnpackedVariant;
}

class C4AulCompiler::CodegenAstVisitor : public ::aul::DefaultRecursiveVisitor
{
private:

	// Block Handles for both 'continue' and 'break' commands
	BasicBlock*				continue_dest		= nullptr;
	BasicBlock*				break_dest			= nullptr;
	unsigned int			range_loop_depth	= 0;
	std::vector<llvmValue*>	range_loop_cntrs;
	
	class C4CompiledValue
	{
	private:
		C4V_Type valType;
		llvmValue *llvmVal;

		const ::aul::ast::Node *n;

		llvmValue* buildConversion(C4V_Type t_to) const;

	protected:
		CodegenAstVisitor const * const compiler;

	public:
		C4CompiledValue(const C4V_Type &valType, llvmValue *llvmVal, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler);
		virtual ~C4CompiledValue() {}

		C4V_Type getType() const { return valType; }
		llvmValue *getInt() const;
		llvmValue *getBool() const;
		llvmValue *getArray() const { return getHigher(C4V_Array); };
		llvmValue *getPropList() const { return getHigher(C4V_PropList); };
		llvmValue *getString() const { return getHigher(C4V_String); };
		llvmValue *getNil() const;
		llvmValue *getIsNil() const;
		llvmValue *getVariant() const;
		llvmValue *getValue(C4V_Type t) const;
	private:
		llvmValue *getHigher(C4V_Type) const;

	public:
		static unique_ptr<C4CompiledValue> defaultVal(const C4V_Type type, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler)
		{
			return make_unique<C4CompiledValue>(type, C4V_Type_LLVM::defaultValue(type), n, compiler);
		}
	};

	class C4CompiledLValue;
	class AulVariable
	{
	private:
		llvmValue *addr;
		C4V_Type type;
		CodegenAstVisitor* cgv;
	public:
		AulVariable(std::string name, C4V_Type t, ::aul::ast::VarDecl::Scope scope, CodegenAstVisitor* cgv, unique_ptr<C4CompiledValue> defaultVal = nullptr);
		void store(C4CompiledValue& rv) const {
			cgv->m_builder->CreateStore(rv.getValue(type), addr);
		}
		static unique_ptr<C4CompiledLValue> get(std::string var_name, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler);
		C4V_Type getType() const { return type; };
	};
	std::unordered_map<std::string,AulVariable> fn_var_scope;

	class C4CompiledLValue : public C4CompiledValue
	{
	protected:
		C4CompiledLValue(C4V_Type typ, llvmValue *rval, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler) :
			C4CompiledValue(typ, rval, n, compiler) {}
	public:
		virtual void store(unique_ptr<C4CompiledValue>& rval) const = 0;
	};

	class C4CompiledLVariable : public C4CompiledLValue {
	private:
		const AulVariable *const lval;
	public:
		C4CompiledLVariable(llvmValue *rval, const AulVariable* lval, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler) :
			C4CompiledLValue(lval->getType(), rval, n, compiler),
			lval(lval) { }
		void store(unique_ptr<C4CompiledValue>& rval) const { lval->store(*rval); }
		virtual ~C4CompiledLVariable() {}
	};
	
	class C4CompiledLStruct : public C4CompiledLValue {
	private:
		unique_ptr<C4CompiledValue> strk, idx;
	public:
		C4CompiledLStruct(llvmValue *rval, unique_ptr<C4CompiledValue> strk, unique_ptr<C4CompiledValue> idx, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler) :
			C4CompiledLValue(C4V_Any, rval, n, compiler),
			strk(move(strk)), idx(move(idx)) { }
		void store(unique_ptr<C4CompiledValue>& rval) const;
		virtual ~C4CompiledLStruct() {}
	};
	
	class C4CompiledLSlice : public C4CompiledLValue {
	private:
		unique_ptr<C4CompiledValue> strk;
		llvmValue* idx1, *idx2;
	public:
		C4CompiledLSlice(llvmValue *rval, unique_ptr<C4CompiledValue> strk, llvmValue* idx1, llvmValue* idx2, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler) :
			C4CompiledLValue(C4V_Any, rval, n, compiler),
			strk(move(strk)), idx1(idx1), idx2(idx2) { }
		void store(unique_ptr<C4CompiledValue>& rval) const;
		virtual ~C4CompiledLSlice() {}
	};

	C4AulScriptFunc *Fn = nullptr;
	// target_host: The C4ScriptHost on which compilation is done
	C4ScriptHost *target_host = nullptr;
	// host: The C4ScriptHost where the script actually resides in
	C4ScriptHost *host = nullptr;

	// LLVM stuff necessary for compilations
	unique_ptr<llvm::Module> mod;
	unique_ptr<IRBuilder<>> m_builder;
	std::shared_ptr<C4JIT> jit;

	llvmFunction *efunc_CallByPFunc;
	llvmFunction *efunc_CheckArrayIndex;
	llvmFunction *efunc_CompareEquals;
	llvmFunction *efunc_CreateProplist;
	llvmFunction *efunc_CreateValueArray;
	llvmFunction *efunc_GetArrayIndex;
	llvmFunction *efunc_GetArraySlice;
	llvmFunction *efunc_GetStructIndex;
	llvmFunction *efunc_SetArrayIndex;
	llvmFunction *efunc_SetArraySlice;
	llvmFunction *efunc_SetStructIndex;
	llvmFunction *efunc_ValueConversionFunc;
	llvmFunction *efunc_Pow;
	unique_ptr<C4CompiledValue> tmp_expr; // result from recursive expression code generation
	unique_ptr<C4CompiledValue> context_this;
	std::array<llvmValue*,C4V_Type_LLVM::variant_member_count> parameter_array; // place to store parameters and their types when calling an engine function


public:
	CodegenAstVisitor(C4ScriptHost *host, C4ScriptHost *source_host) : target_host(host), host(source_host) { init(); }
	explicit CodegenAstVisitor(C4AulScriptFunc *func) : Fn(func), target_host(func->pOrgScript), host(target_host) { init(); }

	virtual ~CodegenAstVisitor() {}

	using DefaultRecursiveVisitor::visit;
	virtual void visit(const ::aul::ast::Noop *) override {};
	virtual void visit(const ::aul::ast::StringLit *n) override;
	virtual void visit(const ::aul::ast::IntLit *n) override;
	virtual void visit(const ::aul::ast::BoolLit *n) override;
	virtual void visit(const ::aul::ast::ArrayLit *n) override;
	virtual void visit(const ::aul::ast::ProplistLit *n) override;
	virtual void visit(const ::aul::ast::NilLit *n) override;
	virtual void visit(const ::aul::ast::ThisLit *n) override;
	virtual void visit(const ::aul::ast::VarExpr *n) override;
	virtual void visit(const ::aul::ast::UnOpExpr *n) override;
	virtual void visit(const ::aul::ast::BinOpExpr *n) override;
	virtual void visit(const ::aul::ast::AssignmentExpr *n) override;
	virtual void visit(const ::aul::ast::SubscriptExpr *n) override;
	virtual void visit(const ::aul::ast::SliceExpr *n) override;
	virtual void visit(const ::aul::ast::CallExpr *n) override;
	//virtual void visit(const ::aul::ast::ParExpr *n) override;
	//virtual void visit(const ::aul::ast::Block *n) override;
	virtual void visit(const ::aul::ast::Return *n) override;
	virtual void visit(const ::aul::ast::ForLoop *n) override;
	virtual void visit(const ::aul::ast::RangeLoop *n) override;
	virtual void visit(const ::aul::ast::DoLoop *n) override;
	virtual void visit(const ::aul::ast::WhileLoop *n) override;
	virtual void visit(const ::aul::ast::Break *n) override;
	virtual void visit(const ::aul::ast::Continue *n) override;
	virtual void visit(const ::aul::ast::If *n) override;
	virtual void visit(const ::aul::ast::VarDecl *n) override;
	virtual void visit(const ::aul::ast::FunctionDecl *n) override;

	void DumpLLVM() const { mod->dump(); }
	void StandaloneCompile(C4AulScriptFunc *func, const ::aul::ast::Function *def);

	void finalize();
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
	void ExternDecls();
	void FinalizeFunc(C4AulScriptFunc *func, const std::string&);
	llvmValue* constLLVMPointer(void * ptr);
	llvmValue* buildInt(int i) const {
		return llvm::ConstantInt::get(llvmcontext, APInt(32, i, true));
	}
	llvmValue* buildBool(bool b) const {
		return llvm::ConstantInt::get(llvmcontext, APInt(1, (int) b, true));
	}
	llvmValue* buildString(const char* c) const {
		C4String* str = ::Strings.RegString(c);
		return llvm::ConstantInt::get(llvmcontext,
			APInt(C4V_Type_LLVM::getVariantVarSize(), reinterpret_cast<intptr_t>(str), false));
		// TODO: We might need some magic to ensure that this is not deleted early / properly deleted
	}
	BasicBlock* CreateBlock(llvmFunction* parent = nullptr) const { return CreateBlock( nullptr , parent ); }
	BasicBlock* CreateBlock( const char* name , llvmFunction* parent = nullptr) const { assert((m_builder && CurrentBlock()) || parent); return BasicBlock::Create(llvmcontext, name ? name : "anon" , parent ? parent : CurrentBlock()->getParent()); }
	BasicBlock* CurrentBlock() const { return m_builder->GetInsertBlock(); }
	void SetInsertPoint(BasicBlock* bb) const { return m_builder->SetInsertPoint(bb); }
	void SetInsertPoint(BasicBlock* bb, BasicBlock::iterator it) const { return m_builder->SetInsertPoint(bb, it); }
	/* TODO: I'm not so sure I'm happy that these are const */

	C4V_Type_LLVM::UnpackedVariant UnpackValue(llvmValue* packed) const;
	unique_ptr<C4CompiledValue> PackVariant(C4V_Type_LLVM::UnpackedVariant v, const ::aul::ast::Node *n = nullptr);
	template<typename T>
	unique_ptr<C4CompiledValue> LoadPackVariant(T v, std::vector<llvmValue*> gep, const ::aul::ast::Node *n = nullptr) {
		C4V_Type_LLVM::UnpackedVariant upret;
		assert(v.size() == upret.size());
		for (size_t j = 0; j < upret.size(); j++) {
			llvmValue* ep = checkCompile(m_builder->CreateGEP(v[j], gep));
			upret[j] = checkCompile(m_builder->CreateLoad(ep));
		}
		return PackVariant(upret, n);
	}

	template<typename T>
	void UnpackStoreVariant(llvmValue* v, T to, std::vector<llvmValue*> gep) {
		auto upret = UnpackValue(v);
		for (size_t j = 0; j < upret.size(); j++) {
			llvmValue* ep = m_builder->CreateGEP(to[j], gep);
			m_builder->CreateStore(upret[j], ep);
		}
	}
};

C4V_Type_LLVM::UnpackedVariant C4AulCompiler::CodegenAstVisitor::UnpackValue(llvmValue* unpacked) const {
	std::array<llvmValue*,2> ret;
	for (unsigned int i = 0; i < ret.size(); i++) {
		// if you run into llvm type trouble, an unpacked->dump(); here tends to help.
		ret[i] = checkCompile(m_builder->CreateExtractValue(unpacked, {i}));
	}
	return ret;
}

unique_ptr<C4AulCompiler::CodegenAstVisitor::C4CompiledValue>
C4AulCompiler::CodegenAstVisitor::PackVariant(C4V_Type_LLVM::UnpackedVariant v, const ::aul::ast::Node *n) {
	llvmValue* packed = checkCompile(C4V_Type_LLVM::defaultVariant(C4V_Nil/*hopefully overwritten*/));
	for (unsigned int i = 0; i < v.size(); i++)
		packed = checkCompile(m_builder->CreateInsertValue(packed, v[i], {i}));
	return make_unique<C4CompiledValue>(C4V_Any, checkCompile(packed), n, this);
}

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
	v.finalize();
}

void C4AulCompiler::Compile(C4AulScriptFunc *func, const ::aul::ast::Function *def)
{
	{
		// Don't visit the whole definition here; that would create a new function
		// and we don't want that.
		PreparseAstVisitor v(func);
		def->body->accept(&v);
	}
	{
		CodegenAstVisitor v(func);
		v.StandaloneCompile(func, def);
	}
}

C4AulCompiler::CodegenAstVisitor::C4CompiledValue::C4CompiledValue(const C4V_Type &valType, llvmValue *llvmVal, const ::aul::ast::Node *n, const CodegenAstVisitor *compiler) : valType(valType), llvmVal(llvmVal), n(n), compiler(compiler)
{
	compiler->checkCompile(llvmVal);
}

C4AulCompiler::CodegenAstVisitor::AulVariable::AulVariable(std::string name, C4V_Type t, ::aul::ast::VarDecl::Scope scope, CodegenAstVisitor* cgv, unique_ptr<C4CompiledValue> defaultVal)
	: type(t), cgv(cgv)
{
	switch(scope) {
		case ::aul::ast::VarDecl::Scope::Func:
			addr = cgv->checkCompile(cgv->m_builder->CreateAlloca(C4V_Type_LLVM::get(type), 0, name));
			break;
		default:
			throw cgv->Error("Sorry, only function-scope variables supported so far.");
	}
	assert(cgv);
	if(defaultVal) {
		store(*defaultVal);
	} else {
		cgv->m_builder->CreateStore(C4V_Type_LLVM::defaultValue(type), addr);
	}
}

extern "C" {
	C4V_Data InternalValueConversionFunc(C4V_Type current_tt, C4V_Data data, C4V_Type dst_tt) {
		// TODO: This function wants more parameters: Whether the conversion is happening for a parameter,
		// and the necessary information to generate a proper script error
		C4Value orig = AulLLVMToC4Value(current_tt, data);
		C4Value ret;
		if (!orig.CheckConversion(dst_tt))
			throw C4AulExecError(FormatString("runtime type conversion error: %s -> %s", orig.GetTypeName(), GetC4VName(dst_tt)).getData());
		switch (dst_tt) {
			case C4V_Nil: ret.Set0(); // Why would this be called? :/
			case C4V_Int: ret = C4Value(orig.getInt()); break;
			case C4V_Bool: ret = C4Value(orig.getBool()); break;
			// TODO: Properly test the following and make sure everything is fine, including memleaks, etc.
			case C4V_Object: ret = C4Value(orig.getObj()); break;
			case C4V_Def: ret = C4Value(orig.getDef()); break;
			case C4V_PropList: ret = C4Value(orig.getPropList()); break;
			case C4V_String: ret = C4Value(orig.getStr()); break;
			case C4V_Array: ret = C4Value(orig.getArray()); break;
			case C4V_Function: ret = C4Value(orig.getFunction()); break;
			default: assert(!"TODO: Not gonna happen?");
		}
		assert(ret.GetType() == dst_tt);
		return C4ValueToAulLLVM(ret).second;
	}
}

llvmValue* C4AulCompiler::CodegenAstVisitor::C4CompiledValue::buildConversion(C4V_Type t_to) const {
	auto& bld = *compiler->m_builder;
	assert(t_to != C4V_Nil); // That just doesn't make any sense.
	assert(t_to <= C4V_Last); // This function doesn't make sense for C4V_Any and friends either. TODO: What about those enumerates?
	auto ttt = C4V_Type_LLVM::LLVMTypeTag(t_to);
	llvmValue* typetag = compiler->checkCompile(bld.CreateExtractValue(llvmVal, {0}));
	// We could probably do some nifty hacks when converting to int or bool, based on the fact that the values of C4V_Nil, C4V_Int and C4V_Bool are close together.
	llvmValue* direct = bld.CreateExtractValue(llvmVal, {1});
	llvmValue* match = compiler->checkCompile(bld.CreateICmp(CmpInst::ICMP_EQ, typetag, ttt));
	BasicBlock* orig = compiler->CurrentBlock();
	BasicBlock* mismatch = compiler->CreateBlock("typeconv");
	BasicBlock* cont = compiler->CreateBlock("typeconvcont");
	llvm::BranchInst* br = bld.CreateCondBr(match, cont, mismatch);
	if (t_to != C4V_Bool) // Bool is probably more converted to than other types, so I'll leave that for now.
	{
		// We expect that the variable already has the right type in most cases.
		llvm::ICmpInst* cmp = llvm::dyn_cast<llvm::ICmpInst>(br->getCondition());
		assert(cmp);
		llvm::MDBuilder mdb(cmp->getContext());
		br->setMetadata(llvm::LLVMContext::MD_prof, mdb.createBranchWeights(64, 1));
	}
	compiler->SetInsertPoint(mismatch);
	// Yay, we need to pack the struct…
	auto unpacked = compiler->UnpackValue(llvmVal);
	static_assert(unpacked.size() == 2, "Next call needs all args.");
	llvmValue* convd = compiler->checkCompile(bld.CreateCall(compiler->efunc_ValueConversionFunc, std::vector<llvmValue*>{unpacked[0], unpacked[1], ttt}));
	bld.CreateBr(cont);
	compiler->SetInsertPoint(cont);
	llvm::PHINode *pn = bld.CreatePHI(C4V_Type_LLVM::getVariantVarLLVMType(), 2);
	pn->addIncoming(direct, orig);
	pn->addIncoming(convd, mismatch);
	return compiler->checkCompile(pn);
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getInt() const
{
	// TODO: I'd like to annotate the default cases with static_assertions that they actually cannot be.
	switch(valType) {
		case C4V_Int: return llvmVal;
		case C4V_Bool: return compiler->m_builder->CreateZExt(llvmVal, C4V_Type_LLVM::get(C4V_Int));
		case C4V_Nil: return compiler->buildInt(0);
		case C4V_Any: return compiler->m_builder->CreateTruncOrBitCast(buildConversion(C4V_Int), C4V_Type_LLVM::get(C4V_Int));
		default: throw compiler->Error(n, "Error: value cannot be converted to Int!");
	}
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getBool() const
{
	auto zero_comparison = [&](llvmValue *cmp) {
		return compiler->m_builder->CreateICmp(CmpInst::ICMP_NE,
				compiler->m_builder->CreateZExt(cmp, C4V_Type_LLVM::getVariantVarLLVMType()),
				ConstantInt::get(llvmcontext, APInt(C4V_Type_LLVM::getVariantVarSize(), 0, false)));
	};
	switch(valType) {
		case C4V_Nil: return compiler->buildBool(false);
		case C4V_Bool: return llvmVal;
		case C4V_Int: return zero_comparison(llvmVal);
		case C4V_Any: return zero_comparison(buildConversion(C4V_Bool));
		default: throw compiler->Error(n, "Error: value cannot be converted to Bool!");
	}
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getNil() const
{
	switch(valType) {
		case C4V_Nil:
			return llvmVal;
		default:
			throw compiler->Error(n, "Error: value is not a Nil!");
	}
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getIsNil() const
{
	switch(valType) {
		case C4V_Nil:
			return compiler->buildBool(true);
		case C4V_Any:
		{
			auto ttn = C4V_Type_LLVM::LLVMTypeTag(C4V_Nil);
			llvmValue* typetag = compiler->m_builder->CreateExtractValue(llvmVal, {0});

			return compiler->m_builder->CreateICmp(CmpInst::ICMP_EQ, typetag, ttn);
		}
		default: 
			return compiler->buildBool(false);
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
		case C4V_Array:
		case C4V_String:
		case C4V_PropList:
		case C4V_Function:
			return compiler->m_builder->CreateInsertValue(C4V_Type_LLVM::defaultVariant(valType),
				llvmVal, {1});
		default:
			assert(!"Everything can be converted to variant"); // TODO
			throw compiler->Error(n, "Internal error: Could not convert value to generic!");
	}
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getValue(C4V_Type t) const
{
	switch (t) {
		case C4V_Int: return getInt();
		case C4V_Bool: return getBool();
		case C4V_Object:
		case C4V_Def:
		case C4V_Effect:
			t = C4V_PropList;
			// no break
		case C4V_String:
		case C4V_PropList:
		case C4V_Array:
			return getHigher(t);
		case C4V_Any: return getVariant();
		default: assert(!"TODO");
	}
}

llvmValue *C4AulCompiler::CodegenAstVisitor::C4CompiledValue::getHigher(C4V_Type t) const
{
	auto actType = valType;
	switch (actType) {
		case C4V_Object:
		case C4V_Def:
		case C4V_Effect:
			actType = C4V_PropList;
		default: break;
	}
	if (valType == t) return llvmVal;
	if (valType == C4V_Any) return buildConversion(t);
	throw compiler->Error(n, "Error: cannot convert %s to %s!", GetC4VName(valType), GetC4VName(t));
}

unique_ptr<C4AulCompiler::CodegenAstVisitor::C4CompiledLValue> C4AulCompiler::CodegenAstVisitor::AulVariable::get(std::string var_name, const ::aul::ast::Node *n, const C4AulCompiler::CodegenAstVisitor *compiler)
{
	const AulVariable& var = compiler->fn_var_scope.at(var_name);
	// TODO: catch out of bounds
	return make_unique<C4CompiledLVariable>(compiler->m_builder->CreateLoad(var.addr), &var, n, compiler);
}


void C4AulCompiler::CodegenAstVisitor::init()
{
	jit = std::make_shared<C4JIT>();
	mod = jit->makeModule("c4aulllvm", llvmcontext);
	FnDecls();
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::StringLit *n)
{
	tmp_expr = make_unique<C4CompiledValue>(C4V_String, buildString(n->value.c_str()), n, this);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::IntLit *n)
{
	tmp_expr = make_unique<C4CompiledValue>(C4V_Int, buildInt(n->value), n, this);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::BoolLit *n)
{
	tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, buildBool(n->value), n, this);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::ArrayLit *n)
{
	llvmValue* array = m_builder->CreateCall(efunc_CreateValueArray, std::vector<llvmValue*>{ buildInt(n->values.size()) });
	int32_t idx = 0;
	for (auto& val: n->values)
	{
		val->accept(this);
		assert(tmp_expr);
		auto params = std::vector<llvmValue*>{array, buildInt(idx)};
		auto unpacked = UnpackValue(tmp_expr->getVariant());
		params.insert(params.end(), unpacked.begin(), unpacked.end());
		m_builder->CreateCall(efunc_SetArrayIndex, params);
		idx++;
	}
	tmp_expr = make_unique<C4CompiledValue>(C4V_Array, array, n, this);
}
void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::ProplistLit *n) {
	// TODO: Prototypes
	llvmValue* pl = m_builder->CreateCall(efunc_CreateProplist);
	for (auto& el: n->values)
	{
		llvmValue* key = buildString(el.first.c_str());
		auto args = std::vector<llvmValue*>{
			C4V_Type_LLVM::LLVMTypeTag(C4V_PropList), pl,
			C4V_Type_LLVM::LLVMTypeTag(C4V_String), key };
		el.second->accept(this);
		assert(tmp_expr);
		auto unpacked = UnpackValue(tmp_expr->getVariant());
		assert(unpacked.size() == 2); // needed above
		args.insert(args.end(), unpacked.begin(), unpacked.end());
		m_builder->CreateCall(efunc_SetStructIndex, args);
	}
	tmp_expr = make_unique<C4CompiledValue>(C4V_PropList, pl, n, this);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::NilLit *n) {
	tmp_expr = make_unique<C4CompiledValue>(C4V_Nil, buildBool(false) /* maybe, or maybe not. */, n, this);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::ThisLit *n) {
	assert(context_this); // TODO: Might actually want to throw a proper error
	tmp_expr = make_unique<C4CompiledValue>(C4V_PropList, context_this->getPropList(), n, this); // TODO… Uh… a copy… this looks like a design flaw
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::If *n)
{
	n->cond->accept(this);
	unique_ptr<C4CompiledValue> cond = move(tmp_expr); assert(cond);
	
	BasicBlock* iftrueblock = CreateBlock("ifcondtrue");
	BasicBlock* continuationblock = CreateBlock("ifcont");
	
	if( n->iffalse )
	{
		BasicBlock* iffalseblock = CreateBlock("ifcondfalse");
		m_builder->CreateCondBr( cond->getBool() , iftrueblock , iffalseblock );
		
		// fill negative branch
		SetInsertPoint( iffalseblock );
		n->iffalse->accept(this);
		m_builder->CreateBr( continuationblock );
	}
	else
		m_builder->CreateCondBr( cond->getBool() , iftrueblock , continuationblock );
	
	// Fill the positive branch
	SetInsertPoint( iftrueblock );
	n->iftrue->accept(this);
	m_builder->CreateBr( continuationblock );
	
	// Start inserting in the next block (after the 'If')
	SetInsertPoint( continuationblock );
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::WhileLoop *n)
{
	// Backup old break-continue-context
	BasicBlock* old_break_dest = break_dest;
	BasicBlock* old_continue_dest = continue_dest;
	
	// Create the blocks we will need
	BasicBlock* condition = CreateBlock("whilecond");
	BasicBlock* body = CreateBlock("whilebody");
	BasicBlock* continuation = CreateBlock("whilecont");
	
	// Jump to the condition
	m_builder->CreateBr( condition );
	
	// Open new break/continue-context
	break_dest = continuation;
	continue_dest = condition;
	
	// Fill Condition block
	SetInsertPoint( condition );
	n->cond->accept(this);
	unique_ptr<C4CompiledValue> cond = move(tmp_expr); assert(cond);
	m_builder->CreateCondBr( cond->getBool() , body , continuation );
	
	// Fill While Body
	SetInsertPoint( body );
	n->body->accept(this);
	m_builder->CreateBr( condition );
	
	// Start inserting in the next block (after the 'While')
	SetInsertPoint( continuation );
	
	// Restore old break-continue-context
	break_dest = old_break_dest;
	continue_dest = old_continue_dest;
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::DoLoop *n)
{
	//
	// Basically the same as WhileLoop except for ('m-builder->CreateBr( body )')
	//
	
	// Backup old break-continue-context
	BasicBlock* old_break_dest = break_dest;
	BasicBlock* old_continue_dest = continue_dest;
	
	// Create the blocks we will need
	BasicBlock* condition = CreateBlock("dowhilecond");
	BasicBlock* body = CreateBlock("dowhilebody");
	BasicBlock* continuation = CreateBlock("dowhilecont");
	
	// Jump to the condition
	m_builder->CreateBr( body );
	
	// Open new break/continue-context
	break_dest = continuation;
	continue_dest = condition;
	
	// Fill Condition block
	SetInsertPoint( condition );
	n->cond->accept(this);
	unique_ptr<C4CompiledValue> cond = move(tmp_expr); assert(cond);
	m_builder->CreateCondBr( cond->getBool() , body , continuation );
	
	// Fill While Body
	SetInsertPoint( body );
	n->body->accept(this);
	m_builder->CreateBr( condition );
	
	// Start inserting in the next block (after the 'DoWhile')
	SetInsertPoint( continuation );
	
	// Restore old break-continue-context
	break_dest = old_break_dest;
	continue_dest = old_continue_dest;
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::ForLoop *n)
{
	// Backup old break-continue-context
	BasicBlock* old_break_dest = break_dest;
	BasicBlock* old_continue_dest = continue_dest;
	
	// Create the blocks we will need
	BasicBlock* body = CreateBlock("forbody");
	BasicBlock* loop_start = n->cond ? CreateBlock("forcond") : body;
	BasicBlock* loop_incr = n->incr ? CreateBlock("forstep") : loop_start;
	BasicBlock* continuation = CreateBlock("forcont");
	
	if( n->init )
		n->init->accept(this);
	
	// Jump to the start of the loop
	m_builder->CreateBr( loop_start );
	
	// Open new break/continue-context
	break_dest = continuation;
	continue_dest = loop_incr;
	
	// Fill Loop
	SetInsertPoint( loop_start );
	
	if( n->cond ){
		n->cond->accept(this);
		unique_ptr<C4CompiledValue> cond = move(tmp_expr); assert(cond);
		
		// Create branch into loop body
		m_builder->CreateCondBr( cond->getBool() , body , continuation );
		SetInsertPoint( body );
	}
	
	// Fill Body
	n->body->accept(this);
	
	// Append incrementing function
	if( n->incr ){
		// Jump to the increment part of the for loop
		m_builder->CreateBr( loop_incr );
		
		// Insert incrementation code here
		SetInsertPoint( loop_incr );
		n->incr->accept(this);
	}
	
	// Jump to the start of the loop again!
	m_builder->CreateBr( loop_start );
	
	// Start inserting in the next block (after the 'For')
	SetInsertPoint( continuation );
	
	// Restore old break-continue-context
	break_dest = old_break_dest;
	continue_dest = old_continue_dest;
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::RangeLoop *n)
{
	range_loop_depth++;
	
	if( range_loop_cntrs.size() < range_loop_depth )
	{
		BasicBlock* tmp = CurrentBlock();
		
		// Get First Block of function in which we will prepend
		// the for-range counter variable declaration
		assert( Fn ); assert( Fn->llvmFunc );
		BasicBlock* start_of_func = &Fn->llvmFunc->getEntryBlock();
		SetInsertPoint( start_of_func , start_of_func->begin() );
		range_loop_cntrs.push_back( m_builder->CreateAlloca( C4V_Type_LLVM::get(C4V_Int) , nullptr , "cntr" ) );
		
		// Jump back to editing stuff
		SetInsertPoint( tmp );
	}
	
	// Backup old break-continue-context
	BasicBlock* old_break_dest = break_dest;
	BasicBlock* old_continue_dest = continue_dest;
	
	// Create the blocks we will need
	BasicBlock* iteration = CreateBlock("rangeiter");
	BasicBlock* body = CreateBlock("rangebody");
	BasicBlock* continuation = CreateBlock("rangecont");
	
	// Open new break/continue-context
	break_dest = continuation;
	continue_dest = iteration;
	
	// Initialize Loop counter
	m_builder->CreateStore( buildInt(0) , range_loop_cntrs[range_loop_depth - 1] );
	
	// Emit code for array
	n->cond->accept(this); assert(tmp_expr);
	
	// Create call to array index checker func
	auto unpacked = UnpackValue( tmp_expr->getVariant() );

	// TODO: The unpacked is generated in one block but used in the next. Find out under which circumstances this is legal!
	
	// Branch to iteration routine
	m_builder->CreateBr( iteration );
	SetInsertPoint( iteration );
	
	for(size_t j = 0; j < unpacked.size(); ++j)
	{
		llvmValue* ep = m_builder->CreateGEP(parameter_array[j], std::vector<llvmValue*>{buildInt(0), buildInt(0)});
		m_builder->CreateStore(unpacked[j], ep);
	}
	
	std::vector<llvmValue*> llvm_args;
	for (auto pa: parameter_array)
		llvm_args.push_back(m_builder->CreateGEP(pa, std::vector<llvmValue*>{buildInt(0), buildInt(0)}));
		
	// Load current index
	llvmValue* cur_idx = m_builder->CreateLoad( range_loop_cntrs[range_loop_depth - 1] );
	
	// Push Current Array index to list of arguments
	llvm_args.push_back( cur_idx );
	
	// Call our helper method that will check
	// if the index is within the array and,
	// if yes, read the nth element out of the list
	llvmValue* index_within_range = m_builder->CreateCall(
		efunc_CheckArrayIndex,
		llvm_args
	);
	
	// Increment Array Iterator
	llvmValue* new_idx = m_builder->CreateAdd( cur_idx , buildInt(1) );
	m_builder->CreateStore( new_idx , range_loop_cntrs[range_loop_depth - 1] );
	
	// Create branch into loop body
	m_builder->CreateCondBr( index_within_range , body , continuation );
	SetInsertPoint( body );
	
	//
	// Fill Body
	//
	
	// Get current element
	auto tmp = LoadPackVariant(parameter_array, std::vector<llvmValue*>{buildInt(0), buildInt(0)}, n);
	AulVariable::get(n->var, n, this)->store(tmp);
	
	// Normal Code Here...
	n->body->accept(this);
	
	// Jump to the start of the loop again!
	m_builder->CreateBr( iteration );
	
	// Start inserting in the next block (after the 'For')
	SetInsertPoint( continuation );
	
	// Restore old break-continue-context
	break_dest = old_break_dest;
	continue_dest = old_continue_dest;
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::Break *n)
{
	assert( break_dest );
	m_builder->CreateBr( break_dest );
	SetInsertPoint(CreateBlock("deadcode")); // To not generate the error "Terminator found in the middle of a basic block!"
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::Continue *n)
{
	assert( continue_dest );
	m_builder->CreateBr( continue_dest );
	SetInsertPoint(CreateBlock("deadcode")); // To not generate the error "Terminator found in the middle of a basic block!"
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::VarExpr *n)
{
	tmp_expr = AulVariable::get(n->identifier, n, this);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::UnOpExpr *n)
{
	// TODO: for which type of expression should we call 'visit'?
	n->operand->accept(this);
	unique_ptr<C4CompiledValue> operand = std::move(tmp_expr);
	assert(operand);
	// TODO: what is the semantics of n->op? Which value corresponds to which symbol?

	switch(C4ScriptOpMap[n->op].Code) {
		case AB_Neg:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateNeg(operand->getInt(), "tmp_neg"), n, this);
			break;
		case AB_Not:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, m_builder->CreateNot(operand->getBool(), "tmp_not"), n, this);
			break;
		case AB_BitNot:
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateNot(operand->getInt(), "tmp_bit_not"), n, this);
			break;
		case AB_Inc:
		{
			auto assignable = dynamic_cast<const C4CompiledLValue*>(&*operand);
			if (!assignable)
				throw Error("RValue as operand of ++", n);
			unique_ptr<C4CompiledValue> afterInc = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateAdd(operand->getInt(), buildInt(1), "tmp_inc_add"), n, this);
			assignable->store(afterInc);
			if(C4ScriptOpMap[n->op].Postfix)
				tmp_expr = move(operand);
			else
				tmp_expr = move(afterInc);
			break;
		}
		case AB_Dec:
		{
			auto assignable = dynamic_cast<const C4CompiledLValue*>(&*operand);
			if (!assignable)
				throw Error("RValue as operand of --", n);
			unique_ptr<C4CompiledValue> afterDec = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateSub(operand->getInt(), buildInt(1), "tmp_dec_sub"), n, this);
			assignable->store(afterDec);
			if(C4ScriptOpMap[n->op].Postfix)
				tmp_expr = move(operand);
			else
				tmp_expr = move(afterDec);
			break;
		}
		default:
			break; // TODO;
	}

	return;
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::BinOpExpr *n)
{
	auto opr = C4ScriptOpMap[n->op];
	auto oprcode = opr.Code;
	unique_ptr<C4CompiledValue> left;
	unique_ptr<C4CompiledValue> right;

	// some operations may decide themselves when to compile lhs and rhs
	if(oprcode != AB_JUMPOR && oprcode != AB_JUMPAND && oprcode != AB_JUMPNNIL) {
		n->lhs->accept(this);
		left  = std::move(tmp_expr); assert(left);
		n->rhs->accept(this);
		right = std::move(tmp_expr); assert(right);
	}

	auto compile_eq_cmp = [&](bool positive)
	{
		C4V_Type lt = left->getType();
		if (lt < C4V_FirstPointer && right->getType() == lt)
		{
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, 
				m_builder->CreateICmp(positive? CmpInst::ICMP_EQ : CmpInst::ICMP_NE, left->getValue(lt), right->getValue(lt)), n, this);
		}
		else
		{
			std::vector<llvmValue*> args;
			args << UnpackValue(left->getVariant()) << UnpackValue(right->getVariant());
			llvmValue* val = m_builder->CreateCall(efunc_CompareEquals, args);
			if (!positive)
				val = m_builder->CreateXor(val, buildBool(true));
			tmp_expr = make_unique<C4CompiledValue>(C4V_Bool, val, n, this);
		}
	};


	auto compile_left_true = [&](bool eval_right_on_true)
	{
		// lhs will be evaluated unconditionally
		n->lhs->accept(this);
		auto left = move(tmp_expr); assert(left);
		auto ob = CurrentBlock();

		SetInsertPoint(CreateBlock("tmp_jmpand_rhs"));
		n->rhs->accept(this);
		auto right = move(tmp_expr); assert(right);
		auto rhb = CurrentBlock();

		C4V_Type etype = (left->getType() == right->getType()) ? left->getType() : C4V_Any;

		llvmValue *rhv = right->getValue(etype);
		auto ctb = CreateBlock("tmp_jmpand_continue");
		m_builder->CreateBr(ctb);

		SetInsertPoint(ob);
		auto lhv = left->getValue(etype);
		auto lhc = left->getBool();
		ob = CurrentBlock();
		if(eval_right_on_true)
			m_builder->CreateCondBr(lhc, rhb, ctb);
		else
			m_builder->CreateCondBr(lhc, ctb, rhb);

		SetInsertPoint(ctb);
		llvm::PHINode *pn = m_builder->CreatePHI(C4V_Type_LLVM::get(etype), 2, "tmp_jmpor_phi");
		pn->addIncoming(lhv, ob);
		pn->addIncoming(rhv, rhb);

		tmp_expr = make_unique<C4CompiledValue>(etype, pn, n, this);
	};

	switch(oprcode) {
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
			tmp_expr = make_unique<C4CompiledValue>(C4V_Int, m_builder->CreateCall(efunc_Pow, std::vector<llvmValue*>{left->getInt(), right->getInt()}), n, this);
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
			compile_eq_cmp(true);
			break;
		case AB_NotEqual:
			compile_eq_cmp(false);
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
			compile_left_true(true);
			break;
		}
		case AB_JUMPOR:
		{
			compile_left_true(false);
			break;
		}
		case AB_JUMPNNIL:
		{
			// lhs will be evaluated unconditionally
			n->lhs->accept(this);
			auto left = move(tmp_expr); assert(left);
			auto ob = CurrentBlock();

			SetInsertPoint(CreateBlock("tmp_jmpand_rhs"));
			n->rhs->accept(this);
			auto right = move(tmp_expr); assert(right);
			auto rhb = CurrentBlock();

			C4V_Type etype = (left->getType() == right->getType()) ? left->getType() : C4V_Any;

			llvmValue *rhv = right->getValue(etype);
			auto ctb = CreateBlock("tmp_jmpand_continue");
			m_builder->CreateBr(ctb);

			SetInsertPoint(ob);
			auto lhv = left->getValue(etype);
			auto lhc = left->getIsNil();
			ob = CurrentBlock();
			m_builder->CreateCondBr(lhc, rhb, ctb);

			SetInsertPoint(ctb);
			llvm::PHINode *pn = m_builder->CreatePHI(C4V_Type_LLVM::get(etype), 2, "tmp_jmpor_phi");
			pn->addIncoming(lhv, ob);
			pn->addIncoming(rhv, rhb);

			tmp_expr = make_unique<C4CompiledValue>(etype, pn, n, this);
			break;
		}
		default: /* silence warning. TODO */ break;
	}

	if(opr.Changer) {
		auto assignable = dynamic_cast<const C4CompiledLValue*>(&*left);
		if (!assignable)
			throw Error("RValue on the left hand side of =", n);
		assignable->store(tmp_expr);
	}

}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::AssignmentExpr *n)
{
		n->lhs->accept(this);
		auto lhs = move(tmp_expr);
		n->rhs->accept(this);
		auto rhs = move(tmp_expr);

		assert(lhs);
		auto assignable = dynamic_cast<const C4CompiledLValue*>(&*lhs);
		if (!assignable)
			throw Error("RValue on the left hand side of =", n);
		assignable->store(rhs);
		tmp_expr = move(lhs);
		/* Code dup with VarDecl */
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::SubscriptExpr *n)
{
	// For now, it's fine to always execute the code generated here, even if the subscript is used as a setter.
	// However, at some point, I would like to subclass C4CompiledValue to something that only generates the code if the result is actually used and also already converts the type as necessary.
	// This might also be the solution to the LValue-Problem: That subclass could have a store-method.

	n->object->accept(this);
	auto object = move(tmp_expr); assert(object);
	n->index->accept(this);
	auto index = move(tmp_expr); assert(index);

	std::vector<llvmValue*> args;
	assert(!C4Value(42).CheckConversion(C4V_String)); // Int is not automatically converted to string, so if the index is an int, the object must be an array.
	bool use_array_access_fastpath;
	if (object->getType() == C4V_Array || index->getType() == C4V_Int)
	{
		use_array_access_fastpath = true;
		args.push_back(object->getArray());
		args.push_back(index->getInt());
	}
	else
	{
		use_array_access_fastpath = false;
		for (auto upv: UnpackValue(object->getVariant()))
			args.push_back(upv);
		for (auto upv: UnpackValue(index->getVariant()))
			args.push_back(upv);
	}
	static_assert(C4V_Type_LLVM::variant_member_count == 2, "Next call needs type array to be parameter_array[0].");
	llvmValue* rettp = m_builder->CreateGEP(parameter_array[0], std::vector<llvmValue*>{buildInt(0), buildInt(0)});
	args.push_back(rettp);
	llvmValue* retd = m_builder->CreateCall(use_array_access_fastpath ? efunc_GetArrayIndex : efunc_GetStructIndex, args);
	llvmValue* rett = m_builder->CreateLoad(rettp);
	tmp_expr = std::make_unique<C4CompiledLStruct>(PackVariant({{rett, retd}}, n)->getVariant(), move(object), move(index), n, this);
}

void C4AulCompiler::CodegenAstVisitor::C4CompiledLStruct::store(unique_ptr<C4CompiledValue> &rval) const
{
	std::vector<llvmValue*> args;
	bool use_array_access_fastpath;
	if (strk->getType() == C4V_Array || idx->getType() == C4V_Int)
	{
		use_array_access_fastpath = true;
		args.push_back(strk->getArray());
		args.push_back(idx->getInt());
	}
	else
	{
		// TODO: These unpacks may cause side-effect tainted code generation. Maybe, they should be executed at construction time.
		use_array_access_fastpath = false;
		for (auto upv: compiler->UnpackValue(strk->getVariant()))
			args.push_back(upv);
		for (auto upv: compiler->UnpackValue(idx->getVariant()))
			args.push_back(upv);
	}
	for (auto upv: compiler->UnpackValue(rval->getVariant()))
		args.push_back(upv);
	compiler->m_builder->CreateCall(use_array_access_fastpath ? compiler->efunc_SetArrayIndex : compiler->efunc_SetStructIndex, args);
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::SliceExpr *n)
{
	// Remark: Similar r/lvalue trouble to Subscript

	n->object->accept(this);
	auto object = move(tmp_expr); assert(object);
	n->start->accept(this);
	auto start = move(tmp_expr); assert(start);
	auto lstart = start->getInt();
	n->end->accept(this);
	auto end = move(tmp_expr); assert(end);
	auto lend = end->getInt();
	auto crv = m_builder->CreateCall(
		efunc_GetArraySlice,
		std::vector<llvmValue*>{object->getArray(), lstart, lend}
	);
	auto rval = std::make_unique<C4CompiledValue>(C4V_Array, crv, n, this);
	tmp_expr = std::make_unique<C4CompiledLSlice>(rval->getVariant(), move(object), lstart, lend, n, this);
}

void C4AulCompiler::CodegenAstVisitor::C4CompiledLSlice::store(unique_ptr<C4CompiledValue> &rval) const
{
	std::vector<llvmValue*> args { strk->getArray(), idx1, idx2 };
	for (auto upv: compiler->UnpackValue(rval->getVariant()))
		args.push_back(upv);
	compiler->m_builder->CreateCall(compiler->efunc_SetArraySlice, args);
}


void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::VarDecl *n)
{
	for (const auto &decl: n->decls)
	{
		// Essentially, this is treated like an assignment since the space has been allocated long before.
		if (!decl.init)
			continue;

		auto lhs = AulVariable::get(decl.name, n, this);
		decl.init->accept(this);
		auto rhs = move(tmp_expr);

		assert(lhs);
		auto assignable = dynamic_cast<const C4CompiledLValue*>(&*lhs);
		if (!assignable)
			throw Error("RValue on the left hand side of =", n);
		assignable->store(rhs);
		tmp_expr = move(lhs);
		/* Code dup with AssignmentExpr */
	}
	tmp_expr.reset();
}
void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::FunctionDecl *n)
{
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

	m_builder = make_unique<IRBuilder<>>(llvmcontext);
	llvmFunction* lf = Fn->llvmFunc;
	assert(lf);
	if(!lf)
		throw Error(n, "internal error: unable to find LLVM function definition for %s", n->name.c_str());
	BasicBlock* bb = BasicBlock::Create(llvmcontext, "entrybb", lf);
	m_builder->SetInsertPoint(bb);

	// If this isn't a global function, but there is a global one with
	// the same name, and this function isn't overloading a different
	// one, add the global function to the overload chain
	if (!n->is_global && !Fn->OwnerOverloaded)
	{
		C4AulFunc *global_parent = target_host->Engine->GetFunc(Fn->GetName());
		if (global_parent)
			Fn->SetOverloaded(global_parent);
	}
	assert(parameter_array.size() == 2);
	auto create_pa = [&](size_t idx, llvmType* t, const char* tw) {
		parameter_array[idx] = m_builder->CreateAlloca(llvm::ArrayType::get(t, C4AUL_MAX_Par+1), nullptr, tw);
	};
	create_pa(0, C4V_Type_LLVM::getVariantTypeLLVMType(), "pass_par_types");
	create_pa(1, C4V_Type_LLVM::getVariantVarLLVMType(), "pass_par_vals");
	llvmFunction::arg_iterator argit = lf->arg_begin();
	context_this = make_unique<C4CompiledValue>(C4V_PropList, &*argit, n, this);
	UnpackStoreVariant(context_this->getVariant(), parameter_array, std::vector<llvmValue*>{buildInt(0), buildInt(0)});
	argit++;
	if (Fn->var_type_hints.size() < Fn->GetParCount())
		Warn(target_host, host, n, Fn, "Internal: function %s has no type inference info.", Fn->GetName());
	auto getTypeSafe = [&](std::string vname) { try { return Fn->var_type_hints.at(vname); } catch(const std::out_of_range&) { return C4V_Any; } };
	for (int i = 0; i != Fn->GetParCount(); ++i, ++argit) {
		std::string vname;
		if (i < Fn->ParNamed.iSize) {
			vname = Fn->ParNamed.GetItemUnsafe(i);
		} else {
			char fdst[20];
			snprintf(fdst, 20, "par.%d", i);
			vname = fdst;
		}
		auto par = std::make_unique<C4CompiledValue>(Fn->GetParType()[i], &*argit, n, this);
		fn_var_scope.insert({{vname, AulVariable(vname, getTypeSafe(vname), ::aul::ast::VarDecl::Scope::Func, this, move(par))}});
	}
	for (int i = 0; i < Fn->VarNamed.iSize; i++) {
		const char *vname = Fn->VarNamed.GetItemUnsafe(i);
		fn_var_scope.insert({{vname, AulVariable(vname, getTypeSafe(vname), ::aul::ast::VarDecl::Scope::Func, this)}}); // Caveat: Might do nothing if a parameter with the same name exists. Shouldn't matter…
	}
	assert(argit == lf->arg_end());
	Fn->var_type_hints.clear();

	n->body->accept(this);

	// TODO: nil return with correct return type
	m_builder->CreateRet(C4V_Type_LLVM::defaultValue(Fn->GetRetType()));

	//f->dump();
	llvm::verifyFunction(*lf); // the optimizer should also verify it, but…

	Fn = nullptr;
	fn_var_scope.clear();
	tmp_expr.reset(); // I'd rather get nullpointer errors than stuff failing inside llvm…
	context_this.reset();
	for (auto& pa: parameter_array)
		pa = nullptr;
}

llvmValue* C4AulCompiler::CodegenAstVisitor::constLLVMPointer(void * ptr)
{
	llvmValue* ic = ConstantInt::get(llvmcontext, APInt(sizeof(ptr) * CHAR_BIT, reinterpret_cast<size_t>(ptr), false));
	return m_builder->CreateIntToPtr(ic, llvmType::getInt8PtrTy(llvmcontext));
}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::CallExpr *n)
{
	const char *cname = n->callee.c_str();
	std::vector<unique_ptr<C4CompiledValue>> arg_vals;

	if (n->context)
		n->context->accept(this);
		// TODO
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

	C4AulScriptFunc *sf = callee->SFunc();
	if (sf)
	{
		assert(sf->llvmFunc);
		while (arg_vals.size() > static_cast<size_t>(sf->GetParCount()))
			arg_vals.pop_back();
		while (arg_vals.size() < static_cast<size_t>(sf->GetParCount()))
			arg_vals.push_back(C4CompiledValue::defaultVal(sf->GetParType()[arg_vals.size()], n, this));
		assert(sf->GetParCount() == static_cast<int>(arg_vals.size()));
		std::vector<llvmValue*> llvm_args(arg_vals.size()+1, nullptr);
		llvm_args[0] = context_this->getPropList();
		for(int i = 0; i < sf->GetParCount(); i++)
			llvm_args[i+1] = arg_vals[i]->getValue(sf->GetParType()[i]);
		assert(sf->GetRetType() != C4V_Nil); // For now, I don't know how to deal with that
		auto llvmret = checkCompile(m_builder->CreateCall(sf->llvmFunc, llvm_args));
		tmp_expr = make_unique<C4CompiledValue>(sf->GetRetType(), llvmret, n, this);
	}
	else
	{
		LogF("Calling %s at %p", callee->GetName(), callee);
		auto llvm_args = std::vector<llvmValue*>{
			constLLVMPointer(callee), // TODO: Create named constants or annotate in some other way to ease reading the IR a bit…
			ConstantInt::get(llvmcontext, APInt(32, arg_vals.size(), false))
		};
		for (auto pa: parameter_array)
			llvm_args.push_back(m_builder->CreateGEP(pa, std::vector<llvmValue*>{buildInt(0), buildInt(0)}));
		std::vector<C4V_Type_LLVM::UnpackedVariant> unpackeds;
		// getVariant may generate code, which in turn might use the parameter_array(s). Thus, unpack first and then write into those. (This might lead to very ugly bugs.)
		for (auto& arg_val: arg_vals)
			unpackeds.push_back(UnpackValue(arg_val->getVariant()));
		for (size_t i = 0; i < std::min<size_t>(unpackeds.size(), callee->GetParCount()); ++i)
		{
			for(size_t j = 0; j < unpackeds[i].size(); ++j)
			{
				llvmValue* ep = m_builder->CreateGEP(parameter_array[j], std::vector<llvmValue*>{buildInt(0), buildInt(i+1)});
				m_builder->CreateStore(unpackeds[i][j], ep);
			}
		}
		checkCompile(m_builder->CreateCall(efunc_CallByPFunc, llvm_args));
		// I'm assuming that Fn->GetRetType() is C4V_Any. If this wasn't the case, we might want to do something more efficient (similarly above).
		tmp_expr = LoadPackVariant(parameter_array, std::vector<llvmValue*>{buildInt(0), buildInt(0)}, n);
	}
	assert(tmp_expr);

}

void C4AulCompiler::CodegenAstVisitor::visit(const ::aul::ast::Return *n)
{
	// Note: There doesn't seem to be a good way to find out whether this is return; or return (foobar);
	tmp_expr.reset();
	n->value->accept(this);
	if(!tmp_expr)
		tmp_expr = C4CompiledValue::defaultVal(C4V_Nil, n, this);
	m_builder->CreateRet(tmp_expr->getValue(Fn->GetRetType()));
	SetInsertPoint(CreateBlock("deadcode"));
}

// TODO: Right place for these?
C4V_Type CheckArrayAccess(C4Value& Structure, C4Value& Index)
{
	if (Structure.CheckConversion(C4V_Array))
	{
		if (!Index.CheckConversion(C4V_Int))
			throw C4AulExecError(FormatString("array access: index of type %s, but expected int", Index.GetTypeName()).getData());
		return C4V_Array;
	}
	else if (Structure.CheckConversion(C4V_PropList))
	{
		if (!Index.CheckConversion(C4V_String))
			throw C4AulExecError(FormatString("proplist access: index of type %s, but expected string", Index.GetTypeName()).getData());
		return C4V_PropList;
	}
	else
		throw C4AulExecError(FormatString("can't access %s as array or proplist", Structure.GetTypeName()).getData());
}
extern "C" {
	void LLVMAulPFuncCall(uint8_t * func_i8, uint32_t par_count, C4V_Type* types, C4V_Data* data)
	{
		C4AulFunc *func = reinterpret_cast<C4AulFunc *>(func_i8);

		C4Value pars[C4AUL_MAX_Par+1];
		for(uint32_t i = 0; i < std::min<uint32_t>(par_count, func->GetParCount()) + 1; ++i)
			pars[i] = AulLLVMToC4Value(types[i], data[i]);
		C4Value rv = func->Exec(pars[0].getPropList(), pars+1, false);
		std::tie(types[0], data[0]) = C4ValueToAulLLVM(rv);
	}

	C4V_Data LLVMAulCreateValueArray(int32_t reserved_size)
	{
		C4Value rvh;
		rvh.SetArray(new C4ValueArray(reserved_size));
		assert(rvh.GetType() == C4V_Array);
		return C4ValueToAulLLVM(rvh).second;
		// Side-effect of pulling the array through C4Value: The refcount is increased and decreased once, putting it into the deletion marker.
	}
	C4V_Data LLVMAulCreateProplist()
	{
		C4Value rvh;
		rvh.SetPropList(C4PropList::New());
		assert(rvh.GetType() == C4V_PropList);
		return C4ValueToAulLLVM(rvh).second;
	}

	void LLVMAulSetStructElement(C4V_Type ct, C4V_Data cd, C4V_Type it, C4V_Data id, C4V_Type dt, C4V_Data dd)
	{
		C4Value c = AulLLVMToC4Value(ct, cd), i = AulLLVMToC4Value(it, id), v = AulLLVMToC4Value(dt, dd);
		C4V_Type acc_type = CheckArrayAccess(c, i);
		switch (acc_type) {
			case C4V_Array: c.getArray()->SetItem(i.getInt(), v); break;
			case C4V_PropList: {
				C4PropList *pPropList = c.getPropList();
				if (pPropList->IsFrozen())
					throw C4AulExecError("proplist write: proplist is readonly");
				pPropList->SetPropertyByS(i.getStr(), v);
				break;
			}
			default: assert(!"reachable");
		}
	}
	void LLVMAulSetArrayElement(C4V_Data array, int32_t idx, C4V_Type dt, C4V_Data dd)
	{
		// TODO: 0 checks
		array.Array->SetItem(idx, AulLLVMToC4Value(dt, dd));
	}
	void LLVMAulSetArraySlice(C4V_Data array_dst, int32_t idx1, int32_t idx2, C4V_Type srct, C4V_Data srcd) {
		C4Value dst;
		dst.SetArray(array_dst.Array);
		C4Value src = AulLLVMToC4Value(srct, srcd);
		dst.getArray()->SetSlice(idx1, idx2, src);
	}

	C4V_Data LLVMAulGetArrayElement(C4V_Data array, int32_t idx, C4V_Type* tret)
	{
		C4V_Data rv;
		std::tie(*tret, rv) = C4ValueToAulLLVM(array.Array->GetItem(idx));
		return rv;
	}
	C4V_Data LLVMAulGetStructElement(C4V_Type ct, C4V_Data cd, C4V_Type it, C4V_Data id, C4V_Type* tret)
	{
		C4Value c = AulLLVMToC4Value(ct, cd);
		C4Value i = AulLLVMToC4Value(it, id);
		C4Value v;
		C4V_Type acc_type = CheckArrayAccess(c, i);
		switch (acc_type) {
			case C4V_Array: v = c.getArray()->GetItem(i.getInt()); break;
			case C4V_PropList: {
				C4PropList *pPropList = c.getPropList();
				if (!pPropList->GetPropertyByS(i.getStr(), &v))
					v.Set0();
				break;
			}
			default: assert(!"reachable");
		}
		C4V_Data rv;
		std::tie(*tret, rv) = C4ValueToAulLLVM(v);
		return rv;
	}
	C4V_Data LLVMAulGetArraySlice(C4V_Data array, int32_t idx1, int32_t idx2)
	{
		C4Value rethlp;
		rethlp.SetArray(array.Array->GetSlice(idx1, idx2));
		assert(rethlp.GetType() == C4V_Array);
		return C4ValueToAulLLVM(rethlp).second;
	}
	bool LLVMAulCheckArrayIndex(C4V_Type* type, C4V_Data* data, int32_t idx )
	{
		C4Value array = AulLLVMToC4Value(*type, *data);
		
		// Is Arraxy?
		if( !array.CheckConversion(C4V_Array) )
			throw C4AulExecError(FormatString("For range expected array, got %s", array.GetTypeName()).getData());
		
		// Check Index
		if( idx >= array.getArray()->GetSize() )
			return false;
		
		std::tie(*type, *data) = C4ValueToAulLLVM(array.getArray()->GetItem(idx));
		
		return true;
	}
	
	bool LLVMAulCompareEquals(C4V_Type t1, C4V_Data d1, C4V_Type t2, C4V_Data d2)
	{
		C4Value v1 = AulLLVMToC4Value(t1, d1);
		C4Value v2 = AulLLVMToC4Value(t2, d2);
		return v1 == v2;
	}

	// Not to be called from LLVM, but to be called instead of LLVM-Generated code.
	void LLVMAulDummyFunc(C4V_Type* t, C4V_Data* d) {
		C4Value v; v.Set0();
		std::tie(t[0], d[0]) = C4ValueToAulLLVM(v);
	}
}

void C4AulCompiler::CodegenAstVisitor::ExternDecls() {
	efunc_CallByPFunc = RegisterEngineFunction(LLVMAulPFuncCall, "Engine.LLVMAulPFuncCall", mod, jit); // Calling engine functions
	efunc_ValueConversionFunc = RegisterEngineFunction(InternalValueConversionFunc, "Engine.LLVMVarTypeConv", mod, jit); // Converting between runtime types
	efunc_ValueConversionFunc->addFnAttr(llvm::Attribute::ReadNone);
	efunc_CreateValueArray = RegisterEngineFunction(LLVMAulCreateValueArray, "Engine.CreateArray", mod, jit);
	efunc_CreateProplist = RegisterEngineFunction(LLVMAulCreateProplist, "Engine.CreatePropList", mod, jit);
	efunc_GetArrayIndex = RegisterEngineFunction(LLVMAulGetArrayElement, "Engine.GetArrayIndex", mod, jit);
	efunc_GetArrayIndex->addFnAttr(llvm::Attribute::ReadOnly);
	efunc_GetArraySlice = RegisterEngineFunction(LLVMAulGetArraySlice, "Engine.GetArraySlice", mod, jit);
	efunc_GetArraySlice->addFnAttr(llvm::Attribute::ReadOnly);
	efunc_GetStructIndex = RegisterEngineFunction(LLVMAulGetStructElement, "Engine.GetStructIndex", mod, jit);
	efunc_GetStructIndex->addFnAttr(llvm::Attribute::ReadOnly);
	efunc_SetArrayIndex = RegisterEngineFunction(LLVMAulSetArrayElement, "Engine.SetArrayIndex", mod, jit);
	efunc_SetArraySlice = RegisterEngineFunction(LLVMAulSetArraySlice, "Engine.SetArraySlice", mod, jit);
	efunc_SetStructIndex = RegisterEngineFunction(LLVMAulSetStructElement, "Engine.SetStructIndex", mod, jit);
	efunc_CheckArrayIndex = RegisterEngineFunction(LLVMAulCheckArrayIndex, "Engine.CheckArrayIndex", mod, jit);
	efunc_CompareEquals = RegisterEngineFunction(LLVMAulCompareEquals, "Engine.CompareEquals", mod, jit);
	efunc_CompareEquals->addFnAttr(llvm::Attribute::ReadOnly);
	efunc_Pow = RegisterEngineFunction(Pow, "EngineCPP.Pow", mod, jit); // TODO: Check linkage/calling convention accross platforms
	efunc_Pow->addFnAttr(llvm::Attribute::ReadNone);
}

void C4AulCompiler::CodegenAstVisitor::FnDecls() {
	ExternDecls();

	// Declarations for script functions
	for (const auto& func: ::ScriptEngine.FuncLookUp) {
		C4AulScriptFunc *sf = func->SFunc();
		if(!sf)
			continue;
		{
			std::vector<llvmType*> parTypes{C4V_Type_LLVM::get(C4V_PropList)};
			for(int i = 0; i < sf->GetParCount(); ++i)
				parTypes.push_back(C4V_Type_LLVM::get(sf->GetParType()[i]));
			FunctionType *ft = FunctionType::get(C4V_Type_LLVM::get(sf->GetRetType()), parTypes, false);
			sf->llvmFunc = checkCompile(llvmFunction::Create(ft, llvmFunction::PrivateLinkage, func->GetName(), mod.get()));
			llvmFunction::arg_iterator argit = sf->llvmFunc->arg_begin();
			argit->setName("Engine.this");
			argit++;
			for (int i = 0; i < sf->ParNamed.iSize; ++argit, ++i) {
				argit->setName(std::string(sf->ParNamed.GetItemUnsafe(i)) + ".par");
			}
			sf->llvmImpl = LLVMAulDummyFunc; // Hopefully overwritten…
		}

		{
			//also add a delegate with simple parameter types for easy external calls
			FunctionType *dft = FunctionType::get(llvmType::getVoidTy(llvmcontext), std::vector<llvmType*>{
				llvm::PointerType::getUnqual(C4V_Type_LLVM::getVariantTypeLLVMType()),
				llvm::PointerType::getUnqual(C4V_Type_LLVM::getVariantVarLLVMType())
			},false);
			auto llvmDelegate = checkCompile(llvmFunction::Create(dft, llvmFunction::ExternalLinkage, std::string(func->GetName()) + ".delegate", mod.get()));
			m_builder = make_unique<IRBuilder<>>(llvmcontext);
			SetInsertPoint(CreateBlock(llvmDelegate));
			auto argv = make_value_vector(llvmDelegate->args());
			std::vector<llvmValue*> delegate_args{LoadPackVariant(argv, std::vector<llvmValue*>{buildInt(0)})->getPropList()};
			for (int i = 0; i < func->GetParCount(); ++i) {
				delegate_args.push_back(LoadPackVariant(argv, std::vector<llvmValue*>{buildInt(i+1)})->getValue(sf->GetParType()[i]));
			}
			auto dlgret = make_unique<C4CompiledValue>(sf->GetRetType(), m_builder->CreateCall(sf->llvmFunc, delegate_args), nullptr, this);
			UnpackStoreVariant(dlgret->getVariant(), argv, std::vector<llvmValue*>{buildInt(0)});
			m_builder->CreateRet(nullptr);
			sf->llvmDlgName = llvmDelegate->getName();
			assert(sf->llvmDlgName != "");
		}
	}
}

void C4AulCompiler::CodegenAstVisitor::finalize()
{
	assert(jit);
	jit->addModule(move(mod));
	for(const auto& func: ::ScriptEngine.FuncLookUp) {
		C4AulScriptFunc *sf = func->SFunc();
		if(!sf)
			continue;
		FinalizeFunc(sf, sf->llvmDlgName);
	}
}
	
void C4AulCompiler::CodegenAstVisitor::FinalizeFunc(C4AulScriptFunc *sf, const std::string& name) {
	sf->llvmFunc = nullptr; // now that we moved the module, who knows what will happen to the pointer
	sf->jit = jit;
	auto symbol = jit->findSymbol(name);
	assert(symbol);
	sf->llvmImpl = reinterpret_cast<decltype(sf->llvmImpl)>(symbol.getAddress());
	assert(sf->llvmImpl);
	if (!sf->llvmImpl) {
		sf->llvmImpl = LLVMAulDummyFunc;
		throw Error("Internal Error: Could not synthesize code for %s.", sf->GetName());
	}
}

void C4AulCompiler::CodegenAstVisitor::StandaloneCompile(C4AulScriptFunc *func, const ::aul::ast::Function *def)
{
	func->llvmImpl = LLVMAulDummyFunc;
	func->llvmFunc = nullptr;
	std::string name = func->GetName();
	m_builder = make_unique<IRBuilder<>>(llvmcontext);
	FunctionType *ft = FunctionType::get(llvmType::getVoidTy(llvmcontext), std::vector<llvmType*>{},false);
	auto lf = checkCompile(llvmFunction::Create(ft, llvmFunction::ExternalLinkage, name, mod.get()));
	BasicBlock* bb = BasicBlock::Create(llvmcontext, "entrybb", lf);
	SetInsertPoint(bb);
	def->body->accept(this);
	DumpLLVM();
	assert(jit);
	jit->addModule(move(mod));
	FinalizeFunc(func, func->GetName());
}

static_assert(C4AUL_MAX_Par <= std::numeric_limits<int>::max(), "Use of int in loops iterating over parameters."); // I mean… yeah. This is pretty much given.
llvm::LLVMContext llvmcontext;
