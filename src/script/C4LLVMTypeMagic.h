#ifndef C4LLVMTYPEMAGIC_H_
#define C4LLVMTYPEMAGIC_H_

#include "script/C4Value.h"
#include "script/C4LLVMJIT.h"
#include <llvm/IR/IRBuilder.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/IR/Module.h> // Surprisingly required for llvm::Function

extern llvm::LLVMContext llvmcontext;
template<typename T> llvm::Type* CPPTypeToLLVM();
// Just the things I need 
template<> llvm::Type* CPPTypeToLLVM<bool>() { return llvm::Type::getIntNTy(llvmcontext, 1); };
template<> llvm::Type* CPPTypeToLLVM<int32_t>() { return llvm::Type::getIntNTy(llvmcontext, 32); };
template<> llvm::Type* CPPTypeToLLVM<uint32_t>() { return CPPTypeToLLVM<int32_t>(); };
template<> llvm::Type* CPPTypeToLLVM<int64_t>() { return llvm::Type::getIntNTy(llvmcontext, 64); };
template<> llvm::Type* CPPTypeToLLVM<C4V_Type>() { return llvm::Type::getIntNTy(llvmcontext, CHAR_BIT * sizeof(C4V_Type)); };
template<> llvm::Type* CPPTypeToLLVM<C4V_Data>() { return llvm::Type::getIntNTy(llvmcontext, CHAR_BIT * sizeof(C4V_Data)); };
template<> llvm::Type* CPPTypeToLLVM<C4V_Type*>() { return llvm::PointerType::getUnqual(CPPTypeToLLVM<C4V_Type>()); };
template<> llvm::Type* CPPTypeToLLVM<C4V_Data*>() { return llvm::PointerType::getUnqual(CPPTypeToLLVM<C4V_Data>()); };
template<> llvm::Type* CPPTypeToLLVM<uint8_t*>() { return llvm::Type::getInt8PtrTy(llvmcontext); };
template<> llvm::Type* CPPTypeToLLVM<void*>() { return llvm::Type::getInt8PtrTy(llvmcontext); } // "Note that LLVM does not permit pointers to void (void*) [...]. Use i8* instead."
template<> llvm::Type* CPPTypeToLLVM<void>() { return llvm::Type::getVoidTy(llvmcontext); }

template<typename RetType, typename... ArgTypes>
inline llvm::Function* RegisterEngineFunction(
	RetType(*f)(ArgTypes...), 
	std::string name, 
	std::unique_ptr<llvm::Module>& mod, 
	std::shared_ptr<C4JIT>& jit)
{
	assert(mod && jit);
	llvm::Function* rv;
	auto at = std::vector<llvm::Type*>{CPPTypeToLLVM<ArgTypes>()...}; // magic happens here
	llvm::FunctionType *ft = llvm::FunctionType::get(CPPTypeToLLVM<RetType>(), at, false/* I doubt that any of this would work with varargs anyway */);
	rv = llvm::Function::Create(ft, llvm::Function::AvailableExternallyLinkage, name, mod.get()); // the Linkage seems to affect the calling… and I have no idea what is correct…
	jit->addGlobalMapping(name, reinterpret_cast<llvm::JITTargetAddress>(f));
	assert(rv);
	return rv;
}

template<typename Z, typename X>
typename std::enable_if<std::is_convertible<X,Z>::value || std::is_assignable<Z,X>::value, Z>::type
deref_to(X && x) { return x; }
template<typename Z, typename X>
typename std::enable_if<!std::is_convertible<X,Z>::value && !std::is_assignable<Z,X>::value, Z>::type
deref_to(X && x) { return deref_to<Z>(*std::forward<X>(x)); }

template<typename T> std::vector<llvm::Value*> make_value_vector(T&& t) {
	std::vector<llvm::Value*> r;
	auto it = t.begin();
	while (it != t.end())
		r.push_back(&*(it++));
	return r;
}


#endif
