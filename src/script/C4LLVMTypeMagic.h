#ifndef C4LLVMTYPEMAGIC_H_
#define C4LLVMTYPEMAGIC_H_

#include "script/C4Value.h"
#include <llvm/IR/IRBuilder.h>
#include <llvm/ExecutionEngine/ExecutionEngine.h>
#include <llvm/IR/Module.h> // Surprisingly required for llvm::Function

template<typename T> llvm::Type* CPPTypeToLLVM();
// Just the things I need 
template<> llvm::Type* CPPTypeToLLVM<int32_t>() { return llvm::Type::getIntNTy(llvm::getGlobalContext(), 32); };
template<> llvm::Type* CPPTypeToLLVM<uint32_t>() { return CPPTypeToLLVM<int32_t>(); };
template<> llvm::Type* CPPTypeToLLVM<int64_t>() { return llvm::Type::getIntNTy(llvm::getGlobalContext(), 64); };
template<> llvm::Type* CPPTypeToLLVM<C4V_Type>() { return llvm::Type::getIntNTy(llvm::getGlobalContext(), CHAR_BIT * sizeof(C4V_Type)); };
template<> llvm::Type* CPPTypeToLLVM<C4V_Data>() { return llvm::Type::getIntNTy(llvm::getGlobalContext(), CHAR_BIT * sizeof(C4V_Data)); };
template<> llvm::Type* CPPTypeToLLVM<C4V_Type*>() { return llvm::PointerType::getUnqual(CPPTypeToLLVM<C4V_Type>()); };
template<> llvm::Type* CPPTypeToLLVM<C4V_Data*>() { return llvm::PointerType::getUnqual(CPPTypeToLLVM<C4V_Data>()); };
template<> llvm::Type* CPPTypeToLLVM<uint8_t*>() { return llvm::Type::getInt8PtrTy(llvm::getGlobalContext()); };
template<> llvm::Type* CPPTypeToLLVM<void*>() { return llvm::Type::getInt8PtrTy(llvm::getGlobalContext()); } // "Note that LLVM does not permit pointers to void (void*) [...]. Use i8* instead."
template<> llvm::Type* CPPTypeToLLVM<void>() { return llvm::Type::getVoidTy(llvm::getGlobalContext()); }

template<typename RetType, typename... ArgTypes, typename NameT>
inline llvm::Function* RegisterEngineFunction(RetType(*f)(ArgTypes...), NameT name, llvm::Module* mod, llvm::ExecutionEngine* ee) {
	llvm::Function* rv;
	auto at = std::vector<llvm::Type*>{CPPTypeToLLVM<ArgTypes>()...}; // magic happens here
	llvm::FunctionType *ft = llvm::FunctionType::get(CPPTypeToLLVM<RetType>(), at, false/* I doubt that any of this would work with varargs anyway */);
	rv = llvm::Function::Create(ft, llvm::Function::ExternalLinkage, name, mod);
	assert(rv);
	ee->addGlobalMapping(rv, reinterpret_cast<void*>(f));
	return rv;
}

#endif
