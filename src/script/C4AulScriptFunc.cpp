/*
 * OpenClonk, http://www.openclonk.org
 *
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
#include "script/C4AulScriptFunc.h"

#include "script/C4AulExec.h"
#include "script/C4ScriptHost.h"
#include "script/C4Value.h"
#include <llvm/ExecutionEngine/GenericValue.h>
#include <llvm/IR/Function.h>
#ifndef DEBUG_BYTECODE_DUMP
#define DEBUG_BYTECODE_DUMP 0
#endif

C4AulScriptFunc::C4AulScriptFunc(C4PropListStatic * Parent, C4ScriptHost *pOrgScript, const char *pName, const char *Script):
		C4AulFunc(Parent, pName),
		OwnerOverloaded(nullptr),
		llvmFunc(nullptr),
		ParCount(0),
		Script(Script),
		pOrgScript(pOrgScript),
		tProfileTime(0)
{
	 for (auto & i : ParType) i = C4V_Any;
}

C4AulScriptFunc::C4AulScriptFunc(C4PropListStatic * Parent, const C4AulScriptFunc &FromFunc):
		C4AulFunc(Parent, FromFunc.GetName()),
		OwnerOverloaded(nullptr),
		llvmFunc(nullptr),
		ParCount(FromFunc.ParCount),
		Script(FromFunc.Script),
		VarNamed(FromFunc.VarNamed),
		ParNamed(FromFunc.ParNamed),
		pOrgScript(FromFunc.pOrgScript),
		tProfileTime(0),
		var_type_hints(FromFunc.var_type_hints)
{
	for (int i = 0; i < C4AUL_MAX_Par; i++)
		ParType[i] = FromFunc.ParType[i];
}

C4AulScriptFunc::~C4AulScriptFunc()
{
	if (OwnerOverloaded) OwnerOverloaded->DecRef();
	ClearCode();
}

void C4AulScriptFunc::SetOverloaded(C4AulFunc * f)
{
	if (OwnerOverloaded) OwnerOverloaded->DecRef();
	OwnerOverloaded = f;
	if (f) f->IncRef();
}

void C4AulScriptFunc::ClearCode()
{
	// TODO: Is there anything we need to clean up?
}


#include "script/C4ValueMagic.h"

C4Value C4AulScriptFunc::Exec(C4PropList * p, C4Value pPars[], bool fPassErrors)
{
	// TODO: Handle context p
	C4V_Type retpar_types[C4AUL_MAX_Par+1];
	C4V_Data retpar_data [C4AUL_MAX_Par+1];
	std::tie(retpar_types[0], retpar_data[0]) = C4ValueToAulLLVM(C4Value(p));
	for (int i = 0; i < GetParCount(); i++)
		std::tie(retpar_types[i+1], retpar_data[i+1]) = C4ValueToAulLLVM(pPars[i]);
	// TODO: Catch errors on fPassErrors
	assert(llvmImpl);
	llvmImpl(retpar_types, retpar_data);
	return AulLLVMToC4Value(retpar_types[0], retpar_data[0]);
}

void C4AulScriptFunc::DumpByteCode()
{
	if (DEBUG_BYTECODE_DUMP && llvmFunc)
	{
		llvmFunc->dump();
	}
}
