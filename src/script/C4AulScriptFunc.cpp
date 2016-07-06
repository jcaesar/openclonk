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

C4AulScriptFunc::C4AulScriptFunc(C4PropListStatic * Parent, C4ScriptHost *pOrgScript, const char *pName, const char *Script):
		C4AulFunc(Parent, pName),
		OwnerOverloaded(NULL),
		llvmFunc(nullptr),
		ParCount(0),
		Script(Script),
		pOrgScript(pOrgScript),
		tProfileTime(0)
{
	for (int i = 0; i < C4AUL_MAX_Par; i++) ParType[i] = C4V_Any;
	AddBCC(AB_EOFN);
}

C4AulScriptFunc::C4AulScriptFunc(C4PropListStatic * Parent, const C4AulScriptFunc &FromFunc):
		C4AulFunc(Parent, FromFunc.GetName()),
		OwnerOverloaded(NULL),
		llvmFunc(nullptr),
		ParCount(FromFunc.ParCount),
		Script(FromFunc.Script),
		VarNamed(FromFunc.VarNamed),
		ParNamed(FromFunc.ParNamed),
		pOrgScript(FromFunc.pOrgScript),
		tProfileTime(0)
{
	for (int i = 0; i < C4AUL_MAX_Par; i++)
		ParType[i] = FromFunc.ParType[i];
	AddBCC(AB_EOFN);
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

void C4AulScriptFunc::AddBCC(C4AulBCCType eType, intptr_t X, const char * SPos)
{
	// store chunk
	Code.emplace_back(eType, X);
	PosForCode.push_back(SPos);
}

void C4AulScriptFunc::RemoveLastBCC()
{
	Code.pop_back();
	PosForCode.pop_back();
}

void C4AulScriptFunc::ClearCode()
{
	while(Code.size() > 0)
		RemoveLastBCC();
	// This function is now broken until an AddBCC call
}

int C4AulScriptFunc::GetLineOfCode(C4AulBCC * bcc)
{
	return SGetLine(pOrgScript ? pOrgScript->GetScript() : Script, PosForCode[bcc - &Code[0]]);
}

C4AulBCC * C4AulScriptFunc::GetCode()
{
	assert(!Code.empty());
	return &Code[0];
}

C4Value C4AulScriptFunc::Exec(C4PropList * p, C4Value pPars[], bool fPassErrors)
{
	C4V_Type retpar_types[C4AUL_MAX_Par];
	C4V_Data retpar_data [C4AUL_MAX_Par];
	for (int i = 0; i < GetParCount(); i++) {
		retpar_types[i] = pPars[i].GetType();
		retpar_data [i] = pPars[i].GetData();
	}
	// TODO: Catch errors on fPassErrors
	llvmImpl(retpar_types, retpar_data);
	C4Value rv;
	rv.Set(retpar_data[0], retpar_types[0]);
	return rv;
}
