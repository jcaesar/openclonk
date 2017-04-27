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
// executes script functions

#include "C4Include.h"
#include "script/C4AulExec.h"

#include "script/C4Aul.h"
#include "script/C4AulScriptFunc.h"
#include "script/C4AulDebug.h"
#include "object/C4Object.h"
#include "config/C4Config.h"
#include "game/C4Game.h"
#include "lib/C4Log.h"
#include "control/C4Record.h"
#include "object/C4Def.h"
#include "script/C4ScriptHost.h"
#include <algorithm>

C4AulExec AulExec;

C4AulExecError::C4AulExecError(const char *szError)
{
	assert(szError);
	// direct error message string
	sMessage.Copy(szError ? szError : "(no error message)");
}

StdStrBuf C4AulScriptContext::ReturnDump(StdStrBuf Dump)
{
	assert(!"TODO");
	return Dump;
}

void C4AulScriptContext::dump(StdStrBuf Dump)
{
	// Log it
	DebugLog(ReturnDump(Dump).getData());
}

void C4AulExec::LogCallStack()
{
	for (C4AulScriptContext *pCtx = pCurCtx; pCtx >= Contexts; pCtx--)
		pCtx->dump(StdStrBuf(" by: "));
}

C4String *C4AulExec::FnTranslate(C4PropList * _this, C4String *text)
{
#define ReturnIfTranslationAvailable(script, key) do \
{ \
	const auto &s = script; \
	const auto &k = key; \
	if (s) \
	{ \
		try \
		{ \
			return ::Strings.RegString(s->Translate(k).c_str()); \
		} \
		catch (C4LangStringTable::NoSuchTranslation &) {} \
	} \
} while(0)

	if (!text || text->GetData().isNull()) return nullptr;
	// Find correct script: translations of the context if possible, containing script as fallback
	if (_this && _this->GetDef())
		ReturnIfTranslationAvailable(&(_this->GetDef()->Script), text->GetCStr());
	ReturnIfTranslationAvailable(AulExec.pCurCtx[0].Func->pOrgScript, text->GetCStr());

	// No translation available, log
	DebugLogF("WARNING: Translate: no translation for string \"%s\"", text->GetCStr());
	// Trace
	AulExec.LogCallStack();
	return text;
#undef ReturnIfTranslationAvailable
}

bool C4AulExec::FnLogCallStack(C4PropList * _this)
{
	AulExec.LogCallStack();
	return true;
}

void C4AulExec::ClearPointers(C4Object * obj)
{
	for (C4AulScriptContext *pCtx = pCurCtx; pCtx >= Contexts; pCtx--)
	{
		if (pCtx->Obj == obj)
			pCtx->Obj = nullptr;
	}
}

C4Value C4AulExec::Exec(C4AulScriptFunc *pSFunc, C4PropList * p, C4Value *pnPars, bool fPassErrors)
{
	// Save start context
	C4AulScriptContext *pOldCtx = pCurCtx;
	C4Value *pPars = pCurVal + 1;
	try
	{
		// Push parameters
		assert(pnPars);
		for (int i = 0; i < pSFunc->GetParCount(); i++)
			PushValue(pnPars[i]);

		// Push a new context
		C4AulScriptContext ctx;
		ctx.tTime = 0;
		ctx.Obj = p;
		ctx.Return = nullptr;
		ctx.Pars = pPars;
		ctx.Func = pSFunc;
		ctx.CPos = nullptr;
		PushContext(ctx);

		// Execute
		return pSFunc->Exec(p, pnPars, fPassErrors);
	}
	catch (C4AulError &e)
	{
		if (!fPassErrors)
			::ScriptEngine.GetErrorHandler()->OnError(e.what());
		// Unwind stack
		// TODO: The stack dump should be passed to the error handler somehow
		while (pCurCtx > pOldCtx)
		{
			pCurCtx->dump(StdStrBuf(" by: "));
			PopContext();
		}
		PopValuesUntil(pPars - 1);
		// Pass?
		if (fPassErrors)
			throw;
		// Trace
		LogCallStack();
	}

	// Return nothing
	return C4VNull;
}

void C4AulExec::StartTrace()
{
	if (iTraceStart < 0)
		iTraceStart = ContextStackSize();
}

void C4AulExec::StartProfiling(C4ScriptHost *pProfiledScript)
{
	// stop previous profiler run
	if (fProfiling) StopProfiling();
	fProfiling = true;
	// resets profling times and starts recording the times
	this->pProfiledScript = pProfiledScript;
	C4TimeMilliseconds tNow = C4TimeMilliseconds::Now();
	tDirectExecStart = tNow; // in case profiling is started from DirectExec
	tDirectExecTotal = 0;
	for (C4AulScriptContext *pCtx = Contexts; pCtx <= pCurCtx; ++pCtx)
		pCtx->tTime = tNow;
}

void C4AulExec::PushContext(const C4AulScriptContext &rContext)
{
	if (pCurCtx >= Contexts + MAX_CONTEXT_STACK - 1)
		throw C4AulExecError("context stack overflow");
	*++pCurCtx = rContext;
	// Trace?
	if (iTraceStart >= 0)
	{
		StdStrBuf Buf("T");
		Buf.AppendChars('>', ContextStackSize() - iTraceStart);
		pCurCtx->dump(Buf);
	}
	// Profiler: Safe time to measure difference afterwards
	if (fProfiling) pCurCtx->tTime = C4TimeMilliseconds::Now();
}

void C4AulExec::PopContext()
{
	if (pCurCtx < Contexts)
		throw C4AulExecError("internal error: context stack underflow");
	// Profiler adding up times
	if (fProfiling)
	{
		uint32_t dt = C4TimeMilliseconds::Now() - pCurCtx->tTime;
		if (pCurCtx->Func)
			pCurCtx->Func->tProfileTime += dt;
	}
	// Trace done?
	if (iTraceStart >= 0)
	{
		if (ContextStackSize() <= iTraceStart)
		{
			iTraceStart = -1;
		}
	}
	pCurCtx--;
}

void C4AulProfiler::StartProfiling(C4ScriptHost *pScript)
{
	AulExec.StartProfiling(pScript);
	if(pScript)
		ResetTimes(pScript->GetPropList());
	else
		ResetTimes();
}

void C4AulProfiler::StopProfiling()
{
	if (!AulExec.IsProfiling()) return;
	AulExec.StopProfiling();
	// collect profiler times
	C4AulProfiler Profiler;
	Profiler.CollectEntry(nullptr, AulExec.tDirectExecTotal);
	if(AulExec.pProfiledScript)
		Profiler.CollectTimes(AulExec.pProfiledScript->GetPropList());
	else
		Profiler.CollectTimes();
	Profiler.Show();
}

void C4AulProfiler::CollectEntry(C4AulScriptFunc *pFunc, uint32_t tProfileTime)
{
	// zero entries are not collected to have a cleaner list
	if (!tProfileTime) return;
	// add entry to list
	Entry e;
	e.pFunc = pFunc;
	e.tProfileTime = tProfileTime;
	Times.push_back(e);
}

void C4AulProfiler::Show()
{
	// sort by time
	std::sort(Times.rbegin(), Times.rend());
	// display them
	Log("Profiler statistics:");
	Log("==============================");
	typedef std::vector<Entry> EntryList;
	for (EntryList::iterator i = Times.begin(); i!=Times.end(); ++i)
	{
		Entry &e = (*i);
		LogF("%05ums\t%s", e.tProfileTime, e.pFunc ? (e.pFunc->GetFullName().getData()) : "Direct exec");
	}
	Log("==============================");
	// done!
}

C4Value C4AulExec::DirectExec(C4PropList *p, const char *szScript, const char *szContext, bool fPassErrors, C4AulScriptContext* context, bool parse_function)
{
	if (DEBUGREC_SCRIPT && Config.General.DebugRec)
	{
		AddDbgRec(RCT_DirectExec, szScript, strlen(szScript)+1);
		int32_t iObjNumber = p && p->GetPropListNumbered() ? p->GetPropListNumbered()->Number : -1;
		AddDbgRec(RCT_DirectExec, &iObjNumber, sizeof(int32_t));
	}
	// profiler
	StartDirectExec();
	C4PropListStatic * script = ::GameScript.GetPropList();
	if (p && p->IsStatic())
		script = p->IsStatic();
	else if (p && p->GetDef())
		script = p->GetDef();
	// Add a new function
	auto pFunc = std::make_unique<C4AulScriptFunc>(script, nullptr, nullptr, szScript);
	// Parse function
	try
	{
		if (parse_function)
		{
			// Expect a full function (e.g. "func foo() { return bar(); }")
			pFunc->ParseDirectExecFunc(&::ScriptEngine, context);
		}
		else
		{
			// Expect a single statement (e.g. "bar()")
			pFunc->ParseDirectExecStatement(&::ScriptEngine, context);
		}
		C4AulParSet Pars;
		C4Value vRetVal(Exec(pFunc.get(), p, Pars.Par, fPassErrors));
		// profiler
		StopDirectExec();
		return vRetVal;
	}
	catch (C4AulError &ex)
	{
		if(fPassErrors)
			throw;
		::ScriptEngine.GetErrorHandler()->OnError(ex.what());
		LogCallStack();
		StopDirectExec();
		return C4VNull;
	}
}

void C4AulProfiler::ResetTimes(C4PropListStatic * p)
{
	// zero all profiler times of owned functions
	C4AulScriptFunc *pSFunc;
	for (C4String *pFn = p->EnumerateOwnFuncs(); pFn; pFn = p->EnumerateOwnFuncs(pFn))
		if ((pSFunc = p->GetFunc(pFn)->SFunc()))
			pSFunc->tProfileTime = 0;
}

void C4AulProfiler::CollectTimes(C4PropListStatic * p)
{
	// collect all profiler times of owned functions
	C4AulScriptFunc *pSFunc;
	for (C4String *pFn = p->EnumerateOwnFuncs(); pFn; pFn = p->EnumerateOwnFuncs(pFn))
		if ((pSFunc = p->GetFunc(pFn)->SFunc()))
			CollectEntry(pSFunc, pSFunc->tProfileTime);
}

void C4AulProfiler::ResetTimes()
{
	// zero all profiler times of owned functions
	ResetTimes(::ScriptEngine.GetPropList());
	// reset sub-scripts
	for (C4ScriptHost *pScript = ::ScriptEngine.Child0; pScript; pScript = pScript->Next)
		ResetTimes(pScript->GetPropList());
}

void C4AulProfiler::CollectTimes()
{
	// collect all profiler times of owned functions
	CollectTimes(::ScriptEngine.GetPropList());
	// collect sub-scripts
	for (C4ScriptHost *pScript = ::ScriptEngine.Child0; pScript; pScript = pScript->Next)
		CollectTimes(pScript->GetPropList());
}
