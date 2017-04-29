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
#include "script/C4AulDebug.h"

#include "game/C4Application.h"
#include "C4Version.h"
#include "control/C4GameControl.h"
#include "game/C4Game.h"
#include "gui/C4MessageInput.h"
#include "lib/C4Log.h"
#include "object/C4Def.h"
#include "object/C4Object.h"
#include "script/C4AulExec.h"

#ifndef NOAULDEBUG

// *** C4AulDebug

C4AulDebug::C4AulDebug()
		: fInit(false), fConnected(false)
{
}

C4AulDebug::~C4AulDebug()
{
	for (std::list<StdStrBuf*>::iterator it = StackTrace.begin(); it != StackTrace.end(); it++)
		{delete *it;}
	if (pDebug == this) pDebug = nullptr;
}

bool C4AulDebug::InitDebug(const char *szPassword, const char *szHost)
{
	// Create debug object
	if (!pDebug) pDebug = new C4AulDebug();
	// Initialize
	pDebug->SetPassword(szPassword);
	pDebug->SetAllowed(szHost);
	pDebug->SetEngine(&AulExec);
	return true;
}

bool C4AulDebug::Listen(uint16_t iPort, bool fWait)
{
	if (!Init(iPort))
		{ LogFatal("C4Aul debugger failed to initialize!"); return false; }
	// Log
	LogF("C4Aul debugger initialized on port %d", iPort);
	// Add to application
	Application.Add(this);
	// Wait for connection
	if (fWait)
	{
		Log("C4Aul debugger waiting for connection...");
		while (!isConnected())
			if (!Application.ScheduleProcs())
				return false;
	}
	// Done
	return true;
}

void C4AulDebug::PackPacket(const C4NetIOPacket &rPacket, StdBuf &rOutBuf)
{
	// Enlarge buffer
	int iSize = rPacket.getSize(),
	            iPos = rOutBuf.getSize();
	rOutBuf.Grow(iSize + 2);
	// Write packet
	rOutBuf.Write(rPacket, iPos);
	// Terminate
	uint8_t *pPos = getMBufPtr<uint8_t>(rOutBuf, iPos + iSize);
	*pPos = '\r'; *(pPos + 1) = '\n';
}

size_t C4AulDebug::UnpackPacket(const StdBuf &rInBuf, const C4NetIO::addr_t &addr)
{
	// Find line separation
	const char *pSep = reinterpret_cast<const char *>(memchr(rInBuf.getData(), '\n', rInBuf.getSize()));
	if (!pSep)
		return 0;
	// Check if it's windows-style separation
	int iSize = pSep - getBufPtr<char>(rInBuf) + 1,
	            iLength = iSize - 1;
	if (iLength && *(pSep - 1) == '\r')
		iLength--;
	// Copy the line
	StdStrBuf Buf; Buf.Copy(getBufPtr<char>(rInBuf), iLength);
	// Password line?
	if (fConnected)
	{
		ProcessLineResult result = ProcessLine(Buf);
		// Send answer
		SendLine(result.okay ? "OK" : "ERR", result.answer.length() > 0 ? result.answer.c_str() : nullptr);
	}
	else if (!Password.getSize() || Password == Buf)
	{
		fConnected = true;
		SendLine("HLO", "This is " C4ENGINECAPTION ", " C4VERSION);
		Log("C4Aul debugger connected successfully!");
	}
	else
		C4NetIOTCP::Close(PeerAddr);
	// Consume line
	return iSize;
}

bool C4AulDebug::OnConn(const C4NetIO::addr_t &AddrPeer, const C4NetIO::addr_t &AddrConnect, const addr_t *pOwnAddr, C4NetIO *pNetIO)
{
	assert(pNetIO == this);
	// Already have a connection?
	if (fConnected) return false;
	// Check address
	if (!AllowedAddr.IsNull())
		if (AllowedAddr.GetHost() != AddrPeer.GetHost() ||
		    (AllowedAddr.GetPort() && AllowedAddr.GetPort() != AddrPeer.GetPort()))
		{
			LogF("C4AulDebug blocked connection from %s", AddrPeer.ToString().getData());
			return false;
		}
	// Log
	LogF("C4AulDebug got connection from %s", AddrPeer.ToString().getData());
	// Accept connection
	PeerAddr = AddrPeer;
	return true;
}

void C4AulDebug::OnDisconn(const C4NetIO::addr_t &AddrPeer, C4NetIO *pNetIO, const char *szReason)
{
	LogF("C4AulDebug lost connection (%s)", szReason);
	fConnected = false;
	eState = DS_Go;
	PeerAddr.Clear();
}

void C4AulDebug::OnPacket(const class C4NetIOPacket &rPacket, C4NetIO *pNetIO)
{
	// Won't get called
}

bool C4AulDebug::SetAllowed(const char *szHost)
{
	// Clear
	AllowedAddr.Clear();
	// No host?
	if (!szHost || !*szHost) return true;
	// Resolve the address
	AllowedAddr.SetAddress(StdStrBuf(szHost));
	return !AllowedAddr.IsNull();
}

bool C4AulDebug::Init(uint16_t iPort)
{
	if (fInit) Close();
	if (iPort == EndpointAddress::IPPORT_NONE) return false;

	// Register self as callback for network events
	C4NetIOTCP::SetCallback(this);

	// Start listening
	if (!C4NetIOTCP::Init(iPort))
		return false;

	// Okay
	fInit = true;
	eState = DS_Go;
	return true;
}

bool C4AulDebug::Close()
{
	if (!fInit) return true;
	fInit = fConnected = false;
	return C4NetIOTCP::Close();
}

bool C4AulDebug::Close(const addr_t &addr)
{
	if (!fInit) return true;
	bool success = C4NetIOTCP::Close(addr);
	if (success)
		fInit = fConnected = false;
	return success;
}

void C4AulDebug::OnLog(const char *szLine)
{
	if (!fConnected) return;
	SendLine("LOG", szLine);
}

C4AulDebug::ProcessLineResult C4AulDebug::ProcessLine(const StdStrBuf &Line)
{
	C4NetIOTCP::Close(PeerAddr);
	// TODO: Either remove this entirely or reimplement something somehow with LLVM
}

bool C4AulDebug::SendLine(const char *szType, const char *szData)
{
	StdStrBuf Line = szData ? FormatString("%s %s", szType, szData) : StdStrBuf(szType);
	return Send(C4NetIOPacket(Line.getData(), Line.getSize(), false, PeerAddr));
}

void C4AulDebug::DebugStep(C4AulBCC *pCPos, C4Value* stackTop)
{
	// Already stopped? Ignore.
	// This means we are doing some calculation with suspended script engine.
	// We do /not/ want to have recursive suspensions...
	if (eState == DS_Stop)
		return;

	// Have break point?
	if (pCPos->Par.i)
		eState = DS_Step;

	int iCallDepth = pExec->GetContextDepth();
	// Stop?
	switch (eState)
	{
		// Continue normally
	case DS_Go: return;

		// Always stop
	case DS_Stop: break;
	case DS_Step: break;

		// Only stop for same level or above
	case DS_StepOver:
		if (iCallDepth > iStepCallDepth)
			return;
		break;

		// Only stop above
	case DS_StepOut:
		if (iCallDepth >= iStepCallDepth)
			return;
		break;
	}
	
	// Get current script context
	C4AulScriptContext *pCtx = pExec->GetContext(iCallDepth-1);

	if (!fConnected)
	{
		// not connected anymore? nevermind
		eState = DS_Go;
		return;
	}
	
	// Maybe got a command in the meantime?
	Execute(0);

	// Let's stop here
	eState = DS_Stop;
	iStepCallDepth = iCallDepth;
	Game.HaltCount++;

	// No valid stop position? Just continue
	if (!pCtx)
	{
		Game.HaltCount--;
		eState = DS_Step;
		return;
	}

	// Signal
	if (pCPos && pCPos->bccType == AB_DEBUG && pCPos->Par.i)
		SendLine("STP", FormatString("Stopped on breakpoint %d", pCPos->Par.i).getData());
	else
		SendLine("STP", "Stepped");

	// Position
	ObtainStackTrace(pCtx, pCPos);
	SendLine("POS", StackTrace.front()->getData());

	// Suspend until we get some command
	while (fConnected && eState == DS_Stop)
		if (!Application.ScheduleProcs())
		{
			Close();
			return;
		}

	// Do whatever we've been told.
	Game.HaltCount--;
}

void C4AulDebug::ControlScriptEvaluated(const char* script, const char* result)
{
	SendLine("EVR", FormatString("%s=%s", script, result).getData());
}

const char* C4AulDebug::RelativePath(StdStrBuf &path)
{
	const char* p = path.getData();
	const char* result = Config.AtRelativePath(p);
	if (p != result)
		return result;
	// try path relative to scenario container
	StdStrBuf scenarioContainerPath;
	GetParentPath(::Game.ScenarioFile.GetName(), &scenarioContainerPath);
	return GetRelativePathS(p, scenarioContainerPath.getData());
}

void C4AulDebug::ObtainStackTrace(C4AulScriptContext* pCtx, C4AulBCC* pCPos)
{
	for (std::list<StdStrBuf*>::iterator it = StackTrace.begin(); it != StackTrace.end(); it++)
		{delete *it;}
	StackTrace.clear();
	for (int ctxNum = pExec->GetContextDepth()-1; ctxNum >= 0; ctxNum--)
	{
		C4AulScriptContext* c = pExec->GetContext(ctxNum);
		C4AulBCC* _cpos = c == pCtx ? pCPos : c->CPos;
		if (_cpos)
		{
			StdStrBuf* format = new StdStrBuf(FormatCodePos(c, _cpos));
			StackTrace.push_back(format);
		}
	}
}

StdStrBuf C4AulDebug::FormatCodePos(C4AulScriptContext *pCtx, C4AulBCC *pCPos)
{
	return StdStrBuf("(llvm)");
}

C4AulDebug * C4AulDebug::pDebug = nullptr;

#endif
