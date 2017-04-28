// TODO: Too much magic. Make this file disappear
#ifndef C4VALUEMAGIC_H
#define C4VALUEMAGIC_H

#include "script/C4Value.h"

// Okay, here is the problem. For C4ValueArray, there is a refcounting scheme, and that can be easily abused to not do refcounting during script execution and only accumulate the refs afterwards. For C4PropList (and children) there is something more tricky: A proplist actually knows all places from where it is being pointed to, and it can zero those places at any time (esp. if it is being deleted).
// Now, I don't want to have the llvm code make calls to keep track of all the places a pointer to a proplist is stored. (ultimately, something like that might be the way to go, but for now, that seems rather complicated.)
// For now, I've got a (slightly inefficient) but better idea: I'll use an intermediate. Put refcounting on it, and shwoops, I can use the same trick as for a list.

class C4PropListDlg : public C4RefCnt {
private:
	C4Value v;
public:
	void set(C4PropList* pl) {
		v.SetPropList(pl);
	}
	const C4Value& get() const {
		return v;
	}

	virtual ~C4PropListDlg() {}
};

// Yes, I could make a new C4V_Something C4V_Type enum member for this class, but I'd run into cyclicity problems. For now, a hack will do:

inline std::pair<C4V_Type,C4V_Data> C4ValueToAulLLVM(C4Value v) {
	C4V_Type t = v.GetType();
	switch (t) {
		case C4V_PropList:
		case C4V_Object:
		// I don't think the next two appear as actual types, still.
		case C4V_Def:
		case C4V_Effect: {
			auto dlg = new C4PropListDlg(); // TODO: This breaks reference integrity (and is more inefficient than I like). The Proplist would have to store where its (only) delegade resides.
			dlg->IncRef(); dlg->DecRef(); // Mark for deletion
			dlg->set(v.getPropList());
			C4V_Data d;
			d.PropList = reinterpret_cast<C4PropList*>(dlg); // Here comes the hack (1)
			return { t, d };
		}
		default:
			return { t, v.GetData() };
	}
}

inline C4Value AulLLVMToC4Value(C4V_Type t, C4V_Data d) {
	C4Value v;
	switch(t) {
		case C4V_PropList:
		case C4V_Object:
		case C4V_Def:
		case C4V_Effect: {
			auto dlg = reinterpret_cast<C4PropListDlg*>(d.PropList); // Hack (2)
			v.Set(dlg->get());
			break;
		}
		case C4V_Nil:
			v.Set0(); // So apparently, C4Value doesn't like it if you call Set(asdf, C4V_Nil)…
		default:
			v.Set(d,t);
			break;
	}
	switch(t) {
		case C4V_Nil:
		case C4V_Int:
		case C4V_Bool:
			break;
		case C4V_PropList:
		case C4V_String:
		case C4V_Array:
		case C4V_Function:
		case C4V_Object:
		case C4V_Def:
		case C4V_Effect:
			if (!v.GetData())
				v.Set0();
			break;
		case C4V_Any:
		case C4V_Enum:
		case C4V_C4ObjectEnum:
			assert(!"TODO");
	}
	return v;
}

#endif // C4VALUEMAGIC_H
