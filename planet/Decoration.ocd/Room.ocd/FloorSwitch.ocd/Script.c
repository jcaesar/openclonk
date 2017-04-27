/**
	Floor Switch
	A switch which is triggered when sufficient mass lies on top of it.

	@author Maikel
*/

local target_door, y_position;
local up_action, down_action;

public func Initialize()
{
	y_position = 0;
	AddTimer("CheckObjects", 5);
	return;
}

public func CheckObjects()
{
	// Get the total mass on the switch.
	var total_mass = 0;
	var obj_on_switch = FindObjects(Find_InRect(-20, -30, 40, 30), Find_NoContainer(), Find_Not(Find_Category(C4D_StaticBack)));
	for (var obj in obj_on_switch)
		if (obj->GetContact(-1, CNAT_Bottom))
      		total_mass += obj->GetMass();
	// Determine desired position.
	var desired_y = 0;
	if (total_mass >= this.SwitchMass)
		desired_y = this.MoveDownDistance;
	// Don't do anything if at desired position.
	if (y_position == desired_y)
		return;
	// Determine movement change and move switch plus object on it.
	var change = BoundBy(desired_y - y_position, -1, 1);
	for (var obj in obj_on_switch)
		if (obj->GetContact(-1, CNAT_Bottom))
      		obj->SetPosition(obj->GetX(), obj->GetY() + change);
	SetPosition(GetX(), GetY() + change);
	y_position += change;
	// Do moving of target door or perform user actions.
	if (y_position == desired_y)
	{
		if (desired_y == 0)
		{
			if (target_door)
				target_door->CloseDoor();
			UserAction->EvaluateAction(up_action, this);
		}
		else if (desired_y == this.MoveDownDistance)
		{
			if (target_door)
				target_door->OpenDoor();
			UserAction->EvaluateAction(down_action, this);
		}
	}
	return;
}

public func SetStoneDoor(object door)
{
	target_door = door;
	return true;
}

public func SetActions(new_up_action, new_down_action)
{
	up_action = new_up_action;
	down_action = new_down_action;
	return true;
}


/*-- Saving --*/

public func SaveScenarioObject(proplist props)
{
	if (!inherited(props, ...)) return false;
	if (target_door) props->AddCall("Target", this, "SetStoneDoor", target_door);
	if (up_action || down_action) props->AddCall("Action", this, "SetActions", up_action, down_action);
	return true;
}


/*-- Editor --*/

public func Definition(proplist def)
{
	if (!def.EditorProps) def.EditorProps = {};
	def.EditorProps.target_door = { Name = "$Target$", Type = "object", Filter = "IsSwitchTarget" };
	def.EditorProps.up_action = new UserAction.Prop { Name="$UpAction$" };
	def.EditorProps.down_action = new UserAction.Prop { Name="$DownAction$" };
	return _inherited(def, ...);
}


/*-- Properties --*/

local Name = "$Name$";
local Description = "$Description$";
local Plane = 200;
local SwitchMass = 100;
local MoveDownDistance = 3;