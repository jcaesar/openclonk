#include Library_Liquid

func GetLiquidType() { return "Acid"; }

func Disperse(int angle, int strength)
{
	DisperseMaterial(GetLiquidType(), GetLiquidAmount(), strength, angle);
	_inherited(...);
}

local Name="$Name$";