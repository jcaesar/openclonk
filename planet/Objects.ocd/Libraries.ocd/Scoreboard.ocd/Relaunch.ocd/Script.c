/*--
		Modular scoreboard: Relaunches
		Author: Maikel

		This script can be included to create a relaunch count column in the scoreboard.
		Make sure that the following functions return _inherited(...);
			* Initialize();
			* InitializePlayer(int plr);
			* RelaunchPlayer(int plr, int killer);
			* RemovePlayer(int plr);
--*/

/*-- Callbacks --*/

protected func Initialize()
{
	// init scoreboard
	// init scoreboard, uses the condition of Scoreboard_Deaths too
	if(UnlimitedRelaunches()) return;
    Scoreboard->Init(
		[{key = "relaunches", title = Scoreboard_Relaunch, sorted = true, desc = true, default = "", priority = 75, conditional = Scoreboard_Death.ScoreboardCondition}]
		);
	return _inherited(...);
}

protected func InitializePlayer(int plr)
{
    if(UnlimitedRelaunches()) return;
	Scoreboard->NewPlayerEntry(plr);
	Scoreboard->SetPlayerData(plr, "relaunches", GetRelaunchCount(plr));
	return _inherited(plr, ...);
}

protected func RelaunchPlayer(int plr, int killer)
{
    if(UnlimitedRelaunches()) return;
	Scoreboard->SetPlayerData(plr, "relaunches", GetRelaunchCount(plr));
	return _inherited(plr, killer, ...);
}

protected func RemovePlayer(int plr)
{
	return _inherited(plr, ...);
}

/*-- Misc --*/



local Name = "Scoreboard Relaunches";
