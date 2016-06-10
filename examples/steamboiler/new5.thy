theory gpsa1n2
imports 
Main 

begin 
datatype State = init | norm | broken | stop
datatype OnOff = on |off
datatype OpenClosed = open0 | closed
datatype WorksBroken = works | broken


record SteamBoiler0 = 
PSWITCH :: "State"
W_MAX :: "State"
D_MAX :: "State"
PAMOUNT :: "State"
W_MIN :: "State"
A :: "OnOff"
DELTA_D :: "State"
DELTA_P :: "State"
L :: "State"
V :: "OpenClosed"
Z :: "State"


locale 1n2 = 
fixes 
w_max :: "State"
and 
d_max :: "State"
and 
pswitch :: "State"
and 
l :: "State"
and a :: "OnOff"
and 
w_min :: "State"
and 
delta_p :: "State"
and 
delta_d :: "State"
and v :: "OpenClosed"
and 
pamount :: "State"
and z :: "State"
 
begin

definition IS1 :: 
 "SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"IS1 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' == (a' = off) 
\<and> (z' = init)"

definition IS6 :: 
 "SteamBoiler0 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 => bool"
where 
"IS6 steamboiler0 delta' steamboiler1 s' steamboiler1' steamboiler0' == (a' = off) 
\<and> (z' = init)"

definition PRE4 :: 
 "(*PRE4_TYPES*) => bool"
where 
"PRE4 (*PRE4_VARIABLES*) == (*PRECONDITION*) "

definition SNormalControlStop1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalControlStop1 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm) 
\<and> (k_w = broken \<and>
 k_d = broken)
\<and> (a' = off \<and>
 z' = stop)"

definition SNormalContinue1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalContinue1 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm) 
\<and> (k_w = works) 
\<and> (w > w_opt - 3l) 
\<and> (w \<le> w_opt)
\<and> (p_1' = pswitch(p_1 k_p1) \<and>
 p_2' = pswitch(p_2 k_p2)) 
\<and> (p_3' = pswitch(p_3 k_p3) \<and>
 p_4' = pswitch(p_4 k_p4)) 
\<and> (s' = w) 
\<and> (v' = v \<and>
 a' = a \<and>
 z' = z)"

definition SNormalWaterStop1 :: 
" => bool"
where 
"SNormalWaterStop1  ==
 
\<and> "

definition SNormalStop0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SNormalStop0 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' ==
 (z = norm) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)"

definition SNormalFill02 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalFill02 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = broken) 
\<and> (k_w = broken) 
\<and> (k_d = broken)
\<and> (a' = off \<and>
 z' = stop)"

definition PumpsOff :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> SteamBoiler1 \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => bool"
where 
"PumpsOff p_4 steamboiler0 steamboiler1 p_3 p_2 steamboiler1' p_1 steamboiler0' == (p_1 = off \<and>
 p_2' = off \<and>
 p_3' = off \<and>
 p_4' = off)"

definition SNormalContinue0 :: 
 "SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SNormalContinue0 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' == (z = norm) 
\<and> (w > w_opt - 3l) 
\<and> (w \<le> w_opt)"

definition PumpsOn :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> SteamBoiler1 \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => bool"
where 
"PumpsOn p_4 steamboiler0 steamboiler1 p_3 p_2 steamboiler1' p_1 steamboiler0' == (p_1 = on \<and>
 p_2' = on \<and>
 p_3' = on \<and>
 p_4' = on)"

definition PumpsControlledOff :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken => bool"
where 
"PumpsControlledOff p_4 steamboiler0 k_w k_d steamboiler1 p_3 p_2 steamboiler1' k_p2 k_p3 k_p1 p_1 steamboiler0' k_p4 == (p_1 = on \<and>
 p_2' = on \<and>
 p_3' = on \<and>
 p_4' = on)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (p_1 = off \<and>
 p_2' = off \<and>
 p_3' = off \<and>
 p_4' = off)"

definition AmountComputation :: 
 "WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken => bool"
where 
"AmountComputation k_p4 k_d k_w amount delta_pumps k_p2 k_p3 k_p1 == (amount) 
\<and> (delta_pumps)"

definition IS9 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"IS9 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w > w_max)
\<and> (z' = z) 
\<and> (v' = open0) 
\<and> (a' = off) 
\<and> ((Pumps p_1 p_2 p_3 p_4)Off)"

definition IS8 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"IS8 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w < w_min + d_max)
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off) 
\<and> ((Pumps p_1 p_2 p_3 p_4)On)"

definition IS3 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"IS3 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' ==
 (z = init) 
\<and> (d > 0)
\<and> (z' = stop)"

definition IS2 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"IS2 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max)
\<and> (w \<le> w_max) 
\<and> ((Pumps p_1 p_2 p_3 p_4)Off) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on)"

definition IS7 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"IS7 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w \<ge> w_min + d_max) 
\<and> (w \<le> w_max)
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on) 
\<and> (s' = w) 
\<and> ((Pumps p_1 p_2 p_3 p_4)Off)"

definition IS5 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"IS5 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' == True"

definition IS4 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"IS4 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max)
\<and> ((Pumps p_1 p_2 p_3 p_4)On) 
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off)"

definition SNormalFill00 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalFill00 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' amount delta_pumps k_p2 k_p3 k_p1 steamboiler0' ==
 (z = broken) 
\<and> (k_w = broken) 
\<and> (k_d = works)
\<and> (s' = s + amount -d) 
\<and> (delta' = delta + delta_pumps + delta_d) 
\<and> (s' \<ge> w_min + delta') 
\<and> (s' \<le> w_max - delta') 
\<and> (s' < (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOn) 
\<and> (s' \<ge> (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOff) 
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = broken)"

definition PO5 :: 
"(*PO5_TYPES*) => bool"
where 
"PO5 (*PO5_VARIABLES*) == (*POSTCONDITION*) "

definition SNormalBroken1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalBroken1 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' amount delta_pumps k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm) 
\<and> (k_w = broken) 
\<and> (k_d = works) 
\<and> (s' = s+ amount -d) 
\<and> (delta' = delta_pumps + delta_d)
\<and> (s' \<ge> w_min + delta') 
\<and> (s' \<le> w_max - delta') 
\<and> (s' < (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOn) 
\<and> (s' \<ge> (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOff) 
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = broken)"

definition SNormalFill1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalFill1 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt - 3l)
\<and> (s' = w) 
\<and> ((Pumps p_1 p_2 p_3 p_4)ControlledOn) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

definition SNormalNotFill1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalNotFill1 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm) 
\<and> (k_w = works) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> (s' = w) 
\<and> ((Pumps p_1 p_2 p_3 p_4)ControlledOff) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

definition SNormalFill0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SNormalFill0 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' ==
 (z = norm) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt -3l)
\<and> ((Pumps p_1 p_2 p_3 p_4)On) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

definition SNormalNotFill0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler1 \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SNormalNotFill0 steamboiler0 a' steamboiler1 steamboiler1' steamboiler0' z' v' ==
 (z = norm) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> ((Pumps p_1 p_2 p_3 p_4)Off) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

definition SNormalFill01 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalFill01 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' amount delta_pumps k_p2 k_p3 k_p1 steamboiler0' ==
 (z = broken) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_max) 
\<and> (w < (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOn) 
\<and> (w \<ge> (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOff)
\<and> (s' = w) 
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = norm)"

definition SNormalFill03 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SNormalFill03 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' amount delta_pumps k_p2 k_p3 k_p1 steamboiler0' ==
 (z = broken \<or>
 z = norm) 
\<and> (k_w = broken) 
\<and> (k_d = works)
\<and> (s' = s + amount - d) 
\<and> (z = broken rightarrow delta' = delta + delta_pumps + delta_d) 
\<and> (z = norm rightarrow delta' = delta_pumps + delta_d) 
\<and> (s' < w_min + delta' \<or>
 s' > w_max - delta') 
\<and> (a' = off \<and>
 z' = stop)"

definition IS10 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler1 \<Rightarrow> nat \<Rightarrow> SteamBoiler1 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"IS10 steamboiler0 k_p4 k_d delta' k_w steamboiler1 s' steamboiler1' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = init) 
\<and> (d > 0 \<or>
 k_w = broken)
\<and> (z' = stop)"

definition TS5 :: 
"(*TS5_TYPES*) => bool"
where 
"TS5 (*TS5_VARIABLES*) == (*TS5_EXPRESSION*)"

definition TS4 :: 
"(*TS4_TYPES*) => bool"
where 
"TS4 (*TS4_VARIABLES*) == (*TS4_EXPRESSION*)"

definition TS1 :: 
"(*TS1_TYPES*) => bool"
where 
"TS1 (*TS1_VARIABLES*) == (*TS1_EXPRESSION*)"

definition TS2 :: 
"(*TS2_TYPES*) => bool"
where 
"TS2 (*TS2_VARIABLES*) == (*TS2_EXPRESSION*)"

definition TS3 :: 
"(*TS3_TYPES*) => bool"
where 
"TS3 (*TS3_VARIABLES*) == (*TS3_EXPRESSION*)"

definition TS6 :: 
"(*TS6_TYPES*) => bool"
where 
"TS6 (*TS6_VARIABLES*) == (*TS6_EXPRESSION*)"

end
end
