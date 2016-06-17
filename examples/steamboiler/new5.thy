theory new5
imports 
Main 

begin 
datatype State = init | norm | broken | stop
datatype OnOff = on |off
datatype OpenClosed = open0 | closed
datatype WorksBroken = works | broken


record SteamBoiler0 = 
PSWITCH :: "State"
W_MAX :: "nat"
D_MAX :: "nat"
PAMOUNT :: "State"
W_MIN :: "nat"
A :: "OnOff"
DELTA_D :: "nat"
DELTA_P :: "nat"
L :: "nat"
V :: "OpenClosed"
Z :: "State"
W :: "nat"
D :: "nat"
W_OPT :: "nat"


locale thesteamboiler = 
fixes 
w_max :: "nat"
and 
d_max :: "nat"
and 
l :: "nat"
and a :: "OnOff"
and 
w_min :: "nat"
and 
delta_p :: "nat"
and 
delta_d :: "nat"
and v :: "OpenClosed"
and z :: "State"
and w :: "nat"
and d :: "nat"
and w_opt :: "nat"
 
begin

definition SteamBoilerInit0 :: 
 "SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SteamBoilerInit0 steamboiler0 a' steamboiler0' z' v' == (a' = off) 
\<and> (z' = init)"

(*definition IS2 :: 
 "SteamBoiler0 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> SteamBoiler0 => bool"
where 
"IS2 steamboiler0 delta' s' steamboiler0' == (a' = off) 
\<and> (z' = init)"*)

(*CS8
definition SInitNormal01 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal01 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = init) 
\<and> (d > 0 \<or>
 k_w = broken)
\<and> (z' = stop)"*)

(*CS7*)
definition SNormalStop0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SNormalStop0 steamboiler0 a' steamboiler0' z' v' ==
 (z = norm) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)"

(*CS13
definition SInitNormal03 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal03 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' ==
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
 z' = z)"*)

(*CS2*)
definition SInitStop0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SInitStop0 steamboiler0 a' steamboiler0' z' v' ==
 (z = init) 
\<and> (d > 0)
\<and> (z' = stop)"

(* OS1*)
definition PumpsOff :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => bool"
where 
"PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0' == (p_1' = off \<and>
 p_2' = off \<and>
 p_3' = off \<and>
 p_4' = off)"

(*CS15
definition SInitNormal05 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal05 steamboiler0 k_p4 k_d k_w k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm \<or>
 z = broken) 
\<and> (k_w = works) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)"*)

(* OS3*)
definition SNormalContinue0 :: 
 "SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => bool"
where 
"SNormalContinue0 steamboiler0 a' steamboiler0' z' v' == (z = norm) 
\<and> (w > w_opt - 3*l) 
\<and> (w \<le> w_opt)"

(* OS2*)
definition PumpsOn :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => bool"
where 
"PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0' == (p_1' = on \<and>
 p_2' = on \<and>       
 p_3' = on \<and>
 p_4' = on)"

(*A5*)
fun pswitch ::
"(OnOff * WorksBroken) \<Rightarrow> OnOff"
where
"pswitch (on,works) = on"
| "pswitch (on,broken) = off"
| "pswitch (off,works) = off"
| "pswitch (off,broken) = off"

(*A6*)
fun pamount :: "(OnOff * WorksBroken) => nat"
   where  "pamount (on , works)  = 1"
| "pamount (off , _) = 0"
| "pamount (_ , broken) = 0"

(* OS5*)
definition PumpsControlledOff :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken => bool"
where 
"PumpsControlledOff p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4 == 
(p_1' = pswitch(off, k_p1) \<and>
 p_2' = pswitch(off, k_p2) \<and>
 p_3' = pswitch(off, k_p3) \<and>
 p_4' = pswitch(off, k_p4))"

(* OS4*)
definition PumpsControlledOn :: 
 "OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> WorksBroken => bool"
where 
"PumpsControlledOn p_4' steamboiler0 k_w k_d p_3' p_2' k_p2 k_p3 k_p1 p_1' steamboiler0' k_p4 == 
(p_1' = pswitch(on, k_p1) \<and>
 p_2' = pswitch(on, k_p2) \<and>
 p_3' = pswitch(on, k_p3) \<and>
 p_4' = pswitch(on, k_p4))"

(*CS14
definition SInitNormal04 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal04 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm) 
\<and> (k_w = works) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> (s' = w) 
\<and> ((Pumps p_1 p_2 p_3 p_4)ControlledOff) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"*)

(* OS6
definition AmountComputation :: 
 "WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken => bool"
where 
"AmountComputation k_p4 k_d k_w amount delta_pumps k_p2 k_p3 k_p1 == (amount) 
\<and> (delta_pumps)"*)

(* CS20
SBrokenControlStop1
definition SInitStop00 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitStop00 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = broken) 
\<and> (k_w = broken) 
\<and> (k_d = broken)
\<and> (a' = off \<and>
 z' = stop)"*)

(*CS21
definition SInitStop01 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitStop01 steamboiler0 k_p4 k_d delta' k_w s' amount delta_pumps k_p2 k_p3 k_p1 steamboiler0' ==
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
 z' = stop)"*)

(*CS19
definition SInitNormal09 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal09 steamboiler0 k_p4 k_d delta' k_w s' amount delta_pumps k_p2 k_p3 k_p1 steamboiler0' ==
 (z = broken) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_max) 
\<and> (w < (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOn) 
\<and> (w \<ge> (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOff)
\<and> (s' = w) 
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = norm)"*)

(*CS18
definition SInitNormal08 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal08 steamboiler0 k_p4 k_d delta' k_w s' amount delta_pumps k_p2 k_p3 k_p1 steamboiler0' ==
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
\<and> (z' = broken)"*)

(*CS10
definition SInitEmpty1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal00 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w > w_max)
\<and> (z' = z) 
\<and> (v' = open0) 
\<and> (a' = off) 
\<and> ((Pumps p_1 p_2 p_3 p_4)Off)"*)

(*CS12
definition SNormalFill1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal02 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt - 3l)
\<and> (s' = w) 
\<and> ((Pumps p_1 p_2 p_3 p_4)ControlledOn) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"*)

(*CS17
definition SNormalBroken :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal07 steamboiler0 k_p4 k_d delta' k_w s' amount delta_pumps k_p2 k_p3 k_p1 steamboiler0' ==
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
\<and> (z' = broken)"*)

(*CS16
definition SNormalControlStop1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> SteamBoiler0 => bool"
where 
"SInitNormal06 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 steamboiler0' ==
 (z = norm) 
\<and> (k_w = broken \<and>
 k_d = broken)
\<and> (a' = off \<and>
 z' = stop)"*)


(*CS9*)
definition SInitFill1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> 
WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> bool"
where 
"SInitFill1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a' ==
 (z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w < w_min + d_max)
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off) 
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))"

(*CS8*)
definition SInitNormal1 :: 
"SteamBoiler0 \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> nat \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow> WorksBroken \<Rightarrow>
OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 => State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> bool"
where 
"SInitNormal1 steamboiler0 k_p4 k_d delta' k_w s' k_p2 k_p3 k_p1 p_4' p_3' p_2' p_1' steamboiler0' z' v' a' ==
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
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))"

(*CS5*)
definition SNormalFill0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SNormalFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4'==
 (z = norm) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt -3*l)
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

(*CS4*)
definition SInitEmpty0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitEmpty0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' == 
(z = init)
\<and> (d = 0)
\<and> (w > w_max)
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = z)
\<and> (v' = open0)
\<and> (a' = off)"

(*CS6*)
definition SNormalNotFill0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SNormalNotFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' ==
 (z = norm) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)"

(*CS1*)
definition SInitNormal0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitNormal0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max)
\<and> (w \<le> w_max) 
\<and> ((PumpsOff p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on)"

(*CS3*)
definition SInitFill0 :: 
"SteamBoiler0 \<Rightarrow> OnOff \<Rightarrow> SteamBoiler0 \<Rightarrow> State \<Rightarrow> OpenClosed => OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> OnOff \<Rightarrow> bool"
where 
"SInitFill0 steamboiler0 a' steamboiler0' z' v' p_1' p_2' p_3' p_4' ==
 (z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max)
\<and> ((PumpsOn p_4' steamboiler0 p_3' p_2' p_1' steamboiler0'))
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off)"

definition TS6 :: 
"(*TS6_TYPES*) => bool"
where 
"TS6 (*TS6_VARIABLES*) == (*TS6_EXPRESSION*)"

definition TS4 :: 
"(*TS4_TYPES*) => bool"
where 
"TS4 (*TS4_VARIABLES*) == (*TS4_EXPRESSION*)"

definition TS5 :: 
"(*TS5_TYPES*) => bool"
where 
"TS5 (*TS5_VARIABLES*) == (*TS5_EXPRESSION*)"

definition TS2 :: 
"(*TS2_TYPES*) => bool"
where 
"TS2 (*TS2_VARIABLES*) == (*TS2_EXPRESSION*)"

definition TS1 :: 
"(*TS1_TYPES*) => bool"
where 
"TS1 (*TS1_VARIABLES*) == (*TS1_EXPRESSION*)"

definition TS3 :: 
"(*TS3_TYPES*) => bool"
where 
"TS3 (*TS3_VARIABLES*) == (*TS3_EXPRESSION*)"

lemma SInitNormal01_L1:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = init) 
\<and> (d > 0 \<or>
 k_w = broken)
\<and> (z' = stop)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SNormalStop0_L2:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> :: SteamBoiler1.
\<exists> :: SteamBoiler1.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> z' :: State.
\<exists> v' :: OpenClosed.
(z = norm) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal03_L3:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
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
 z' = z)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitStop0_L4:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> :: SteamBoiler1.
\<exists> :: SteamBoiler1.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> z' :: State.
\<exists> v' :: OpenClosed.
(z = init) 
\<and> (d > 0)
\<and> (z' = stop)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal05_L5:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = norm \<or>
 z = broken) 
\<and> (k_w = works) 
\<and> (w < w_min \<or>
 w > w_max)
\<and> (a' = off \<and>
 z' = stop)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal04_L6:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = norm) 
\<and> (k_w = works) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> (s' = w) 
\<and> ((Pumps p_1 p_2 p_3 p_4)ControlledOff) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitStop00_L7:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = broken) 
\<and> (k_w = broken) 
\<and> (k_d = broken)
\<and> (a' = off \<and>
 z' = stop)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitStop01_L8:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> amount :: nat.
\<exists> delta_pumps :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
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
 z' = stop)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal09_L9:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> amount :: nat.
\<exists> delta_pumps :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = broken) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_max) 
\<and> (w < (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOn) 
\<and> (w \<ge> (w_min + w_max)/2 rightarrow (Pumps p_1 p_2 p_3 p_4)ControlledOff)
\<and> (s' = w) 
\<and> (v' = closed \<and>
 a' = on) 
\<and> (z' = norm)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal08_L10:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> amount :: nat.
\<exists> delta_pumps :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
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
\<and> (z' = broken)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal00_L11:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = init) 
\<and> (d = 0) 
\<and> (w > w_max)
\<and> (z' = z) 
\<and> (v' = open0) 
\<and> (a' = off) 
\<and> ((Pumps p_1 p_2 p_3 p_4)Off)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal02_L12:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = norm) 
\<and> (k_w = works) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt - 3l)
\<and> (s' = w) 
\<and> ((Pumps p_1 p_2 p_3 p_4)ControlledOn) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal07_L13:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> amount :: nat.
\<exists> delta_pumps :: nat.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
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
\<and> (z' = broken)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal06_L14:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = norm) 
\<and> (k_w = broken \<and>
 k_d = broken)
\<and> (a' = off \<and>
 z' = stop)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitFill1_L15:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
(z = init) 
\<and> (d = 0) 
\<and> (k_w = works \<and>
 k_d = works) 
\<and> (w < w_min + d_max)
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off) 
\<and> ((Pumps p_1 p_2 p_3 p_4)On)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal1_L16:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> k_p4 :: WorksBroken.
\<exists> k_d :: WorksBroken.
\<exists> delta' :: nat.
\<exists> k_w :: WorksBroken.
\<exists> :: SteamBoiler1.
\<exists> s' :: nat.
\<exists> :: SteamBoiler1.
\<exists> k_p2 :: WorksBroken.
\<exists> k_p3 :: WorksBroken.
\<exists> k_p1 :: WorksBroken.
\<exists> steamboiler0' :: SteamBoiler0.
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
\<and> ((Pumps p_1 p_2 p_3 p_4)Off)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SNormalFill0_L17:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> :: SteamBoiler1.
\<exists> :: SteamBoiler1.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> z' :: State.
\<exists> v' :: OpenClosed.
(z = norm) 
\<and> (w \<ge> w_min) 
\<and> (w \<le> w_opt -3l)
\<and> ((Pumps p_1 p_2 p_3 p_4)On) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitEmpty0_L18:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> :: SteamBoiler1.
\<exists> :: SteamBoiler1.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> z' :: State.
\<exists> v' :: OpenClosed.
(w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SNormalNotFill0_L19:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> :: SteamBoiler1.
\<exists> :: SteamBoiler1.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> z' :: State.
\<exists> v' :: OpenClosed.
(z = norm) 
\<and> (w > w_opt) 
\<and> (w \<le> w_max)
\<and> ((Pumps p_1 p_2 p_3 p_4)Off) 
\<and> (v' = closed \<and>
 a' = on \<and>
 z' = z)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitNormal0_L20:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> :: SteamBoiler1.
\<exists> :: SteamBoiler1.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> z' :: State.
\<exists> v' :: OpenClosed.
(z = init) 
\<and> (d = 0) 
\<and> (w \<ge> w_min + d_max)
\<and> (w \<le> w_max) 
\<and> ((Pumps p_1 p_2 p_3 p_4)Off) 
\<and> (z' = norm) 
\<and> (v' = closed) 
\<and> (a' = on)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

lemma SInitFill0_L21:
"(\<exists> steamboiler0 :: SteamBoiler0.
\<exists> a' :: OnOff.
\<exists> :: SteamBoiler1.
\<exists> :: SteamBoiler1.
\<exists> steamboiler0' :: SteamBoiler0.
\<exists> z' :: State.
\<exists> v' :: OpenClosed.
(z = init) 
\<and> (d = 0) 
\<and> (w < w_min + d_max)
\<and> ((Pumps p_1 p_2 p_3 p_4)On) 
\<and> (z' = z) 
\<and> (v' = closed) 
\<and> (a' = off)
\<and> (w_min < w_max)
\<and> (w_min < w_ma''x))"
sorry

end
end
