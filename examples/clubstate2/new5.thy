theory new5
imports 
Main 

begin 
typedecl STUDENT

record ClubState2 = 
MAXPLAYERS :: "(STUDENT set)"
HALL :: "(STUDENT set)"
BADMINTON :: "(STUDENT set)"

locale gpsaclubstate = 
fixes 
maxPlayers :: "nat"
and hall :: "(STUDENT set)"
and badminton :: "(STUDENT set)"
and waiting :: "(STUDENT list)"
and onCourt :: "(STUDENT set)"
 
assumes "maxPlayers = 20" 
 and "hall \<subseteq> badminton" 
 and "card hall \<le> maxPlayers" 
(* and "[(sorted_list_of_set onCourt), ran waiting] partition hall"*)
begin

definition InitClubState2 :: 
 "(STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> STUDENT list \<Rightarrow> ClubState2 \<Rightarrow> ClubState2 => bool"
where 
"InitClubState2 badminton' hall' onCourt' waiting' clubstate2' clubstate2 == (badminton' = {})"

definition NewGame :: 
"(STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow>  (STUDENT set) \<Rightarrow> STUDENT list \<Rightarrow> ClubState2 \<Rightarrow> ClubState2 => bool"
where 
"NewGame badminton' hall'  onCourt' waiting' clubstate2' clubstate2 ==
onCourt = {}
\<and> (length waiting \<ge> 2)
\<and> ((length waiting \<ge> 4) \<longrightarrow> (card onCourt' = 4))
\<and> ((length waiting) < 4 \<longrightarrow> ((card onCourt' = 2) \<or> (card onCourt' = 3)))
\<and> (hd waiting \<in> onCourt')
\<and> (onCourt' \<subseteq> (set waiting))
(*\<and> (waiting' = waiting \<restriction> ((Range waiting) - onCourt'))*)
\<and> (hall' = hall)
\<and> (badminton' = badminton)"

definition LeaveHall :: 
"(STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> STUDENT \<Rightarrow> (STUDENT set) \<Rightarrow> STUDENT list \<Rightarrow> ClubState2 \<Rightarrow> ClubState2 => bool"
where 
"LeaveHall badminton' hall' p onCourt' waiting' clubstate2' clubstate2 ==
(p \<in> set waiting)
(* \<and> (waiting' = squash(waiting \<unlhd> {(p)})) *)
\<and> (hall' = hall - {(p)}) 
\<and> (badminton' = badminton)"

definition FinishGame :: 
"(STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow>  STUDENT list \<Rightarrow> ClubState2 \<Rightarrow> ClubState2 => bool"
where 
"FinishGame badminton' hall'  onCourt' waiting' clubstate2' clubstate2 ==
(onCourt \<noteq> {})
\<and> (onCourt' = {})
\<and> (\<exists>s::STUDENT list. (set s=onCourt') \<and> (waiting' =  concat [s]))
\<and> (hall' = hall) 
\<and> (badminton' = badminton)"

lemma NewGame_L1:
"(\<exists> badminton :: (STUDENT set).
\<exists> badminton' :: (STUDENT set).
\<exists> hall :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> onCourt :: (STUDENT set).
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting :: (STUDENT list).
\<exists> waiting' :: (STUDENT list).
onCourt = {}
\<and> (length waiting \<ge> 2)
\<and> ((length waiting \<ge> 4) \<longrightarrow> (card onCourt' = 4))
\<and> ((length waiting) < 4 \<longrightarrow> ((card onCourt' = 2) \<or> (card onCourt' = 3)))
\<and> (hd waiting \<in> onCourt')
\<and> (onCourt' \<subseteq> (set waiting))
(*\<and> (waiting' = waiting \<restriction> ((Range waiting) - onCourt'))*)
\<and> (hall' = hall)
\<and> (badminton' = badminton)
\<and> (hall \<subseteq> badminton)
\<and> (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton')
\<and> (card hall' \<le> maxPlayers))"
by force

lemma LeaveHall_L2:
"(\<exists> badminton :: (STUDENT set).
\<exists> badminton' :: (STUDENT set).
\<exists> hall :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> onCourt :: (STUDENT set).
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting :: (STUDENT list).
\<exists> waiting' :: (STUDENT list).
\<exists> p :: STUDENT.
(p \<in> set waiting)
(* \<and> (waiting' = squash(waiting \<unlhd> {(p)})) *)
\<and> (hall' = hall - {(p)}) 
\<and> (badminton' = badminton)
\<and> (hall \<subseteq> badminton)
\<and> (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton')
\<and> (card hall' \<le> maxPlayers))"
by (metis Diff_eq_empty_iff List.set_insert Nat.le_iff_add add_0_left card.empty empty_Diff equals0I insert_not_empty)

lemma FinishGame_L3:
"(\<exists> badminton :: (STUDENT set).
\<exists> badminton' :: (STUDENT set).
\<exists> hall :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> onCourt :: (STUDENT set).
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting :: (STUDENT list).
\<exists> waiting' :: (STUDENT list).
(onCourt \<noteq> {})
\<and> (onCourt' = {})
\<and> (\<exists>s::STUDENT list. (set s=onCourt') \<and> (waiting' =  concat [s]))
\<and> (hall' = hall) 
\<and> (badminton' = badminton)
\<and> (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton')
\<and> (card hall' \<le> maxPlayers))"
using LeaveHall_L2 by auto



end
end
