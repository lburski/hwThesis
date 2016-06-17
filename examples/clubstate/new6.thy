theory new6
imports 
Main 

begin 
typedecl STUDENT
datatype MESSAGE = success| isMember | notMember | hallFull | inHall | notInHall


record ClubState = 
MAXPLAYERS :: "nat"
HALL :: "(STUDENT set)"
BADMINTON :: "(STUDENT set)"


locale theclubstate = 
fixes maxPlayers :: "nat"
and hall :: "(STUDENT set)"
and badminton :: "(STUDENT set)"
 
assumes
"(hall \<subseteq> badminton)"
and "(card hall \<le> maxPlayers)"
and "maxPlayers = 20"
begin

definition InitClubState :: 
 "(STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => bool"
where 
"InitClubState hall' clubstate' clubstate badminton' == (badminton' = {}) 
\<and> (hall' = {})"

definition LeaveHall :: 
"(STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> (STUDENT set) => bool"
where 
"LeaveHall hall' clubstate' clubstate leaver badminton' ==
 (leaver \<in> hall)
\<and> (hall' = hall - {(leaver)}) 
\<and> (badminton' = badminton)"

definition AddMember :: 
"(STUDENT set) \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => bool"
where 
"AddMember hall' clubstate' newMember clubstate badminton' ==
 (newMember \<notin> badminton)
\<and> (badminton' = badminton \<union> {(newMember)}) 
\<and> (hall' = hall)"

definition EnterHall :: 
"STUDENT \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => bool"
where 
"EnterHall enterer hall' clubstate' clubstate badminton' ==
 (enterer \<in> badminton) 
\<and> (enterer \<notin> hall) 
\<and> (card hall < maxPlayers)
\<and> (hall' = hall \<union> {(enterer)}) 
\<and> (badminton' = badminton)"

definition RemoveMember :: 
"(STUDENT set) \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => bool"
where 
"RemoveMember hall' clubstate' member clubstate badminton' ==
 (member \<in> badminton)
\<and> (badminton' = badminton - {(member)}) 
\<and> (hall' = hall - {(member)})"

definition IsMember :: 
 "MESSAGE \<Rightarrow> STUDENT => bool"
where 
"IsMember outcome newMember == (newMember \<in> badminton)
\<and> (outcome = isMember)"

definition AlreadyInHall :: 
 "MESSAGE \<Rightarrow> (STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> STUDENT => bool"
where 
"AlreadyInHall outcome badminton' hall' clubstate clubstate' enterer == (enterer \<in> hall)
\<and> (outcome = inHall)"

definition NotMember :: 
 "MESSAGE \<Rightarrow> (STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> ClubState => bool"
where 
"NotMember outcome badminton' hall' clubstate member clubstate' == (member \<notin> badminton)
\<and> (outcome = notMember)"

definition NotInHall :: 
 "MESSAGE \<Rightarrow> (STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> ClubState => bool"
where 
"NotInHall outcome badminton' hall' clubstate leaver clubstate' == (leaver \<notin> hall)
\<and> (outcome = notInHall)"

definition SuccessMessage :: 
 "MESSAGE \<Rightarrow> (STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> STUDENT => bool"
where 
"SuccessMessage outcome badminton' hall' clubstate clubstate' newMember == (outcome = success)"

definition TotalLeaveHall :: 
"(STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> (STUDENT set) \<Rightarrow> STUDENT => MESSAGE \<Rightarrow>bool"
where 
"TotalLeaveHall hall' clubstate' clubstate leaver badminton' newMember outcome == (LeaveHall hall' clubstate' clubstate leaver badminton')
\<and> (SuccessMessage outcome badminton' hall' clubstate clubstate' newMember)
\<or> (NotInHall outcome badminton' hall' clubstate leaver clubstate')"

definition TotalRemoveMember :: 
"(STUDENT set) \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => STUDENT \<Rightarrow> MESSAGE \<Rightarrow> bool"
where 
"TotalRemoveMember  hall' clubstate' member clubstate badminton' newMember outcome == (RemoveMember hall' clubstate' member clubstate badminton')
\<and> (SuccessMessage outcome badminton' hall' clubstate clubstate' newMember)
\<or> (NotMember outcome badminton' hall' clubstate member clubstate')"

definition TotalAddMember :: 
"(STUDENT set) \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => MESSAGE \<Rightarrow> bool"
where 
"TotalAddMember hall' clubstate' newMember clubstate badminton' outcome == (AddMember hall' clubstate' newMember clubstate badminton')
\<and> (SuccessMessage outcome badminton' hall' clubstate clubstate' newMember)
\<or> (IsMember outcome newMember)"

definition HallFull :: 
 "(STUDENT set) \<Rightarrow> MESSAGE \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => bool"
where 
"HallFull hall' outcome clubstate' clubstate badminton' == (card hall = maxPlayers)
\<and> (outcome = hallFull)"

definition TotalEnterHall :: 
"STUDENT \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => STUDENT \<Rightarrow> STUDENT \<Rightarrow> MESSAGE \<Rightarrow> bool"
where 
"TotalEnterHall enterer hall' clubstate' clubstate badminton' newMember member outcome == (EnterHall enterer hall' clubstate' clubstate badminton')
\<and> (SuccessMessage outcome badminton' hall' clubstate clubstate' newMember)
\<or> (NotMember outcome badminton' hall' clubstate member clubstate')
\<or> (AlreadyInHall outcome badminton' hall' clubstate clubstate' enterer)
\<or> (HallFull hall' outcome clubstate' clubstate badminton')"

lemma LeaveHall_L1:
"(\<exists> hall' :: (STUDENT set).
\<exists> clubstate' :: ClubState.
\<exists> clubstate :: ClubState.
\<exists> leaver :: STUDENT.
\<exists> badminton' :: (STUDENT set).
(leaver \<in> hall)
\<and> (hall' = hall - {(leaver)}) 
\<and> (badminton' = badminton)
\<longrightarrow> (hall \<subseteq> badminton) 
\<and> (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton') 
\<and> (card hall' \<le> maxPlayers))"
by auto

lemma AddMember_L2:
"(\<exists> hall' :: (STUDENT set).
\<exists> clubstate' :: ClubState.
\<exists> newMember :: STUDENT.
\<exists> clubstate :: ClubState.
\<exists> badminton' :: (STUDENT set).
(newMember \<notin> badminton)
\<and> (badminton' = badminton \<union> {(newMember)}) 
\<and> (hall' = hall)
\<longrightarrow> (hall \<subseteq> badminton) 
\<and> (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton') 
\<and> (card hall' \<le> maxPlayers))"
by auto


lemma EnterHall_L3:
"(\<exists> enterer :: STUDENT.
\<exists> hall' :: (STUDENT set).
\<exists> clubstate' :: ClubState.
\<exists> clubstate :: ClubState.
\<exists> badminton' :: (STUDENT set).
(enterer \<in> badminton) 
\<and> (enterer \<notin> hall) 
\<and> (card hall < maxPlayers)
\<and> (hall' = hall \<union> {(enterer)}) 
\<and> (badminton' = badminton)
\<longrightarrow> (hall \<subseteq> badminton) 
\<and> (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton') 
\<and> (card hall' \<le> maxPlayers))"
by blast


lemma RemoveMember_L4:
"(\<exists> hall' :: (STUDENT set).
\<exists> clubstate' :: ClubState.
\<exists> member :: STUDENT.
\<exists> clubstate :: ClubState.
\<exists> badminton' :: (STUDENT set).
(member \<in> badminton)
\<and> (badminton' = badminton - {(member)}) 
\<and> (hall' = hall - {(member)})
\<longrightarrow> (hall \<subseteq> badminton) 
\<and> (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton') 
\<and> (card hall' \<le> maxPlayers))"
by blast

end
end
