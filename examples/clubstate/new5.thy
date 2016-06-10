theory gpsa1n2
imports 
Main 

begin 
typedecl STUDENT
datatype MESSAGE = success| isMember | notMember | hallFull | inHall | notInHall


record ClubState = 
MAXPLAYERS :: "(STUDENT set)"
HALL :: "(STUDENT set)"
BADMINTON :: "(STUDENT set)"


locale 1n2 = 
fixes maxPlayers :: "(STUDENT set)"
and hall :: "(STUDENT set)"
and badminton :: "(STUDENT set)"
 
assumes
"(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)
maxPlayers = 20"
begin

definition IS1 :: 
 "(STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => bool"
where 
"IS1 hall' clubstate' clubstate badminton' == (badminton' = {}) 
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

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (newMember \<in> badminton)
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

definition IsMember :: 
 "MESSAGE \<Rightarrow> (STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> STUDENT => bool"
where 
"IsMember outcome badminton' hall' clubstate clubstate' newMember == (outcome = success)"

definition TS4 :: 
"(*TS4_TYPES*) => bool"
where 
"TS4 (*TS4_VARIABLES*) == (*TS4_EXPRESSION*)"

definition TS2 :: 
"(*TS2_TYPES*) => bool"
where 
"TS2 (*TS2_VARIABLES*) == (*TS2_EXPRESSION*)"

definition TS1 :: 
"(*TS1_TYPES*) => bool"
where 
"TS1 (*TS1_VARIABLES*) == (*TS1_EXPRESSION*)"

definition HallFull :: 
 "(STUDENT set) \<Rightarrow> MESSAGE \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) => bool"
where 
"HallFull hall' outcome clubstate' clubstate badminton' == (card hall = maxPlayers)
\<and> (outcome = hallFull)"

definition TS3 :: 
"(*TS3_TYPES*) => bool"
where 
"TS3 (*TS3_VARIABLES*) == (*TS3_EXPRESSION*)"

lemma LeaveHall_L1:
"(\<exists> hall' :: (STUDENT set).
\<exists> clubstate' :: ClubState.
\<exists> clubstate :: ClubState.
\<exists> leaver :: STUDENT.
\<exists> badminton' :: (STUDENT set).
(leaver \<in> hall)
\<and> (hall' = hall - {(leaver)}) 
\<and> (badminton' = badminton)
\<and> (hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton') 
 and (card hall' \<le> maxPlayers))"
sorry

lemma AddMember_L2:
"(\<exists> hall' :: (STUDENT set).
\<exists> clubstate' :: ClubState.
\<exists> newMember :: STUDENT.
\<exists> clubstate :: ClubState.
\<exists> badminton' :: (STUDENT set).
(newMember \<notin> badminton)
\<and> (badminton' = badminton \<union> {(newMember)}) 
\<and> (hall' = hall)
\<and> (hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton') 
 and (card hall' \<le> maxPlayers))"
sorry

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
\<and> (hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton') 
 and (card hall' \<le> maxPlayers))"
sorry

lemma RemoveMember_L4:
"(\<exists> hall' :: (STUDENT set).
\<exists> clubstate' :: ClubState.
\<exists> member :: STUDENT.
\<exists> clubstate :: ClubState.
\<exists> badminton' :: (STUDENT set).
(member \<in> badminton)
\<and> (badminton' = badminton - {(member)}) 
\<and> (hall' = hall - {(member)})
\<and> (hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)
\<and> (hall' \<subseteq> badminton') 
 and (card hall' \<le> maxPlayers))"
sorry

end
end
