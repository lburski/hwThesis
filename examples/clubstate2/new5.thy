theory gpsa1n2
imports 
Main 

begin 
typedecl STUDENT


record ClubState = 
MAXPLAYERS :: "(STUDENT set)"
HALL :: "(STUDENT set)"
BADMINTON :: "(STUDENT set)"


locale 1n2 = 
fixes 
maxPlayers :: "(STUDENT set)"
and hall :: "(STUDENT set)"
and badminton :: "(STUDENT set)"
 
assumes
"(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)([onCourt Range waiting ]partition hall)maxPlayers = 20"
begin

definition IS1 :: 
 "(STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) \<Rightarrow> iseq STUDENT \<Rightarrow> ClubState2 \<Rightarrow> ClubState2 => bool"
where 
"IS1 badminton' hall' clubstate clubstate' onCourt' waiting' clubstate2' clubstate2 == (badminton' = {})"

definition NewGame :: 
"(STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) \<Rightarrow> iseq STUDENT \<Rightarrow> ClubState2 \<Rightarrow> ClubState2 => bool"
where 
"NewGame badminton' hall' clubstate clubstate' onCourt' waiting' clubstate2' clubstate2 ==
 (onCourt = {}) 
\<and> (card waiting \<ge> 2) 
\<and> (card waiting) 
\<and> (card waiting) 
\<and> (hd waiting \<in> onCourt')
\<and> (onCourt') 
\<and> (waiting' = waiting) 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)"

definition LeaveHall :: 
"(STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> STUDENT \<Rightarrow> (STUDENT set) \<Rightarrow> iseq STUDENT \<Rightarrow> ClubState2 \<Rightarrow> ClubState2 => bool"
where 
"LeaveHall badminton' hall' clubstate clubstate' p onCourt' waiting' clubstate2' clubstate2 ==
 (p \<in> Range waiting)
\<and> (waiting') 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)"

definition FinishGame :: 
"(STUDENT set) \<Rightarrow> (STUDENT set) \<Rightarrow> ClubState \<Rightarrow> ClubState \<Rightarrow> (STUDENT set) \<Rightarrow> iseq STUDENT \<Rightarrow> ClubState2 \<Rightarrow> ClubState2 => bool"
where 
"FinishGame badminton' hall' clubstate clubstate' onCourt' waiting' clubstate2' clubstate2 ==
 (onCourt \<noteq> {}) 
\<and> (onCourt' = {})
\<and> (\<exists>s) 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)"

lemma NewGame_L1:
"(\<exists> badminton' :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> clubstate :: ClubState.
\<exists> clubstate' :: ClubState.
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting' :: iseq STUDENT.
\<exists> clubstate2' :: ClubState2.
\<exists> clubstate2 :: ClubState2.
(onCourt = {}) 
\<and> (card waiting \<ge> 2) 
\<and> (card waiting) 
\<and> (card waiting) 
\<and> (hd waiting \<in> onCourt')
\<and> (onCourt') 
\<and> (waiting' = waiting) 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall))
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)'))"
sorry

lemma LeaveHall_L2:
"(\<exists> badminton' :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> clubstate :: ClubState.
\<exists> clubstate' :: ClubState.
\<exists> p :: STUDENT.
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting' :: iseq STUDENT.
\<exists> clubstate2' :: ClubState2.
\<exists> clubstate2 :: ClubState2.
(p \<in> Range waiting)
\<and> (waiting') 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall))
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)'))"
sorry

lemma FinishGame_L3:
"(\<exists> badminton' :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> clubstate :: ClubState.
\<exists> clubstate' :: ClubState.
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting' :: iseq STUDENT.
\<exists> clubstate2' :: ClubState2.
\<exists> clubstate2 :: ClubState2.
(onCourt \<noteq> {}) 
\<and> (onCourt' = {})
\<and> (\<exists>s) 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall))
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)'))"
sorry

lemma NewGame_L1:
"(\<exists> badminton' :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> clubstate :: ClubState.
\<exists> clubstate' :: ClubState.
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting' :: iseq STUDENT.
\<exists> clubstate2' :: ClubState2.
\<exists> clubstate2 :: ClubState2.
(onCourt = {}) 
\<and> (card waiting \<ge> 2) 
\<and> (card waiting) 
\<and> (card waiting) 
\<and> (hd waiting \<in> onCourt')
\<and> (onCourt') 
\<and> (waiting' = waiting) 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall))
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)'))"
sorry

lemma LeaveHall_L2:
"(\<exists> badminton' :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> clubstate :: ClubState.
\<exists> clubstate' :: ClubState.
\<exists> p :: STUDENT.
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting' :: iseq STUDENT.
\<exists> clubstate2' :: ClubState2.
\<exists> clubstate2 :: ClubState2.
(p \<in> Range waiting)
\<and> (waiting') 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall))
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)'))"
sorry

lemma FinishGame_L3:
"(\<exists> badminton' :: (STUDENT set).
\<exists> hall' :: (STUDENT set).
\<exists> clubstate :: ClubState.
\<exists> clubstate' :: ClubState.
\<exists> onCourt' :: (STUDENT set).
\<exists> waiting' :: iseq STUDENT.
\<exists> clubstate2' :: ClubState2.
\<exists> clubstate2 :: ClubState2.
(onCourt \<noteq> {}) 
\<and> (onCourt' = {})
\<and> (\<exists>s) 
\<and> (hall' = hall) 
\<and> (badminton' = badminton)
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall))
\<and> ((hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)\<and>(hall \<subseteq> badminton) 
 and (card hall \<le> maxPlayers)\<and>([onCourt Range waiting ]partition hall)'))"
sorry

end
end
