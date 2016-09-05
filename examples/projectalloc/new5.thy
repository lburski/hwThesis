theory new5
imports 
Main 

begin 

typedecl PERSON
typedecl TOPIC
datatype MESSAGE = success | isStudent |
 isLecturer | notStudent | isAllocated  |
 noLecAvailable | notAllocated |
 notLecturer | notListedTopic

record ProjectAlloc = 
STUDINTERESTS ::  "(PERSON \<rightharpoonup> (TOPIC list))"
LECINTERESTS ::  "(PERSON \<rightharpoonup> (TOPIC list))"
ALLOCATION :: "(PERSON \<rightharpoonup> PERSON)"
MAXPLACES :: "(PERSON \<rightharpoonup> nat)"

locale projectAlloc = 
fixes studInterests :: "(PERSON \<rightharpoonup> ((nat * TOPIC) set))"
and lecInterests :: "(PERSON \<rightharpoonup> ((nat * TOPIC) set))"
and allocation :: "(PERSON \<rightharpoonup> PERSON)"
and maxPlaces :: "(PERSON \<rightharpoonup> nat)"
assumes
"(dom studInterests) \<inter> (dom lecInterests) = {}"
and "dom allocation \<subseteq> dom studInterests"
and "ran allocation \<subseteq> dom lecInterests"
and "dom maxPlaces = dom lecInterests"
(*and "(\<forall> lec. (lec \<in> dom maxPlaces) \<longrightarrow> 
(True)
(*card (allocation \<rhd> {lec}) \<le> maxPlaces lec)*)
)"*) 
begin

definition SupsDiffer :: 
 "ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON => bool"
where 
"SupsDiffer projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s == (
(\<exists> old new. ((old \<in> dom lecInterests)
\<and> (new \<in> dom lecInterests))
\<longrightarrow> ((the (allocation s) = old)
\<and> (the (allocation s) = new)
\<and> (old \<noteq> new))))"

definition NotListedTopic :: 
 "ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> TOPIC \<Rightarrow> MESSAGE => bool"
where 
"NotListedTopic  projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l t outcome ==
(t \<notin> (Range (the (lecInterests l))))
\<and> (outcome = notListedTopic)"

definition NotLecturer :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> MESSAGE => bool"
where 
"NotLecturer projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l outcome == 
(l \<notin>  dom lecInterests)
\<and> (outcome = notLecturer)"

definition NotAllocated :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> MESSAGE => bool"
where 
"NotAllocated projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s outcome == 
(s \<notin>  dom allocation)
\<and> (outcome = notAllocated)"

definition LecsAvailable :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => TOPIC \<Rightarrow> PERSON set => bool"
where 
"LecsAvailable projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' t ps ==
(ps = ({p \<in> dom lecInterests.
(t \<in> Range (the (lecInterests p)))
\<and> (the (maxPlaces p) > card ({q. the (allocation q) = p}))
}))"

definition IsStudent :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> MESSAGE => bool"
where 
"IsStudent projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s outcome ==
(s \<in> dom studInterests)
\<and> (outcome = isStudent)"

definition NotStudent :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> MESSAGE => bool"
where 
"NotStudent projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s outcome ==
(s \<notin> dom studInterests)
\<and> (outcome = notStudent)"

definition IsLecturer :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> MESSAGE => bool"
where 
"IsLecturer projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s outcome ==
(s \<in> dom lecInterests)
\<and> (outcome = isLecturer)"

definition NoLecsAvailable :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> MESSAGE => bool"
where 
"NoLecsAvailable projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s outcome ==
 (\<exists> sup \<in> dom lecInterests.
(the (maxPlaces sup) > card ({q. the (allocation q) = sup}))
\<and> ((Range (the (studInterests s)) \<inter> Range (the (lecInterests sup)) = {} )))
\<and> (outcome = noLecAvailable)"

definition IsAllocated :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> MESSAGE => bool"
where 
"IsAllocated projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s outcome ==
(s \<notin> dom studInterests)
\<and> (outcome = isAllocated)"

definition InitProjectAlloc :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> (TOPIC list))  => (PERSON \<rightharpoonup> (TOPIC list)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat)  => bool"
where 
"InitProjectAlloc  projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' ==
(lecInterests' = empty)
\<and> (studInterests' = empty)"

definition SuccessMessage :: 
"MESSAGE => bool"
where 
"SuccessMessage outcome == (outcome = success)"

definition RemoveLecsTopic :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> ((nat * TOPIC) set))  => (PERSON \<rightharpoonup> ((nat * TOPIC) set)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) \<Rightarrow> PERSON \<Rightarrow> TOPIC => nat \<Rightarrow> bool"
where 
"RemoveLecsTopic  projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l t x==
(l \<in> dom lecInterests)
\<and> (t \<in> Range (the (lecInterests l)))
\<and> (lecInterests' = lecInterests(l \<mapsto> {p. (p, t) \<in> the (lecInterests l)}))
\<and> (studInterests' = studInterests)
\<and> (allocation' = allocation)
"

definition CS4 :: 
 "(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) == (PO5)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO2)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE3)
\<and> (PO4)"

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE2)
\<and> (PO3)"

lemma CS5_L1:
"(\<exists> (*CS5_VARIABLESANDTYPES*).
(PRE4)
\<and> (PO6)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS4_L2:
"(\<exists> (*CS4_VARIABLESANDTYPES*).
(PO5)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS1_L3:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS3_L4:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS2_L5:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS5_L1:
"(\<exists> (*CS5_VARIABLESANDTYPES*).
(PRE4)
\<and> (PO6)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS4_L2:
"(\<exists> (*CS4_VARIABLESANDTYPES*).
(PO5)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS1_L3:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS3_L4:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS2_L5:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

end
end
