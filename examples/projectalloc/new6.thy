theory new6
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
and "(\<forall> lec \<in> dom maxPlaces . (card ({l. the (allocation l) = lec})) \<le> the (maxPlaces lec))"
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

(*CS5*)
definition RemoveLecsTopic :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> ((nat * TOPIC) set))  => (PERSON \<rightharpoonup> ((nat * TOPIC) set)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) \<Rightarrow> PERSON \<Rightarrow> TOPIC => nat \<Rightarrow> bool"
where 
"RemoveLecsTopic  projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l t x==
(l \<in> dom lecInterests)
\<and> (t \<in> Range (the (lecInterests l)))
(*\<and> (lecInterests' = lecInterests(l \<mapsto> {p. (p, t) \<in> the (lecInterests l)}))*)
\<and> (studInterests' = studInterests)
\<and> (allocation' = allocation)"

definition DeAllocate :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> ((nat * TOPIC) set))  => (PERSON \<rightharpoonup> ((nat * TOPIC) set)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> bool"
where 
"DeAllocate projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s ==
(\<exists> sup \<in> dom lecInterests. (the (allocation s) = sup)
(*\<and> (allocation' = allocation - {s,sup})*))
\<and> (studInterests' = studInterests)
\<and> (lecInterests' = lecInterests)"

definition AddStudent :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> ((nat * TOPIC) set))  => (PERSON \<rightharpoonup> ((nat * TOPIC) set)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => ((nat * TOPIC) set) \<Rightarrow> PERSON \<Rightarrow> bool"
where 
"AddStudent projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' ts s ==
 (s \<notin> (dom studInterests \<union> dom lecInterests))
\<and> (studInterests' = studInterests(s \<mapsto> ts))
\<and> (lecInterests' = lecInterests)
\<and> (allocation' = allocation)
\<and> (maxPlaces' = maxPlaces)"

definition Allocate :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> ((nat * TOPIC) set))  => (PERSON \<rightharpoonup> ((nat * TOPIC) set)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON => bool"
where 
"Allocate projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' s ==
 (s \<in> dom studInterests)
\<and> (s \<notin> dom allocation)
\<and> ((\<exists> sup \<in> dom lecInterests. \<exists> t :: TOPIC. \<exists> i j :: nat. 
(the (maxPlaces sup) > (card ({q. the (allocation q) = sup})))
\<and> ((i, t) \<in> the (studInterests s))
\<and> ((j, t) \<in> the (lecInterests sup))
\<longrightarrow>
(\<forall> lec \<in> dom lecInterests. \<forall> k :: nat. (
(the (maxPlaces lec) > (card ({j. the (allocation j) = lec}))))
\<longrightarrow> (((k, t) \<in> the (lecInterests lec)) \<longrightarrow> (k \<ge> j)
\<and> ((*ran(1..i-1 studInterests s) \<inter>*) Range (the (lecInterests lec)) = {}))
\<and> (allocation' = allocation(s \<mapsto> sup)))))
\<and> (studInterests' = studInterests)
\<and> (lecInterests' = lecInterests)"

definition AddLecturer :: 
"ProjectAlloc => ProjectAlloc => (PERSON \<rightharpoonup> ((nat * TOPIC) set))  => (PERSON \<rightharpoonup> ((nat * TOPIC) set)) => (PERSON \<rightharpoonup> PERSON) => (PERSON \<rightharpoonup> nat) => PERSON \<Rightarrow> nat \<Rightarrow> ((nat * TOPIC) set) \<Rightarrow> bool"
where 
"AddLecturer projectalloc projectalloc' studInterests' lecInterests' allocation' maxPlaces' l maxAlloc ts ==
 (l \<notin> ((dom studInterests) \<union> (dom lecInterests)))
\<and> (lecInterests' = lecInterests(l \<mapsto> ts))
\<and> (maxPlaces' = maxPlaces(l \<mapsto> maxAlloc))
\<and> (studInterests' = studInterests)
\<and> (allocation' = allocation)"

lemma RemoveLecsTopic_L1:
"(\<exists> projectalloc :: ProjectAlloc.
\<exists> projectalloc' :: ProjectAlloc.
\<exists> studInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> lecInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> allocation' :: (PERSON \<rightharpoonup> PERSON).
\<exists> maxPlaces' :: (PERSON \<rightharpoonup> nat).
\<exists> l :: PERSON.
\<exists> t :: TOPIC.
\<exists> x :: nat.
(l \<in> dom lecInterests)
\<and> (t \<in> Range (the (lecInterests l)))
(*\<and> (lecInterests' = lecInterests(l \<mapsto> {p. (p, t) \<in> the (lecInterests l)}))*)
\<and> (studInterests' = studInterests)
\<and> (allocation' = allocation)
\<longrightarrow> (((dom studInterests) \<inter> (dom lecInterests) = {})
\<and>(dom allocation \<subseteq> dom studInterests)
\<and>(ran allocation \<subseteq> dom lecInterests)
\<and>(dom maxPlaces = dom lecInterests)
\<and> (\<forall> lec \<in> dom maxPlaces. (card ({l. the (allocation l) = lec})) \<le> the (maxPlaces lec))
\<and> ((dom studInterests') \<inter> (dom lecInterests') = {})
\<and>(dom allocation' \<subseteq> dom studInterests')
\<and>(ran allocation' \<subseteq> dom lecInterests')
\<and>(dom maxPlaces' = dom lecInterests')
\<and> (\<forall> lec \<in> dom maxPlaces'. (card ({l. the (allocation' l) = lec})) \<le> the (maxPlaces' lec))))"
by (metis (full_types) dom_restrict empty_iff inf_bot_right)

lemma DeAllocate_L2:
"(\<exists> projectalloc :: ProjectAlloc.
\<exists> projectalloc' :: ProjectAlloc.
\<exists> studInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> lecInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> allocation' :: (PERSON \<rightharpoonup> PERSON).
\<exists> maxPlaces' :: (PERSON \<rightharpoonup> nat).
\<exists> s :: PERSON.
(\<exists> sup \<in> dom lecInterests. (the (allocation s) = sup)
(*\<and> (allocation' = allocation - {s,sup})*))
\<and> (studInterests' = studInterests)
\<and> (lecInterests' = lecInterests)
\<longrightarrow> (((dom studInterests) \<inter> (dom lecInterests) = {})
\<and>(dom allocation \<subseteq> dom studInterests)
\<and>(ran allocation \<subseteq> dom lecInterests)
\<and>(dom maxPlaces = dom lecInterests)
\<and> (\<forall> lec \<in> dom maxPlaces. (card ({l. the (allocation l) = lec})) \<le> the (maxPlaces lec))
\<and> ((dom studInterests') \<inter> (dom lecInterests') = {})
\<and>(dom allocation' \<subseteq> dom studInterests')
\<and>(ran allocation' \<subseteq> dom lecInterests')
\<and>(dom maxPlaces' = dom lecInterests')
\<and> (\<forall> lec \<in> dom maxPlaces'. (card ({l. the (allocation' l) = lec})) \<le> the (maxPlaces' lec))))"
by auto

lemma AddStudent_L3:
"(\<exists> projectalloc :: ProjectAlloc.
\<exists> projectalloc' :: ProjectAlloc.
\<exists> studInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> lecInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> allocation' :: (PERSON \<rightharpoonup> PERSON).
\<exists> maxPlaces' :: (PERSON \<rightharpoonup> nat).
\<exists> ts :: ((nat * TOPIC) set).
\<exists> s :: PERSON.
 (s \<notin> (dom studInterests \<union> dom lecInterests))
\<and> (studInterests' = studInterests(s \<mapsto> ts))
\<and> (lecInterests' = lecInterests)
\<and> (allocation' = allocation)
\<and> (maxPlaces' = maxPlaces)
\<longrightarrow> (((dom studInterests) \<inter> (dom lecInterests) = {})
\<and>(dom allocation \<subseteq> dom studInterests)
\<and>(ran allocation \<subseteq> dom lecInterests)
\<and>(dom maxPlaces = dom lecInterests)
\<and> (\<forall> lec \<in> dom maxPlaces. (card ({l. the (allocation l) = lec})) \<le> the (maxPlaces lec))
\<and> ((dom studInterests') \<inter> (dom lecInterests') = {})
\<and>(dom allocation' \<subseteq> dom studInterests')
\<and>(ran allocation' \<subseteq> dom lecInterests')
\<and>(dom maxPlaces' = dom lecInterests')
\<and> (\<forall> lec \<in> dom maxPlaces'. (card ({l. the (allocation' l) = lec})) \<le> the (maxPlaces' lec))))"
by fastforce

lemma Allocate_L4:
"(\<exists> projectalloc :: ProjectAlloc.
\<exists> projectalloc' :: ProjectAlloc.
\<exists> studInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> lecInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> allocation' :: (PERSON \<rightharpoonup> PERSON).
\<exists> maxPlaces' :: (PERSON \<rightharpoonup> nat).
\<exists> s :: PERSON.
 (s \<in> dom studInterests)
\<and> (s \<notin> dom allocation)
\<and> ((\<exists> sup \<in> dom lecInterests. \<exists> t :: TOPIC. \<exists> i j :: nat. 
(the (maxPlaces sup) > (card ({q. the (allocation q) = sup})))
\<and> ((i, t) \<in> the (studInterests s))
\<and> ((j, t) \<in> the (lecInterests sup))
\<longrightarrow>
(\<forall> lec \<in> dom lecInterests. \<forall> k :: nat. (
(the (maxPlaces lec) > (card ({j. the (allocation j) = lec}))))
\<longrightarrow> (((k, t) \<in> the (lecInterests lec)) \<longrightarrow> (k \<ge> j)
\<and> ((*ran(1..i-1 studInterests s) \<inter>*) Range (the (lecInterests lec)) = {}))
\<and> (allocation' = allocation(s \<mapsto> sup)))))
\<and> (studInterests' = studInterests)
\<and> (lecInterests' = lecInterests)
\<longrightarrow> (((dom studInterests) \<inter> (dom lecInterests) = {})
\<and>(dom allocation \<subseteq> dom studInterests)
\<and>(ran allocation \<subseteq> dom lecInterests)
\<and>(dom maxPlaces = dom lecInterests)
\<and> (\<forall> lec \<in> dom maxPlaces. (card ({l. the (allocation l) = lec})) \<le> the (maxPlaces lec))
\<and> ((dom studInterests') \<inter> (dom lecInterests') = {})
\<and>(dom allocation' \<subseteq> dom studInterests')
\<and>(ran allocation' \<subseteq> dom lecInterests')
\<and>(dom maxPlaces' = dom lecInterests')
\<and> (\<forall> lec \<in> dom maxPlaces'. (card ({l. the (allocation' l) = lec})) \<le> the (maxPlaces' lec))))"
using dom_empty by fastforce

lemma AddLecturer_L5:
"(\<exists> projectalloc :: ProjectAlloc.
\<exists> projectalloc' :: ProjectAlloc.
\<exists> studInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> lecInterests' :: (PERSON \<rightharpoonup> ((nat * TOPIC) set)).
\<exists> allocation' :: (PERSON \<rightharpoonup> PERSON).
\<exists> maxPlaces' :: (PERSON \<rightharpoonup> nat).
\<exists> l :: PERSON.
\<exists> maxAlloc :: nat.
\<exists> ts :: ((nat * TOPIC) set).
 (l \<notin> ((dom studInterests) \<union> (dom lecInterests)))
\<and> (lecInterests' = lecInterests(l \<mapsto> ts))
\<and> (maxPlaces' = maxPlaces(l \<mapsto> maxAlloc))
\<and> (studInterests' = studInterests)
\<and> (allocation' = allocation)
\<longrightarrow> (((dom studInterests) \<inter> (dom lecInterests) = {})
\<and>(dom allocation \<subseteq> dom studInterests)
\<and>(ran allocation \<subseteq> dom lecInterests)
\<and>(dom maxPlaces = dom lecInterests)
\<and> (\<forall> lec \<in> dom maxPlaces. (card ({l. the (allocation l) = lec})) \<le> the (maxPlaces lec))
\<and> ((dom studInterests') \<inter> (dom lecInterests') = {})
\<and>(dom allocation' \<subseteq> dom studInterests')
\<and>(ran allocation' \<subseteq> dom lecInterests')
\<and>(dom maxPlaces' = dom lecInterests')
\<and> (\<forall> lec \<in> dom maxPlaces'. (card ({l. the (allocation' l) = lec})) \<le> the (maxPlaces' lec))))"
by (metis (full_types) dom_empty dom_empty dom_empty dom_eq_singleton_conv 
dom_restrict inf.idem insert_not_empty)


end
end
