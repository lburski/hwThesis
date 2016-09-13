theory new6
imports 
Main 

begin 
typedecl STUDENT
typedecl MODULE
typedecl TIMESLOT
typedecl ROOM
typedecl X
typedecl Y
typedecl Z

record Timetable = 
MODULETT :: "(MODULE \<rightharpoonup> (TIMESLOT * ROOM) set)"
STUDENTTT :: "(STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM))"

definition allPairs ::
"('X \<rightharpoonup> ('Y * 'Z) set) \<Rightarrow> ('Y * 'Z) set"
where
" allPairs f == \<Union>{yz. yz \<in> ran f} "

locale thetimetable  = 
fixes moduleTT :: "(MODULE \<rightharpoonup> (TIMESLOT * ROOM) set)"
and studentTT :: "(STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM))"

assumes
"(\<forall> r \<in> ran moduleTT. \<forall> s \<in> ran moduleTT.
disjoint [r,s])"
(*and allPairs studentTT \<subseteq> allPairs moduleTT*)
(*and "allPairs (studentTT)"*)
and "(\<forall> s \<in> dom studentTT. \<forall> m \<in> dom moduleTT.
((the (studentTT s)) (*\<inter> (the (moduleTT m)))*)) \<noteq> empty)
\<longrightarrow> ((dom (the (studentTT s))) \<inter> (Domain (the (moduleTT m))) = Domain (the (moduleTT m)))"

begin


definition initTimetable :: 
 "Timetable \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> Timetable \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set)  => bool"
where 
"initTimetable timetable' studentTT' timetable moduleTT'  == (studentTT' = empty)
\<and> (moduleTT' = empty)"

definition RegForModule :: 
"Timetable \<Rightarrow> STUDENT \<Rightarrow> MODULE \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set)  => bool"
where 
"RegForModule timetable' s m studentTT' moduleTT'  ==
(s \<in> dom studentTT)
\<and> (m \<in> dom moduleTT)
\<and> (the (moduleTT m) \<noteq> {})
\<and> ((dom (the (studentTT s))) \<inter> (Domain (the (moduleTT m))) \<noteq> {})
\<and> (\<exists> newPairs :: TIMESLOT \<rightharpoonup> ROOM.
\<exists> newPairss :: (TIMESLOT * ROOM) set.
(dom newPairs = (Domain (the (moduleTT m))))
\<and> (newPairss \<subseteq>  (the (moduleTT m)))
\<and> studentTT' = studentTT(s \<mapsto> (the (studentTT s)) ++ newPairs ))
\<and> (moduleTT' = moduleTT)"

definition AddStudent :: 
"Timetable \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set) \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> Timetable => STUDENT \<Rightarrow> bool"
where 
"AddStudent timetable' moduleTT' studentTT' timetable s  ==
 (s \<notin> dom studentTT)
\<and> (studentTT' = studentTT (s  \<mapsto> empty))
\<and> (moduleTT' = moduleTT)"

definition DescheduleModule :: 
"Timetable \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set) \<Rightarrow> MODULE \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> Timetable => bool"
where 
"DescheduleModule timetable' moduleTT' m studentTT' timetable ==
(m \<in> dom moduleTT)
\<and> (the (moduleTT m) \<noteq> {}) 
\<and> (moduleTT' = moduleTT (m \<mapsto> {}))
(*\<and> (student TT' = \<Union> {s \<in> dom studentTT. {s \<mapsto> (studentTT s}})*)"

definition ScheduleModule :: 
"Timetable \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set) \<Rightarrow> MODULE \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> Timetable => bool"
where 
"ScheduleModule timetable' moduleTT' m studentTT' timetable ==
 (m \<in> dom moduleTT) 
\<and> (the (moduleTT m) = {})
\<and> (\<exists> schedule :: (TIMESLOT * ROOM) set.
(allPairs moduleTT  \<inter> schedule = {})
\<and> moduleTT' = moduleTT (m \<mapsto> schedule))
\<and> (studentTT' = studentTT)"

lemma RegForModule_L1:
"(\<exists> timetable' :: Timetable.
\<exists> s :: STUDENT.
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set).
\<exists> timetable :: Timetable.
(s \<in> dom studentTT)
\<and> (m \<in> dom moduleTT)
\<and> (the (moduleTT m) \<noteq> {})
\<and> (((dom (the (studentTT s))) \<inter> (Domain (the (moduleTT m)))) \<noteq> {})
\<and> (\<exists> newPairs :: TIMESLOT \<rightharpoonup> ROOM.
(dom newPairs = (Domain (the (moduleTT m))))
(*\<and> (newPairs  ((moduleTT m)))*)
(*\<and> studentTT' = (s \<mapsto> (studentTT s) newPairs))*))
\<and> (moduleTT' = moduleTT)
\<longrightarrow> (\<forall> s \<in> dom studentTT. \<forall> m \<in> dom moduleTT.
(the (studentTT s) (*\<inter> the (moduleTT m)*) \<noteq> empty)
\<longrightarrow> (dom (the (studentTT s))) (*moduleTT m*) = (dom (the (studentTT s)))))
\<and> (\<forall> s \<in> dom studentTT'. \<forall> m \<in> dom moduleTT'.
(the (studentTT' s) (*\<inter> the (moduleTT' m)*) \<noteq> empty)
\<longrightarrow> (dom (the (studentTT' s))) (*moduleTT' m*) = (dom (the (studentTT' s))))"
by smt

lemma AddStudent_L2:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set).
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
 (s \<notin> dom studentTT)
\<and> (studentTT' = studentTT (s  \<mapsto> empty))
\<and> (moduleTT' = moduleTT)
\<longrightarrow> (\<forall> s \<in> dom studentTT. \<forall> m \<in> dom moduleTT.
(the (studentTT s) (*\<inter> the (moduleTT m)*) \<noteq> empty)
\<longrightarrow> (dom (the (studentTT s))) (*moduleTT m*) = (dom (the (studentTT s)))))
\<and> (\<forall> s \<in> dom studentTT'. \<forall> m \<in> dom moduleTT'.
(the (studentTT' s) (*\<inter> the (moduleTT' m)*) \<noteq> empty)
\<longrightarrow> (dom (the (studentTT' s))) (*moduleTT' m*) = (dom (the (studentTT' s))))"
by smt

lemma DescheduleModule_L3:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set).
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
(m \<in> dom moduleTT)
\<and> (the (moduleTT m) \<noteq> {}) 
\<and> (moduleTT' = moduleTT (m \<mapsto> {}))
(*\<and> (student TT' = \<Union> {s \<in> dom studentTT. {s \<mapsto> (studentTT s}})*)
\<longrightarrow> (\<forall> s \<in> dom studentTT. \<forall> m \<in> dom moduleTT.
(the (studentTT s) (*\<inter> the (moduleTT m)*) \<noteq> empty)
\<longrightarrow> (dom (the (studentTT s))) (*moduleTT m*) = (dom (the (studentTT s)))))
\<and> (\<forall> s \<in> dom studentTT'. \<forall> m \<in> dom moduleTT'.
(the (studentTT' s) (*\<inter> the (moduleTT' m)*) \<noteq> empty)
\<longrightarrow> (dom (the (studentTT' s))) (*moduleTT' m*) = (dom (the (studentTT' s))))"
by blast

lemma ScheduleModule_L4:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT * ROOM) set).
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
 (m \<in> dom moduleTT) 
\<and> (the (moduleTT m) = {})
\<and> (\<exists> schedule :: (TIMESLOT * ROOM) set.
(allPairs moduleTT  \<inter> schedule = {})
\<and> moduleTT' = moduleTT (m \<mapsto> schedule))
\<and> (studentTT' = studentTT)
\<longrightarrow> (\<forall> s \<in> dom studentTT. \<forall> m \<in> dom moduleTT.
(the (studentTT s) (*\<inter> the (moduleTT m)*) \<noteq> empty)
\<longrightarrow> (dom (the (studentTT s))) (*moduleTT m*) = (dom (the (studentTT s)))))
\<and> (\<forall> s \<in> dom studentTT'. \<forall> m \<in> dom moduleTT'.
(the (studentTT' s) (*\<inter> the (moduleTT' m)*) \<noteq> empty)
\<longrightarrow> (dom (the (studentTT' s))) (*moduleTT' m*) = (dom (the (studentTT' s))))"
by smt


end
end
