theory gpsa1n2
imports 
Main 

begin 
typedecl STUDENT MODULE TIMESLOT ROOM


record Timetable = 
MODULETT :: "(MODULE \<rightharpoonup> (TIMESLOT rel ROOM))"
STUDENTTT :: "(STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM))"


locale 1n2 = 
fixes moduleTT :: "(MODULE \<rightharpoonup> (TIMESLOT rel ROOM))"
and studentTT :: "(STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM))"
 
assumes
"(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)"
begin

definition IS1 :: 
 "Timetable \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)) \<Rightarrow> Timetable \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)) \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) => bool"
where 
"IS1 timetable' studentTT' moduleTT timetable moduleTT' studentTT == (studentTT' = {}) 
\<and> (moduleTT' = {})"

definition RegForModule :: 
"Timetable \<Rightarrow> STUDENT \<Rightarrow> MODULE \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)) \<Rightarrow> Timetable => bool"
where 
"RegForModule timetable' s m studentTT' moduleTT' timetable ==
 (s \<in> dom studentTT) 
\<and> (m \<in> dom moduleTT) 
\<and> (the (moduleTT m)) 
\<and> (\<inter> dom (the (moduleTT m))
\<and> ((\<exists>newPairs. TIMESLOT \<rightharpoonup> ROOM)) 
\<and> (moduleTT' = moduleTT)"

definition AddStudent :: 
"Timetable \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)) \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> Timetable => bool"
where 
"AddStudent timetable' moduleTT' studentTT' timetable ==
 (s \<notin> dom studentTT)
\<and> (studentTT' = studentTT (s \<mapsto> )) 
\<and> (moduleTT' = moduleTT)"

definition DescheduleModule :: 
"Timetable \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)) \<Rightarrow> MODULE \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> Timetable => bool"
where 
"DescheduleModule timetable' moduleTT' m studentTT' timetable ==
 (m \<in> dom moduleTT) 
\<and> (the (moduleTT m))
\<and> (moduleTT' = moduleTT oplus {(m mapsto {})}) 
\<and> (studentTT')"

definition ScheduleModule :: 
"Timetable \<Rightarrow> (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)) \<Rightarrow> MODULE \<Rightarrow> (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)) \<Rightarrow> Timetable => bool"
where 
"ScheduleModule timetable' moduleTT' m studentTT' timetable ==
 (m \<in> dom moduleTT) 
\<and> (the (moduleTT m))
\<and> (\<exists>schedule. TIMESLOT rel ROOM) 
\<and> (studentTT' = studentTT)"

lemma RegForModule_L1:
"(\<exists> timetable' :: Timetable.
\<exists> s :: STUDENT.
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)).
\<exists> timetable :: Timetable.
(s \<in> dom studentTT) 
\<and> (m \<in> dom moduleTT) 
\<and> (the (moduleTT m)) 
\<and> (\<inter> dom (the (moduleTT m))
\<and> ((\<exists>newPairs. TIMESLOT \<rightharpoonup> ROOM)) 
\<and> (moduleTT' = moduleTT)
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT))
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)'))"
sorry

lemma AddStudent_L2:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)).
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
(s \<notin> dom studentTT)
\<and> (studentTT' = studentTT (s \<mapsto> )) 
\<and> (moduleTT' = moduleTT)
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT))
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)'))"
sorry

lemma DescheduleModule_L3:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)).
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
(m \<in> dom moduleTT) 
\<and> (the (moduleTT m))
\<and> (moduleTT' = moduleTT oplus {(m mapsto {})}) 
\<and> (studentTT')
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT))
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)'))"
sorry

lemma ScheduleModule_L4:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)).
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
(m \<in> dom moduleTT) 
\<and> (the (moduleTT m))
\<and> (\<exists>schedule. TIMESLOT rel ROOM) 
\<and> (studentTT' = studentTT)
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT))
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)'))"
sorry

lemma RegForModule_L1:
"(\<exists> timetable' :: Timetable.
\<exists> s :: STUDENT.
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)).
\<exists> timetable :: Timetable.
(s \<in> dom studentTT) 
\<and> (m \<in> dom moduleTT) 
\<and> (the (moduleTT m)) 
\<and> (\<inter> dom (the (moduleTT m))
\<and> ((\<exists>newPairs. TIMESLOT \<rightharpoonup> ROOM)) 
\<and> (moduleTT' = moduleTT)
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT))
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)'))"
sorry

lemma AddStudent_L2:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)).
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
(s \<notin> dom studentTT)
\<and> (studentTT' = studentTT (s \<mapsto> )) 
\<and> (moduleTT' = moduleTT)
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT))
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)'))"
sorry

lemma DescheduleModule_L3:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)).
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
(m \<in> dom moduleTT) 
\<and> (the (moduleTT m))
\<and> (moduleTT' = moduleTT oplus {(m mapsto {})}) 
\<and> (studentTT')
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT))
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)'))"
sorry

lemma ScheduleModule_L4:
"(\<exists> timetable' :: Timetable.
\<exists> moduleTT' :: (MODULE \<rightharpoonup> (TIMESLOT rel ROOM)).
\<exists> m :: MODULE.
\<exists> studentTT' :: (STUDENT \<rightharpoonup> (TIMESLOT \<rightharpoonup> ROOM)).
\<exists> timetable :: Timetable.
(m \<in> dom moduleTT) 
\<and> (the (moduleTT m))
\<and> (\<exists>schedule. TIMESLOT rel ROOM) 
\<and> (studentTT' = studentTT)
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT))
\<and> ((\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)\<and>(\<forall>r s. ran moduleTT) 
 and (\<forall>s. dom studentTT)'))"
sorry

end
end
