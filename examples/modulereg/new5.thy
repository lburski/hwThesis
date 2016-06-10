theory new5
imports 
Main 

begin 
typedecl PERSON 
typedecl MODULE

record ModuleReg = 
STUDENTS :: " PERSON set"
DEGMODULES :: " MODULE set"
TAKING :: "(PERSON * MODULE) set"

locale gpsaModuleReg = 
fixes students :: " PERSON set"
and degModules :: " MODULE set"
and taking :: "(PERSON * MODULE) set"
assumes "Domain taking \<subseteq> students" 
 and "Range taking \<subseteq> degModules"
begin

definition RegForModule :: 
"ModuleReg \<Rightarrow> ModuleReg \<Rightarrow> PERSON \<Rightarrow> MODULE => MODULE set \<Rightarrow> PERSON set \<Rightarrow> (PERSON * MODULE) set \<Rightarrow> bool"
where 
"RegForModule modulereg modulereg' p m degModules' students' taking' ==
(p \<in> students) 
\<and> (m \<in> degModules) 
\<and> ((p, m) \<notin> taking)
\<and> (taking' = taking \<union> {(p, m)}) 
\<and> (students' = students) 
\<and> (degModules' = degModules)"

definition AddStudent :: 
"ModuleReg \<Rightarrow> ModuleReg => PERSON \<Rightarrow>  MODULE set \<Rightarrow> PERSON set \<Rightarrow> (PERSON * MODULE) set \<Rightarrow> bool"
where 
"AddStudent modulereg modulereg' p degModules' students' taking' ==
 (
(p \<notin> students)
\<and> (students' = students \<union> {(p)}) 
\<and> (degModules' = degModules) 
\<and> (taking' = taking))"

lemma RegForModule_L1:
"(\<exists> degModules:: MODULE set.
\<exists> students :: PERSON set.
\<exists> taking :: (PERSON * MODULE) set.
\<exists> p :: PERSON.
\<exists> degModules':: MODULE set.
\<exists> students' :: PERSON set.
\<exists> taking' :: (PERSON * MODULE) set.
\<exists> m :: MODULE.
(
(p \<in> students) 
\<and> (m \<in> degModules) 
\<and> ((p, m) \<notin> taking)
\<and> (taking' = taking \<union> {(p, m)}) 
\<and> (students' = students) 
\<and> (degModules' = degModules))
\<and> (Domain taking \<subseteq> students)
\<and> (Range taking \<subseteq> degModules)
\<and> (Domain taking' \<subseteq> students')
\<and> (Range taking' \<subseteq> degModules')
)"
sorry

lemma AddStudent_L2:
"(\<exists> degModules:: MODULE set.
\<exists> students :: PERSON set.
\<exists> taking :: (PERSON * MODULE) set.
\<exists> p :: PERSON.
\<exists> degModules':: MODULE set.
\<exists> students' :: PERSON set.
\<exists> taking' :: (PERSON * MODULE) set.
 (
 (students' = students \<union> {(p)}) 
\<and> (degModules' = degModules) 
\<and> (taking' = taking))
\<and> (Domain taking \<subseteq> students)
\<and> (Range taking \<subseteq> degModules)
\<and> (Domain taking' \<subseteq> students')
\<and> (Range taking' \<subseteq> degModules')
)"
sorry

end
end
