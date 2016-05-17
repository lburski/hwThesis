\begin{verbatim}
theory modulereg_proof
imports 
Main 

begin 

typedecl PERSON
typedecl MODULE

record ModuleReg = 
STUDENTS :: " PERSON set"
DEGMODULES :: " MODULE set"
TAKING :: "(PERSON * MODULE) set"

locale zml_modulereg = 
fixes students :: " PERSON set"
and degModules :: " MODULE set"
and taking :: "(PERSON * MODULE) set"
assumes "Domain taking \<subseteq> students" 
 and "Range taking \<subseteq> degModules"
begin

definition RegForModule :: 
"ModuleReg => ModuleReg =>  PERSON set =>  
MODULE set => (PERSON * MODULE) set => PERSON
 => MODULE => bool"
where 
"RegForModule modulereg modulereg' students'
degModules' taking' p m ==
 ((
(p \<in> students) 
\<and> (m \<in> degModules) 
\<and> ((p, m) \<notin> taking)))
\<and> ((
(taking' = taking \<union> {(p, m)}) 
\<and> (students' = students) 
\<and> (degModules' = degModules)))"

definition AddStudent :: 
"ModuleReg => ModuleReg =>  PERSON set =>  
MODULE set => (PERSON * MODULE) set => PERSON => bool"
where 
"AddStudent modulereg modulereg' students' 
degModules' taking' p ==
 ((
(p \<notin> students)))
\<and> ((
(students' = students \<union> {(p)}) 
\<and> (degModules' = degModules) 
\<and> (taking' = taking)))"

lemma pre_AddStudent:
"(\<exists> modulereg modulereg' students' degModules' taking'.
AddStudent modulereg modulereg' students' degModules' taking' p)
\<longleftrightarrow> (p \<notin> students)"
apply (unfold AddStudent_def)
apply auto
done

lemma pre_RegForModule:
"(\<exists> modulereg modulereg' students' degModules' taking'.
RegForModule modulereg modulereg' students' degModules' taking' p m)
 \<longleftrightarrow> (p \<in> students)
 \<and> (m \<in> degModules)
 \<and> ((p,m) \<notin> taking)"
 apply (unfold RegForModule_def)
 apply auto
done

end
end

\end{verbatim}