theory 6
imports 
Main 

begin 
typedecl LINE
typedecl DECLARATION 
typedecl EXPRESSION 
typedecl DEFINITION
typedecl VARS

record ZcgaState = 
Declarations :: "(VARS * EXPRESSION) set"
Expressions :: "(LINE set)"
Definitions :: "(LINE set)"
DefinedConstants :: "(VARS set)"
TERMDECLARATION :: "(VARS * EXPRESSION) set"
SETDECLARATION :: "(VARS * EXPRESSION) set"
TERMS :: "(VARS set)"
SETS :: "(VARS set)"
DVAR :: "(VARS set)"


locale ZCGa = 
fixes declarations :: "(VARS * EXPRESSION) set"
and expressions :: "(LINE set)"
and definitions :: "(LINE set)"
and definedConstants :: "(VARS set)"
and TermDeclaration :: "(VARS * EXPRESSION) set"
and SetDeclaration :: "(VARS * EXPRESSION) set"
and terms :: "(VARS set)"
and sets :: "(VARS set)"
and dvar :: "(VARS set)"
 
assumes
" TermDeclaration \<subseteq> declarations"
and "SetDeclaration \<subseteq> declarations"
and "dvars \<subset> sets \<union> terms"
and "sets \<inter> terms = {}"
begin

definition InitZcgaState :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINE set)\<Rightarrow> (LINE set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> bool"
where 
"InitZcgaState zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' == (declarations' = {}) 
\<and> (expressions' = {}) 
\<and> (definitions' = {}) 
\<and> (definedConstants' = {}) 
\<and> (TermDeclaration' = {}) 
\<and> (SetDeclaration' = {}) 
\<and> (terms' = {}) 
\<and> (sets' = {}) 
\<and> (dvar' = {})"

definition CorrectExpression :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINE set)\<Rightarrow> (LINE set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> LINE \<Rightarrow> 
(VARS set) \<Rightarrow> ((VARS set) \<rightharpoonup> LINE) \<Rightarrow>  bool"
where 
"CorrectExpression zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar'
 newExpression expressParameters expressConstant ==
 (expressParameters \<subseteq> sets \<union> terms) 
\<and> (expressParameters \<noteq> {})
\<and> (newExpression = the (expressConstant expressParameters))
\<and> (expressions' = expressions \<union> {newExpression})"

definition CorrectConstantSet :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINE set)\<Rightarrow> (LINE set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> VARS \<Rightarrow>
(VARS set) \<Rightarrow> ((VARS set) \<rightharpoonup> VARS) \<Rightarrow>  bool"
where 
"CorrectConstantSet zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' newset setParameters setConstant ==
(setParameters \<subseteq> sets \<union> terms)
\<and> (setParameters \<noteq> {})
\<and> (newset = the (setConstant setParameters))
\<and> (sets' = sets \<union> {newset})"

definition CorrectDefinitions :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINE set)\<Rightarrow> (LINE set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
(VARS set) \<Rightarrow> VARS \<Rightarrow> ((VARS set) \<rightharpoonup> VARS) => ((VARS set) \<rightharpoonup> LINE) \<Rightarrow> bool"
where 
"CorrectDefinitions zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' parameters newConstant definedSet newdefinition ==
 (newConstant \<notin> sets)
\<and> (parameters \<subseteq> sets \<union> terms)
\<and> (newConstant = the (definedSet parameters)) 
\<and> (definedConstants' = definedConstants \<union> {(newConstant)})
\<and> (sets' = sets \<union> {newConstant})
\<and> (definitions' = definitions \<union> {the (newdefinition parameters)})"

definition CorrectTermDeclaration :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINE set)\<Rightarrow> (LINE set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
EXPRESSION \<Rightarrow> VARS \<Rightarrow> bool"
where 
"CorrectTermDeclaration zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' dvarExpression var ==
 (var \<notin> dvar)
\<and> (TermDeclaration' = TermDeclaration \<union> {(var, dvarExpression)}) 
\<and> (terms' = terms \<union> {(var)}) 
\<and> (dvar' = dvar \<union> {(var)})"

definition CorrectConstantTerm :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (LINE set)\<Rightarrow> (LINE set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
(VARS set \<rightharpoonup> VARS) \<Rightarrow> VARS \<Rightarrow> VARS set \<Rightarrow> bool"
where 
"CorrectConstantTerm zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' constant newTerm parameters ==
 (parameters \<subseteq> sets \<union> terms) 
\<and> (parameters \<noteq> {})
\<and> (newTerm = the (constant parameters))
\<and> (terms' = terms \<union> {(newTerm)})"

definition CorrectSetDeclaration :: 
"ZcgaState \<Rightarrow> ZcgaState \<Rightarrow> (VARS * EXPRESSION) set \<Rightarrow> (EXPRESSION set)\<Rightarrow> (DEFINITION set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
EXPRESSION \<Rightarrow> VARS \<Rightarrow> bool"
where 
"CorrectSetDeclaration zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' dvarExpression var ==
 (var \<notin> dvar)
\<and> (SetDeclaration' = SetDeclaration \<union> {(var, dvarExpression)}) 
\<and> (sets' = sets \<union> {(var)}) 
\<and> (dvar' = dvar \<union> {(var)})"

definition CorrectSchemaText :: 
"(VARS * EXPRESSION) set \<Rightarrow> (EXPRESSION set)\<Rightarrow> (DEFINITION set) => (VARS set) \<Rightarrow> (VARS * EXPRESSION) set
\<Rightarrow> (VARS * EXPRESSION) set\<Rightarrow> (VARS set)\<Rightarrow> (VARS set)\<Rightarrow> (VARS set) \<Rightarrow> 
(LINE set) \<Rightarrow> bool"
where 
"CorrectSchemaText declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' schemaText ==
(schemaText = {})
\<or> (schemaText = definitions \<union> expressions)"

lemma CorrectExpression_L1:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
 \<exists> expressions' :: (LINE set).
\<exists> definitions' :: (LINE set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> newExpression :: LINE.
\<exists> expressParameters :: (VARS set).
\<exists> expressConstant :: ((VARS set) \<rightharpoonup> LINE).
 (expressParameters \<subseteq> sets \<union> terms) 
\<and> (expressParameters \<noteq> {})
\<and> (newExpression = the (expressConstant expressParameters))
\<and> (expressions' = expressions \<union> {newExpression})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
by smt

lemma CorrectConstantSet_L2:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
 \<exists> expressions' :: (LINE set).
\<exists> definitions' :: (LINE set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> newset:: VARS.
\<exists> setParameters :: (VARS set).
\<exists> setConstant :: ((VARS set) \<rightharpoonup> VARS).
(setParameters \<subseteq> sets \<union> terms)
\<and> (setParameters \<noteq> {})
\<and> (newset = the (setConstant setParameters))
\<and> (sets' = sets \<union> {newset})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
by blast

lemma CorrectTermDeclaration_L3:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
\<exists> expressions' :: (LINE set).
\<exists> definitions' :: (LINE set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> dvarExpression :: EXPRESSION.
\<exists> var :: VARS.
 (var \<notin> dvar)
\<and> (TermDeclaration' = TermDeclaration \<union> {(var, dvarExpression)}) 
\<and> (terms' = terms \<union> {var}) 
\<and> (dvar' = dvar \<union> {var})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
by blast

lemma CorrectConstantTerm_L4:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
\<exists> expressions' :: (LINE set).
\<exists> definitions' :: (LINE set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> constant :: (VARS set \<rightharpoonup> VARS).
\<exists> newTerm :: VARS.
\<exists> parameters :: (VARS set).
 (parameters \<subseteq> sets \<union> terms) 
\<and> (parameters \<noteq> {})
\<and> (newTerm = the (constant parameters))
\<and> (terms' = terms \<union> {(newTerm)})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
by smt

lemma CorrectSetDeclaration_L5:
"(\<exists> zcgastate :: ZcgaState.
\<exists> zcgastate' :: ZcgaState.
\<exists> declarations':: (VARS * EXPRESSION) set.
\<exists> expressions' :: (LINE set).
\<exists> definitions' :: (LINE set).
\<exists> definedConstants' :: (VARS set).
\<exists> TermDeclaration' :: (VARS * EXPRESSION) set.
\<exists> SetDeclaration' :: (VARS * EXPRESSION) set.
\<exists> terms' :: (VARS set).
\<exists> sets' :: (VARS set).
\<exists> dvar' :: (VARS set).
\<exists> dvarExpression :: EXPRESSION.
\<exists> var :: VARS.
 (var \<notin> dvar)
\<and> (SetDeclaration' = SetDeclaration \<union> {(var, dvarExpression)}) 
\<and> (sets' = sets \<union> {var}) 
\<and> (dvar' = dvar \<union> {var})
\<longrightarrow> (TermDeclaration \<subseteq> declarations)
\<and> (SetDeclaration \<subseteq> declarations)
\<and> (dvars \<subset> sets \<union> terms)
\<and> (sets \<inter> terms = {}))"
by blast

lemma pre_CorrectExpression:
"(\<exists> zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' newExpression expressConstant.
 CorrectExpression zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' newExpression expressParameters expressConstant)
\<longrightarrow> (expressParameters \<subseteq> sets \<union> terms) 
\<and> (expressParameters \<noteq> {})"
using CorrectExpression_def by auto

lemma pre_CorrectConstantSet:
"(\<exists> zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' newset setConstant.
CorrectConstantSet zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' newset setParameters setConstant)
\<longrightarrow> (setParameters \<subseteq> sets \<union> terms)
\<and> (setParameters \<noteq> {})"
using CorrectConstantSet_def by auto

lemma pre_CorrectTermDeclaration:
"(\<exists> zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' dvarExpression.
CorrectTermDeclaration zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' dvarExpression var)
\<longrightarrow>  (var \<notin> dvar)"
using CorrectTermDeclaration_def by auto

lemma pre_CorrectConstantTerm:
"(\<exists> zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' constant newTerm.
CorrectConstantTerm zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' constant newTerm parameters)
\<longrightarrow>   (parameters \<subseteq> sets \<union> terms) 
\<and> (parameters \<noteq> {})"
by (simp add: CorrectConstantTerm_def)

lemma pre_CorrectSetDeclaration:
"(\<exists> zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' dvarExpression.
CorrectSetDeclaration zcgastate zcgastate' declarations' expressions' definitions' definedConstants' TermDeclaration' 
SetDeclaration' terms' sets' dvar' dvarExpression var)
\<longrightarrow> (var \<notin> dvar)"
by (simp add: CorrectSetDeclaration_def)


end
end