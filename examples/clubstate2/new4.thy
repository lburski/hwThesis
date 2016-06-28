theory gpsa1n2
imports 
Main 

begin 
(*DATATYPES*)

record SS1 = 
(*DECLARATIONS*)

locale 1n2 = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

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

lemma CS1_L1:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<longrightarrow> ((SI1)
\<and> (SI2))"
sorry

lemma CS3_L2:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<longrightarrow> ((SI1)
\<and> (SI2))"
sorry

lemma CS2_L3:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<longrightarrow> ((SI1)
\<and> (SI2))"
sorry

lemma CS1_L1:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<longrightarrow> ((SI1)
\<and> (SI2))"
sorry

lemma CS3_L2:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<longrightarrow> ((SI1)
\<and> (SI2))"
sorry

lemma CS2_L3:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<longrightarrow> ((SI1)
\<and> (SI2))"
sorry

end
end
