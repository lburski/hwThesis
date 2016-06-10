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

definition CS4 :: 
"(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) ==
 (PRE4)
\<and> (PO5)"

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

lemma CS4_L1:
"(\<exists> (*CS4_VARIABLESANDTYPES*).
(PRE4)
\<and> (PO5)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS1_L2:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS3_L3:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS2_L4:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS4_L1:
"(\<exists> (*CS4_VARIABLESANDTYPES*).
(PRE4)
\<and> (PO5)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS1_L2:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS3_L3:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS2_L4:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<and> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

end
end
