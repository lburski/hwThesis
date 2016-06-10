theory gpsa1n2
imports 
Main 

begin 
(*DATATYPES*)

record SS1 = 
(*DECLARATIONS*)

locale 1n2 = 
fixes (*GLOBAL DECLARATIONS*) 
begin

definition OS11 :: 
 "(*OS11_TYPES*) => bool"
where 
"OS11 (*OS11_VARIABLES*) == (O11)"

definition OS10 :: 
 "(*OS10_TYPES*) => bool"
where 
"OS10 (*OS10_VARIABLES*) == (PRE11)
\<and> (O10)"

definition OS9 :: 
 "(*OS9_TYPES*) => bool"
where 
"OS9 (*OS9_VARIABLES*) == (PRE10)
\<and> (O9)"

definition OS8 :: 
 "(*OS8_TYPES*) => bool"
where 
"OS8 (*OS8_VARIABLES*) == (PRE9)
\<and> (O8)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (O1)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (PRE5)
\<and> (O3)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (PRE7)
\<and> (O5)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (PRE6)
\<and> (O4)"

definition OS7 :: 
 "(*OS7_TYPES*) => bool"
where 
"OS7 (*OS7_VARIABLES*) == (O7)"

definition OS6 :: 
 "(*OS6_TYPES*) => bool"
where 
"OS6 (*OS6_VARIABLES*) == (PRE8)
\<and> (O6)"

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

definition CS5 :: 
"(*CS5_TYPES*) => bool"
where 
"CS5 (*CS5_VARIABLES*) ==
 (PRE4)
\<and> (PO6)"

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
