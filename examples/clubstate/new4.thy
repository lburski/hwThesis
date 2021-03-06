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

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (PRE5)
\<and> (O1)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (PRE7)
\<and> (O3)"

definition OS2 :: 
 "(*OS2_TYPES*) => bool"
where 
"OS2 (*OS2_VARIABLES*) == (PRE6)
\<and> (O2)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (PRE9)
\<and> (O5)"

definition OS6 :: 
 "(*OS6_TYPES*) => bool"
where 
"OS6 (*OS6_VARIABLES*) == (PO6)"

definition TS4 :: 
"(*TS4_TYPES*) => bool"
where 
"TS4 (*TS4_VARIABLES*) == (*TS4_EXPRESSION*)"

definition TS2 :: 
"(*TS2_TYPES*) => bool"
where 
"TS2 (*TS2_VARIABLES*) == (*TS2_EXPRESSION*)"

definition TS1 :: 
"(*TS1_TYPES*) => bool"
where 
"TS1 (*TS1_VARIABLES*) == (*TS1_EXPRESSION*)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (PRE8)
\<and> (O4)"

definition TS3 :: 
"(*TS3_TYPES*) => bool"
where 
"TS3 (*TS3_VARIABLES*) == (*TS3_EXPRESSION*)"

lemma CS4_L1:
"(\<exists> (*CS4_VARIABLESANDTYPES*).
(PRE4)
\<and> (PO5)
\<and> (SI1)
\<and> (SI1'))"
sorry

lemma CS1_L2:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<and> (SI1)
\<and> (SI1'))"
sorry

lemma CS3_L3:
"(\<exists> (*CS3_VARIABLESANDTYPES*).
(PRE3)
\<and> (PO4)
\<and> (SI1)
\<and> (SI1'))"
sorry

lemma CS2_L4:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<and> (SI1)
\<and> (SI1'))"
sorry

end
end
