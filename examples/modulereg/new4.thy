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

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE2)
\<and> (PO2)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE1)
\<and> (PO1)"

lemma CS2_L1:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO2)
\<and> (SI1)
\<and> (SI1'))"
sorry

lemma CS1_L2:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO1)
\<and> (SI1)
\<and> (SI1'))"
sorry

end
end
