theory 4
imports 
Main 

begin 

record SS1 = 
(*DECLARATIONS*)

locale ZCGa = 
fixes (*GLOBAL DECLARATIONS*) 
assumes SI1
begin

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

definition CS5 :: 
 "(*CS5_TYPES*) => bool"
where 
"CS5 (*CS5_VARIABLES*) == (PRE5)
\<and> (PO6)"

definition CS4 :: 
 "(*CS4_TYPES*) => bool"
where 
"CS4 (*CS5_VARIABLES*) == (PRE4)
\<and> (PO5)"

definition CS6 :: 
 "(*CS6_TYPES*) => bool"
where 
"CS6 (*CS6_VARIABLES*) == (PRE6)
\<and> (PO7)"

definition CS1 :: 
 "(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) == (PRE1)
\<and> (PO2)"

definition CS6 :: 
 "(*CS6_TYPES*) => bool"
where 
"CS6 (*CS6_VARIABLES*) == (PRE6)
\<and> (PO7)"

definition CS2 :: 
 "(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) == (PRE2)
\<and> (PO3)"

definition OS1 :: 
 "(OS1_TYPES*) => bool"
where 
"OS1 (OS1_VARIABLES*) == (O1)"

end
end