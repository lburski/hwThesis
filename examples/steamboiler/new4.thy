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

definition IS1 :: 
 "(*IS1_TYPES*) => bool"
where 
"IS1 (*IS1_VARIABLES*) == (PO1)"

definition IS6 :: 
 "(*IS6_TYPES*) => bool"
where 
"IS6 (*IS6_VARIABLES*) == (PO10)"

definition PRE4 :: 
 "(*PRE4_TYPES*) => bool"
where 
"PRE4 (*PRE4_VARIABLES*) == (*PRECONDITION*) "

definition CS8 :: 
"(*CS8_TYPES*) => bool"
where 
"CS8 (*CS8_VARIABLES*) ==
 (PRE17)
\<and> (PO19)"

definition CS5 :: 
"(*CS5_TYPES*) => bool"
where 
"CS5 (*CS5_VARIABLES*) ==
 (PRE14)
\<and> (PO16)"

definition CS7 :: 
"(*CS7_TYPES*) => bool"
where 
"CS7 (*CS7_VARIABLES*) ==
 (PRE16)
\<and> (PO18)"

definition CS3 :: 
"(*CS3_TYPES*) => bool"
where 
"CS3 (*CS3_VARIABLES*) ==
 (PRE8)
\<and> (PO9)"

definition CS12 :: 
"(*CS12_TYPES*) => bool"
where 
"CS12 (*CS12_VARIABLES*) ==
 (PRE21)
\<and> (PO23)"

definition OS1 :: 
 "(*OS1_TYPES*) => bool"
where 
"OS1 (*OS1_VARIABLES*) == (O1)"

definition OS3 :: 
 "(*OS3_TYPES*) => bool"
where 
"OS3 (*OS3_VARIABLES*) == (PRE6)"

definition OS2 :: 
 "(*OS2_TYPES*) => bool"
where 
"OS2 (*OS2_VARIABLES*) == (O2)"

definition OS5 :: 
 "(*OS5_TYPES*) => bool"
where 
"OS5 (*OS5_VARIABLES*) == (O2)"

definition OS4 :: 
 "(*OS4_TYPES*) => bool"
where 
"OS4 (*OS4_VARIABLES*) == (O1)"

definition OS6 :: 
 "(*OS6_TYPES*) => bool"
where 
"OS6 (*OS6_VARIABLES*) == (O3)"

definition IS9 :: 
"(*IS9_TYPES*) => bool"
where 
"IS9 (*IS9_VARIABLES*) ==
 (PRE11)
\<and> (PO13)"

definition IS8 :: 
"(*IS8_TYPES*) => bool"
where 
"IS8 (*IS8_VARIABLES*) ==
 (PRE10)
\<and> (PO12)"

definition IS3 :: 
"(*IS3_TYPES*) => bool"
where 
"IS3 (*IS3_VARIABLES*) ==
 (PRE2)
\<and> (PO3)"

definition IS2 :: 
"(*IS2_TYPES*) => bool"
where 
"IS2 (*IS2_VARIABLES*) ==
 (PRE1)
\<and> (PO2)"

definition IS7 :: 
"(*IS7_TYPES*) => bool"
where 
"IS7 (*IS7_VARIABLES*) ==
 (PRE9)
\<and> (PO11)"

definition IS5 :: 
"(*IS5_TYPES*) => bool"
where 
"IS5 (*IS5_VARIABLES*) == True"

definition IS4 :: 
"(*IS4_TYPES*) => bool"
where 
"IS4 (*IS4_VARIABLES*) ==
 (PRE3)
\<and> (PO4)"

definition CS10 :: 
"(*CS10_TYPES*) => bool"
where 
"CS10 (*CS10_VARIABLES*) ==
 (PRE19)
\<and> (PO21)"

definition PO5 :: 
"(*PO5_TYPES*) => bool"
where 
"PO5 (*PO5_VARIABLES*) == (*POSTCONDITION*) "

definition CS9 :: 
"(*CS9_TYPES*) => bool"
where 
"CS9 (*CS9_VARIABLES*) ==
 (PRE18)
\<and> (PO20)"

definition CS4 :: 
"(*CS4_TYPES*) => bool"
where 
"CS4 (*CS4_VARIABLES*) ==
 (PRE13)
\<and> (PO15)"

definition CS6 :: 
"(*CS6_TYPES*) => bool"
where 
"CS6 (*CS6_VARIABLES*) ==
 (PRE15)
\<and> (PO17)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (PRE5)
\<and> (PO6)"

definition CS2 :: 
"(*CS2_TYPES*) => bool"
where 
"CS2 (*CS2_VARIABLES*) ==
 (PRE7)
\<and> (PO8)"

definition CS11 :: 
"(*CS11_TYPES*) => bool"
where 
"CS11 (*CS11_VARIABLES*) ==
 (PRE20)
\<and> (PO22)"

definition CS13 :: 
"(*CS13_TYPES*) => bool"
where 
"CS13 (*CS13_VARIABLES*) ==
 (PRE22)
\<and> (PO24)"

definition IS10 :: 
"(*IS10_TYPES*) => bool"
where 
"IS10 (*IS10_VARIABLES*) ==
 (PRE12)
\<and> (PO14)"

definition TS5 :: 
"(*TS5_TYPES*) => bool"
where 
"TS5 (*TS5_VARIABLES*) == (*TS5_EXPRESSION*)"

definition TS4 :: 
"(*TS4_TYPES*) => bool"
where 
"TS4 (*TS4_VARIABLES*) == (*TS4_EXPRESSION*)"

definition TS1 :: 
"(*TS1_TYPES*) => bool"
where 
"TS1 (*TS1_VARIABLES*) == (*TS1_EXPRESSION*)"

definition TS2 :: 
"(*TS2_TYPES*) => bool"
where 
"TS2 (*TS2_VARIABLES*) == (*TS2_EXPRESSION*)"

definition TS3 :: 
"(*TS3_TYPES*) => bool"
where 
"TS3 (*TS3_VARIABLES*) == (*TS3_EXPRESSION*)"

definition TS6 :: 
"(*TS6_TYPES*) => bool"
where 
"TS6 (*TS6_VARIABLES*) == (*TS6_EXPRESSION*)"

end
end
