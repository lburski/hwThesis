theory gpsa1n2
imports 
Main 

begin 
datatype events = press_att_cws | press_cas_eng | press_alt_eng | 
 press_fpa_sel
datatype mode_status = off | engaged


record AutoPilot = 
ALT_ENG :: "mode_status"
CAS_ENG :: "mode_status"
ATT_CWS :: "mode_status"
FPA_SEL :: "mode_status"


locale 1n2 = 
fixes alt_eng :: "mode_status"
and cas_eng :: "mode_status"
and att_cws :: "mode_status"
and fpa_sel :: "mode_status"
 
begin

definition off\_eng :: 
 "mode_status => bool"
where 
"off\_eng mode == (O1)"

definition CS1 :: 
"(*CS1_TYPES*) => bool"
where 
"CS1 (*CS1_VARIABLES*) ==
 (att_cws = off)
\<and> (att_cws' = engaged) 
\<and> (fpa_sel' = off) 
\<and> (alt_eng' = off) 
\<and> (cas_eng' = off \<or>
 cas_eng' = engaged)"

end
end
