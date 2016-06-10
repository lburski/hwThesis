theory gpsazmathlang_stInvIncorrect
imports 
Main 

begin 
typedecl NAME 
typedecl SURNAME
typedecl TELEPHONE
datatype OUTPUT = success | alreadyInDirectory | nameNotInDirectory | numberInUse | numberDoesntExist


record SS1 = 
PHONENUMBERS :: (NAME \<rightharpoonup> TELEPHONE) set
PERSONS :: (NAME * SURNAME) set


locale zmathlang_stInvIncorrect = 
fixes phoneNumbers :: "(NAME \<rightharpoonup> TELEPHONE) set"
and persons :: "(NAME * SURNAME) set"
 
assumes SI1
begin

definition OS1 :: 
 "OUTPUT \<Rightarrow> NAME \<Rightarrow> SURNAME => bool"
where 
"OS1 message n s == (message = success)"

definition IS1 :: 
 "(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) set => bool"
where 
"IS1 persons' phoneNumbers' == (phoneNumbers' = {}) 
\<and> (persons' = {})"

definition OS3 :: 
 "(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) set \<Rightarrow> OUTPUT \<Rightarrow> NAME \<Rightarrow> SURNAME => bool"
where 
"OS3 persons' phoneNumbers' message n s == (n, s \<notin> persons)
\<and> (message = nameNotInDirectory)"

definition OS2 :: 
 "(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) set \<Rightarrow> OUTPUT \<Rightarrow> NAME \<Rightarrow> SURNAME => bool"
where 
"OS2 persons' phoneNumbers' message n s == (n, s \<in> persons)
\<and> (message = alreadyInDirectory)"

definition OS5 :: 
 "OUTPUT \<Rightarrow> TELEPHONE => bool"
where 
"OS5 message p == (p \<notin> Range phoneNumbers)
\<and> (message = numberDoesntExist)"

definition OS4 :: 
 "OUTPUT \<Rightarrow> TELEPHONE => bool"
where 
"OS4 message p == (p \<in> Range phoneNumbers)
\<and> (\<exists>n. Domain persons)"

definition CS1 :: 
"NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => bool"
where 
"CS1 name surname phone ==
 (name, surname \<notin> persons)
\<and> (phoneNumbers' = phoneNumbers \<union> {(name, surname )})"

lemma TS1: 
"(*TS1_EXPRESSION*)"
sorry

definition CS4 :: 
"(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) set \<Rightarrow> NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => bool"
where 
"CS4 persons' phoneNumbers' n s p ==
 (p \<in> Range phoneNumbers)
\<and> (\<exists>n. Domain persons)"

definition CS3 :: 
"(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) set \<Rightarrow> NAME \<Rightarrow> SURNAME \<Rightarrow> TELEPHONE => bool"
where 
"CS3 persons' phoneNumbers' n s p ==
 (n, s \<in> persons)
\<and> (phoneNumbers' = phoneNumbers - {(n, s)}) 
\<and> (persons' = persons - {(n, s)})"

definition CS2 :: 
"(NAME * SURNAME) set \<Rightarrow> (NAME \<rightharpoonup> TELEPHONE) set \<Rightarrow> NAME \<Rightarrow> TELEPHONE => bool"
where 
"CS2 persons' phoneNumbers' m p ==
 (m \<notin> Domain persons) 
\<and> (p \<notin> Range phoneNumbers)
\<and> (phoneNumbers' = phoneNumbers \<union> {(m, p)})"

lemma TS4: 
"(*TS4_EXPRESSION*)"
sorry

lemma TS2: 
"(*TS2_EXPRESSION*)"
sorry

lemma TS3: 
"(*TS3_EXPRESSION*)"
sorry

lemma TS5: 
"(*TS5_EXPRESSION*)"
sorry

lemma OS1_L6:
"(\<exists> (*OS1_VARIABLE*) :: (*OS1_TYPE*).
(message = success)
\<and> (SI1\<and>SI1))"

lemma OS3_L7:
"(\<exists> (*OS3_VARIABLE*) :: (*OS3_TYPE*).
(n, s \<notin> persons)
\<and> (message = nameNotInDirectory)
\<and> (SI1\<and>SI1))"

lemma OS2_L8:
"(\<exists> (*OS2_VARIABLE*) :: (*OS2_TYPE*).
(n, s \<in> persons)
\<and> (message = alreadyInDirectory)
\<and> (SI1\<and>SI1))"

lemma OS5_L9:
"(\<exists> (*OS5_VARIABLE*) :: (*OS5_TYPE*).
(p \<notin> Range phoneNumbers)
\<and> (message = numberDoesntExist)
\<and> (SI1\<and>SI1))"

lemma OS4_L10:
"(\<exists> (*OS4_VARIABLE*) :: (*OS4_TYPE*).
(p \<in> Range phoneNumbers)
\<and> (\<exists>n. Domain persons)
\<and> (SI1\<and>SI1))"

lemma CS1_L11:
"(\<exists> (*CS1_VARIABLE*) :: (*CS1_TYPE*).
(name, surname \<notin> persons)
\<and> (phoneNumbers' = phoneNumbers \<union> {(name, surname )})
\<and> (SI1\<and>SI1))"

lemma CS4_L12:
"(\<exists> (*CS4_VARIABLE*) :: (*CS4_TYPE*).
(p \<in> Range phoneNumbers)
\<and> (\<exists>n. Domain persons)
\<and> (SI1\<and>SI1))"

lemma CS3_L13:
"(\<exists> (*CS3_VARIABLE*) :: (*CS3_TYPE*).
(n, s \<in> persons)
\<and> (phoneNumbers' = phoneNumbers - {(n, s)}) 
\<and> (persons' = persons - {(n, s)})
\<and> (SI1\<and>SI1))"

lemma CS2_L14:
"(\<exists> (*CS2_VARIABLE*) :: (*CS2_TYPE*).
(m \<notin> Domain persons) 
\<and> (p \<notin> Range phoneNumbers)
\<and> (phoneNumbers' = phoneNumbers \<union> {(m, p)})
\<and> (SI1\<and>SI1))"

lemma OS1_L6:
"(\<exists> (*OS1_VARIABLE*) :: (*OS1_TYPE*).
(message = success)
\<and> (SI1\<and>SI1))"

lemma OS3_L7:
"(\<exists> (*OS3_VARIABLE*) :: (*OS3_TYPE*).
(n, s \<notin> persons)
\<and> (message = nameNotInDirectory)
\<and> (SI1\<and>SI1))"

lemma OS2_L8:
"(\<exists> (*OS2_VARIABLE*) :: (*OS2_TYPE*).
(n, s \<in> persons)
\<and> (message = alreadyInDirectory)
\<and> (SI1\<and>SI1))"

lemma OS5_L9:
"(\<exists> (*OS5_VARIABLE*) :: (*OS5_TYPE*).
(p \<notin> Range phoneNumbers)
\<and> (message = numberDoesntExist)
\<and> (SI1\<and>SI1))"

lemma OS4_L10:
"(\<exists> (*OS4_VARIABLE*) :: (*OS4_TYPE*).
(p \<in> Range phoneNumbers)
\<and> (\<exists>n. Domain persons)
\<and> (SI1\<and>SI1))"

lemma CS1_L11:
"(\<exists> (*CS1_VARIABLE*) :: (*CS1_TYPE*).
(name, surname \<notin> persons)
\<and> (phoneNumbers' = phoneNumbers \<union> {(name, surname )})
\<and> (SI1\<and>SI1))"

lemma CS4_L12:
"(\<exists> (*CS4_VARIABLE*) :: (*CS4_TYPE*).
(p \<in> Range phoneNumbers)
\<and> (\<exists>n. Domain persons)
\<and> (SI1\<and>SI1))"

lemma CS3_L13:
"(\<exists> (*CS3_VARIABLE*) :: (*CS3_TYPE*).
(n, s \<in> persons)
\<and> (phoneNumbers' = phoneNumbers - {(n, s)}) 
\<and> (persons' = persons - {(n, s)})
\<and> (SI1\<and>SI1))"

lemma CS2_L14:
"(\<exists> (*CS2_VARIABLE*) :: (*CS2_TYPE*).
(m \<notin> Domain persons) 
\<and> (p \<notin> Range phoneNumbers)
\<and> (phoneNumbers' = phoneNumbers \<union> {(m, p)})
\<and> (SI1\<and>SI1))"

end
end
