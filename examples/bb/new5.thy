\begin{verbatim}

theory new5
imports 
Main 

begin 
typedecl NAME 
typedecl DATE
datatype REPORT = ok | already_known | not_known


record BirthdayBook = 
BIRTHDAY :: "(NAME \<rightharpoonup> DATE)"
KNOWN :: "(NAME set)"


locale gpsabirthdaybook =
fixes birthday :: "(NAME \<rightharpoonup> DATE)"
and known :: "(NAME set)"
 
assumes
"(known = dom birthday)"
begin

definition InitBirthdayBook :: 
 "BirthdayBook \<Rightarrow> (NAME set) \<Rightarrow> (NAME \<rightharpoonup> DATE) \<Rightarrow> BirthdayBook => bool"
where 
"InitBirthdayBook birthdaybook' known' birthday' birthdaybook == (known' = {})"

definition FindBirthday :: 
 "(NAME set) \<Rightarrow> NAME \<Rightarrow> BirthdayBook \<Rightarrow> BirthdayBook \<Rightarrow> DATE \<Rightarrow> (NAME \<rightharpoonup> DATE) => bool"
where 
"FindBirthday known' name birthdaybook birthdaybook' date birthday' == (name \<in> known)
\<and> (date = the (birthday name))"

definition AddBirthday :: 
"(NAME set) \<Rightarrow> NAME \<Rightarrow> BirthdayBook \<Rightarrow> BirthdayBook \<Rightarrow> DATE \<Rightarrow> (NAME \<rightharpoonup> DATE) => bool"
where 
"AddBirthday known' name birthdaybook birthdaybook' date birthday' ==
 (name \<notin> known)
\<and> (birthday' = birthday (name \<mapsto> date ))"

definition NotKnown :: 
 "(NAME set) \<Rightarrow> NAME \<Rightarrow> BirthdayBook \<Rightarrow> BirthdayBook \<Rightarrow> (NAME \<rightharpoonup> DATE) \<Rightarrow> REPORT => bool"
where 
"NotKnown known' name birthdaybook birthdaybook' birthday' result == (name \<notin> known)
\<and> (result = not_known)"

definition AlreadyKnown :: 
 "(NAME set) \<Rightarrow> NAME \<Rightarrow> BirthdayBook \<Rightarrow> BirthdayBook \<Rightarrow> (NAME \<rightharpoonup> DATE) \<Rightarrow> REPORT => bool"
where 
"AlreadyKnown known' name birthdaybook birthdaybook' birthday' result == (name \<in> known)
\<and> (result = already_known)"

definition Success :: 
 "REPORT => bool"
where 
"Success result == (result = ok)"

definition RFindBirthday :: 
"(NAME set) \<Rightarrow> NAME \<Rightarrow> BirthdayBook \<Rightarrow> BirthdayBook \<Rightarrow> DATE \<Rightarrow> (NAME \<rightharpoonup> DATE) \<Rightarrow> REPORT => bool"
where 
"RFindBirthday known' name birthdaybook birthdaybook' date birthday' result == (((FindBirthday known' name birthdaybook birthdaybook' date birthday') \<and>
 (Success result)) \<or>
 (NotKnown known' name birthdaybook birthdaybook' birthday' result))"

definition RAddBirthday :: 
"(NAME set) \<Rightarrow> NAME \<Rightarrow> BirthdayBook \<Rightarrow> BirthdayBook \<Rightarrow> DATE \<Rightarrow> (NAME \<rightharpoonup> DATE) \<Rightarrow> REPORT => bool"
where 
"RAddBirthday known' name birthdaybook birthdaybook' date birthday' result == (((AddBirthday known' name birthdaybook birthdaybook' date birthday') \<and>
 (Success result)) \<or>
 (AlreadyKnown known' name birthdaybook birthdaybook' birthday' result))"

lemma AddBirthday_L1:
"(\<exists> known' :: (NAME set).
\<exists> name :: NAME.
\<exists> date :: DATE.
\<exists> birthday' :: (NAME \<rightharpoonup> DATE).
\<exists> birthday :: (NAME \<rightharpoonup> DATE).
\<exists> known :: (NAME set).
(name \<notin> known)
\<and> (birthday' = birthday (name \<mapsto> date ))
\<and> (known = dom birthday)
\<and>(known' = dom birthday'))"
sorry

end
end

\end{verbatim}