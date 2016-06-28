theory new5
imports 
Main 

begin 
typedecl PERSON
typedecl TITLE
datatype MESSAGE= success | notMember | 
notInStock | allCopiesOut | alreadyRented |
 nonPosStockLevel | tooManyRented | stillRented


record VideoShop = 
RENTED :: "(PERSON * TITLE) set"
STOCKLEVEL :: "(TITLE \<rightharpoonup> nat)"
MEMBERS :: "(PERSON set)"


locale thevideoshop = 
fixes rented :: "(PERSON * TITLE) set"
and stockLevel :: "(TITLE \<rightharpoonup> nat)"
and members :: "(PERSON set)"
 
assumes "Domain rented \<subseteq> members" 
 and "Range rented \<subseteq> dom stockLevel" 
 and "(\<forall>t \<in> Range rented. card ({p. (p, t) \<in> rented}) < (the (stockLevel t)))"
begin

definition InitVideoShop :: 
 "(PERSON * TITLE) set \<Rightarrow> (TITLE \<rightharpoonup> nat) \<Rightarrow> VideoShop \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) => bool"
where 
"InitVideoShop rented' stockLevel' videoshop videoshop' members' == (members' = {}) 
\<and> (stockLevel' = empty)"

definition TitlesOut0 :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"TitlesOut0 stockLevel' t videoshop' outcome members' videoshop rented' == (t \<in> Range rented)
\<and> (outcome = stillRented)"

definition TooManyRented :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> nat \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"TooManyRented stockLevel' t videoshop' outcome members' change videoshop rented' == 
((the (stockLevel t)) + change) < card ({p. (p, t) \<in> rented}) \<and>
(outcome = tooManyRented)"

definition NonPosStockLevel :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> nat \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"NonPosStockLevel stockLevel' t videoshop' outcome members' change videoshop rented' == (the (stockLevel t) + change \<le> 0)
\<and> (outcome = nonPosStockLevel)"

definition TitlesOut :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> VideoShop \<Rightarrow> PERSON \<Rightarrow> (TITLE set) \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"TitlesOut stockLevel' videoshop' p titles members' videoshop rented' ==(p \<in> members)
(*\<and> 
(titles = rented \<lparr> {(p)} \<rparr>)*)"

definition CopiesInShop :: 
 "nat \<Rightarrow> (TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => nat \<Rightarrow> bool"
where 
"CopiesInShop copiesOut stockLevel' t videoshop' members' videoshop rented' copiesIn== (t \<in> dom stockLevel)
\<and> (copiesIn = (the (stockLevel t)) - copiesOut)"

definition CopiesRentedOut :: 
 "nat \<Rightarrow> (TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"CopiesRentedOut copiesOut stockLevel' t videoshop' members' videoshop rented' == (t \<in> dom stockLevel)
\<and> (copiesOut = card ({p. (p, t) \<in> rented}))"

definition NotInStock :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"NotInStock stockLevel' t videoshop' outcome members' videoshop rented' == (t \<notin> dom stockLevel)
\<and> (outcome = notInStock)"

definition NotMember :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> PERSON \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"NotMember stockLevel' videoshop' outcome p members' videoshop rented' == (p \<notin> members)
\<and> (outcome = notMember)"

definition AlreadyRented :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> PERSON \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"AlreadyRented stockLevel' t videoshop' outcome p members' videoshop rented' == ((p,t) \<in> rented)
\<and> (outcome = alreadyRented)"

definition AllCopiesOut :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"AllCopiesOut stockLevel' t videoshop' outcome members' videoshop rented' == (the (stockLevel t) = card ({p. (p, t) \<in> rented}))
\<and> (outcome = allCopiesOut)"

definition RentVideo :: 
"(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> PERSON \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"RentVideo stockLevel' t videoshop' p members' videoshop rented' == (p \<in> members)
\<and> (t \<in> dom stockLevel)
\<and> (the (stockLevel t) > card ({p. (p, t) \<in> rented}))
\<and>((p,t) \<notin> rented)
\<and>(rented' = (rented \<union> {(p,t)}))
\<and>(stockLevel' = stockLevel)
\<and>(members' = members)"

definition DeleteTitle :: 
"(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => bool"
where 
"DeleteTitle stockLevel' t videoshop' members' videoshop rented' == (t \<notin> Range rented) 
\<and> (t \<in> dom stockLevel)
(*({p. (p, t) \<in> rented})*)
(*stockLevel' = {t} \<unlhd> stockLevel*)
\<and> (members' = members)
\<and> (rented' = rented)"

definition ChangeStockLevel :: 
"(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> (PERSON * TITLE) set => nat \<Rightarrow> bool"
where 
"ChangeStockLevel stockLevel' t videoshop' members' videoshop rented' change == (t \<in> dom stockLevel) 
\<and> (the (stockLevel t) + change > 0)
\<and> (the (stockLevel t) + change \<ge> card ({p. (p, t) \<in> rented}))
(*\<and> stockLevel' = stockLevl \<oplus> {(t, (the (stockLevel t) + change))}*)
\<and> (rented' = rented)
\<and>(members' = members)"

lemma RentVideo_L1:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> p :: PERSON.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: (PERSON * TITLE) set.
(p \<in> members)
\<and> (t \<in> dom stockLevel)
\<and> (the (stockLevel t) > card ({p. (p, t) \<in> rented}))
\<and>((p,t) \<notin> rented)
\<and>(rented' = (rented \<union> {(p,t)}))
\<and>(stockLevel' = stockLevel)
\<and>(members' = members))
\<longrightarrow> ((Domain rented \<subseteq> members)
 \<and> Range rented \<subseteq> dom stockLevel
(* \<and> (\<forall>t \<in> Range rented. card ({p. (p, t) \<in> rented}) < (the (stockLevel t)))*))"
sorry

lemma DeleteTitle_L2:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: (PERSON * TITLE) set.
(t \<notin> Range rented) 
\<and> (t \<in> dom stockLevel)
(*({p. (p, t) \<in> rented})*)
(*stockLevel' = {t} \<unlhd> stockLevel*)
\<and> (members' = members)
\<and> (rented' = rented))
\<longrightarrow> ((Domain rented \<subseteq> members)
 \<and> Range rented \<subseteq> dom stockLevel
(* \<and> (\<forall>t \<in> Range rented. card ({p. (p, t) \<in> rented}) < (the (stockLevel t)))*))"

sorry

lemma ChangeStockLevel_L3:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: (PERSON * TITLE) set.
(t \<in> dom stockLevel) 
\<and> (the (stockLevel t) + change > 0)
\<and> (the (stockLevel t) + change \<ge> card ({p. (p, t) \<in> rented}))
(*\<and> stockLevel' = stockLevl \<oplus> {(t, (the (stockLevel t) + change))}*)
\<and> (rented' = rented)
\<and>(members' = members)
\<longrightarrow> ((Domain rented \<subseteq> members)
 \<and> Range rented \<subseteq> dom stockLevel
 \<and> (\<forall>t \<in> Range rented. card ({p. (p, t) \<in> rented}) < (the (stockLevel t)))))"
sorry


end
end
