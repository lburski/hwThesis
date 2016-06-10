theory gpsa1n2
imports 
Main 

begin 
typedecl PERSON
typedecl TITLE
datatype MESSAGE:: = success | notMember | 
notInStock | allCopiesOut | alreadyRented |
 nonPosStockLevel | tooManyRented | stillRented


record VideoShop = 
RENTED :: "PERSON rel TITLE"
STOCKLEVEL :: "(TITLE \<rightharpoonup> nat)"
MEMBERS :: "(PERSON set)"


locale 1n2 = 
fixes rented :: "PERSON rel TITLE"
and stockLevel :: "(TITLE \<rightharpoonup> nat)"
and members :: "(PERSON set)"
 
assumes
"(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)"
begin

definition TitlesOut0 :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"TitlesOut0 stockLevel' t videoshop' outcome members' videoshop rented' == (t \<in> Range rented)
\<and> (outcome = stillRented)"

definition TooManyRented :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> num \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"TooManyRented stockLevel' t videoshop' outcome members' change videoshop rented' == (the (stockLevel t))
\<and> (outcome = tooManyRented)"

definition NonPosStockLevel :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> num \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"NonPosStockLevel stockLevel' t videoshop' outcome members' change videoshop rented' == (the (stockLevel t))
\<and> (outcome = nonPosStockLevel)"

definition TitlesOut :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> VideoShop \<Rightarrow> PERSON \<Rightarrow> (TITLE set) \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"TitlesOut stockLevel' videoshop' p titles members' videoshop rented' == (p \<in> members)
\<and> (titles)"

definition CopiesInShop :: 
 "nat => bool"
where 
"CopiesInShop copiesIn == (t \<in> dom stockLevel)
\<and> (copiesIn)"

definition CopiesRentedOut :: 
 "nat \<Rightarrow> (TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"CopiesRentedOut copiesOut stockLevel' t videoshop' members' videoshop rented' == (t \<in> dom stockLevel)
\<and> (copiesOut)"

definition NotInStock :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"NotInStock stockLevel' t videoshop' outcome members' videoshop rented' == (t)
\<and> (outcome = notInStock)"

definition NotMember :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> PERSON \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"NotMember stockLevel' videoshop' outcome p members' videoshop rented' == (p \<notin> members)
\<and> (outcome = notMember)"

definition AlreadyRented :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> PERSON \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"AlreadyRented stockLevel' t videoshop' outcome p members' videoshop rented' == (p mapsto t)
\<and> (outcome)"

definition AllCopiesOut :: 
 "(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> MESSAGE \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"AllCopiesOut stockLevel' t videoshop' outcome members' videoshop rented' == (the (stockLevel t))
\<and> (outcome = allCopiesOut)"

definition IS1 :: 
 "PERSON rel TITLE \<Rightarrow> (TITLE \<rightharpoonup> nat) \<Rightarrow> VideoShop \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) => bool"
where 
"IS1 rented' stockLevel' videoshop videoshop' members' == (members' = {}) 
\<and> (stockLevel' = {})"

definition RentVideo :: 
"(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> PERSON \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"RentVideo stockLevel' t videoshop' p members' videoshop rented' ==
 (p \<in> members) 
\<and> (t \<in> dom stockLevel) 
\<and> (the (stockLevel t)) 
\<and> ((p, t) \<notin> rented)
\<and> (rented') 
\<and> (stockLevel' = stockLevel) 
\<and> (members' = members)"

definition DeleteTitle :: 
"(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"DeleteTitle stockLevel' t videoshop' members' videoshop rented' ==
 (t \<notin> Range rented) 
\<and> (t \<in> dom stockLevel)
\<and> (stockLevel') 
\<and> (members' = members) 
\<and> (rented' = rented)"

definition ChangeStockLevel :: 
"(TITLE \<rightharpoonup> nat) \<Rightarrow> TITLE \<Rightarrow> VideoShop \<Rightarrow> (PERSON set) \<Rightarrow> VideoShop \<Rightarrow> PERSON rel TITLE => bool"
where 
"ChangeStockLevel stockLevel' t videoshop' members' videoshop rented' ==
 (t) 
\<and> (the (stockLevel t)) 
\<and> (the (stockLevel t))
\<and> (stockLevel') 
\<and> (rented' = rented) 
\<and> (members' = members)"

lemma RentVideo_L1:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> p :: PERSON.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: PERSON rel TITLE.
(p \<in> members) 
\<and> (t \<in> dom stockLevel) 
\<and> (the (stockLevel t)) 
\<and> ((p, t) \<notin> rented)
\<and> (rented') 
\<and> (stockLevel' = stockLevel) 
\<and> (members' = members)
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented))
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)'))"
sorry

lemma DeleteTitle_L2:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: PERSON rel TITLE.
(t \<notin> Range rented) 
\<and> (t \<in> dom stockLevel)
\<and> (stockLevel') 
\<and> (members' = members) 
\<and> (rented' = rented)
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented))
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)'))"
sorry

lemma ChangeStockLevel_L3:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: PERSON rel TITLE.
(t) 
\<and> (the (stockLevel t)) 
\<and> (the (stockLevel t))
\<and> (stockLevel') 
\<and> (rented' = rented) 
\<and> (members' = members)
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented))
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)'))"
sorry

lemma RentVideo_L1:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> p :: PERSON.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: PERSON rel TITLE.
(p \<in> members) 
\<and> (t \<in> dom stockLevel) 
\<and> (the (stockLevel t)) 
\<and> ((p, t) \<notin> rented)
\<and> (rented') 
\<and> (stockLevel' = stockLevel) 
\<and> (members' = members)
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented))
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)'))"
sorry

lemma DeleteTitle_L2:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: PERSON rel TITLE.
(t \<notin> Range rented) 
\<and> (t \<in> dom stockLevel)
\<and> (stockLevel') 
\<and> (members' = members) 
\<and> (rented' = rented)
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented))
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)'))"
sorry

lemma ChangeStockLevel_L3:
"(\<exists> stockLevel' :: (TITLE \<rightharpoonup> nat).
\<exists> t :: TITLE.
\<exists> videoshop' :: VideoShop.
\<exists> members' :: (PERSON set).
\<exists> videoshop :: VideoShop.
\<exists> rented' :: PERSON rel TITLE.
(t) 
\<and> (the (stockLevel t)) 
\<and> (the (stockLevel t))
\<and> (stockLevel') 
\<and> (rented' = rented) 
\<and> (members' = members)
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented))
\<and> ((Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)\<and>(Domain rented \<subseteq> members) 
 and (Range rented \<subseteq> dom stockLevel) 
 and (\<forall>t. Range rented)'))"
sorry

end
end
