theory new5
imports 
Main 

begin 
typedecl PERSON
datatype GENDER = male | female

record GenDB = 
PARENT :: "(PERSON * PERSON) set"
SEX :: "PERSON \<rightharpoonup> GENDER"

locale Gendb = 
fixes parent :: "(PERSON * PERSON) set"
and sex :: "(PERSON \<rightharpoonup> GENDER)"
assumes "Domain parent \<union> Range parent \<subseteq> dom sex" 
 and "(\<forall>p :: PERSON. (p, p) \<notin> parent^*)" 
 and "(\<forall>p :: PERSON. \<forall> q :: PERSON. \<forall> r :: PERSON. ({(p,q),(p,r)} \<subseteq> parent)
\<and> q \<noteq> r \<longrightarrow> the (sex q) \<noteq> the (sex r))"
begin

definition InitGenDB :: 
 "(PERSON * PERSON) set => (PERSON * GENDER) set => bool"
where 
"InitGenDB parent' sex' == (sex' = {}) 
\<and> (parent' = {})"

definition CommonAncestors ::
"GenDB \<Rightarrow> GenDB \<Rightarrow> PERSON \<Rightarrow> PERSON \<Rightarrow> PERSON set \<Rightarrow> bool"
where
"CommonAncestors gendb  gendb' p q cas == 
({p,q} \<union> cas \<subseteq> dom sex)
(*\<and> cas = {ca. (\<exists>m n::nat. ((p,ca) \<in> parent^(0) \<and> (q,ca) \<in> parent^0)
\<and> (\<exists>r x y. (x+y < m + n)
\<and> ((p,r) \<in> parent^x)
\<and> ((q,r) \<in> parent^y))}*)"

definition Cousins :: 
 "GenDB => GenDB => PERSON => nat => nat => PERSON set => bool"
where 
"Cousins gendb gendb' p n rem cousins == ({p} \<union> cousins \<subseteq> dom sex )
(*\<and> (let cosrel = (parent^(n + 1) semi (parent^-1)^(n+1+rem)) - (parent semi parent^1)
 in (cousins = cosrel \<lparr>{p}\<rparr> \<union> cosrel^-1 \<lparr>{p}\<rparr>))*)"

definition ChangeName :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON \<rightharpoonup> GENDER) => PERSON => PERSON => bool"
where 
"ChangeName gendb gendb' parent' sex' old new == (old \<in> dom sex) 
\<and> (new \<notin> dom sex)
\<and> (sex' = (**) sex(new \<mapsto> the (sex old)))
(*\<and> parent' =\<and> (parent' = {\<exists> q. \<exists> t.  ({(q,t)})})
\<and> ( ({p. (old, p) \<notin> parent})= parent' )
\<union> {x.PERSON \<longrightarrow> x \<in> parent\<lparr>{old}\<rparr>}
\<union> {x.PERSON \<longrightarrow> x \<notin> parent^-1 \<lparr>{old}\<rparr>}*)"

definition ChangeSex :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON \<rightharpoonup> GENDER) => PERSON => bool"
where 
"ChangeSex gendb gendb' parent' sex' p ==
(p \<in> dom sex)
(*\<and> sex' = sex \<oplus>
({q s. (q \<in> PERSON) \<and> s \<in> GENDER \<longleftrightarrow>}
((q \<in> (parent^-1 semi parent)^* \<lparr>{p?}\<rparr>)
\<and> (s \<noteq> the sex q)})) *)
\<and> (parent' = parent)"

definition AddPerson :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON \<rightharpoonup> GENDER) => PERSON => GENDER => bool"
where 
"AddPerson gendb gendb' parent' sex' name morf == ((
(name \<notin> dom sex)
\<and> (sex' = sex (name \<mapsto> morf))
\<and> (parent' = parent)
))"

definition AddRel :: 
"GenDB => GenDB => (PERSON * PERSON) set => (PERSON \<rightharpoonup> GENDER) => PERSON => PERSON  => bool"
where 
"AddRel gendb gendb' parent' sex' off par ==
 ((
({off,par} \<subseteq> dom sex)
\<and> ((off, par) \<notin> parent) 
\<and> ((par,off) \<notin> parent)
\<and> (card  ({p. (off, p) \<in> parent}) \<le> 1)
\<and> (\<forall>x :: PERSON .  ((off,x) \<in> parent) \<longrightarrow> (the (sex x) \<noteq> the (sex par)))
\<and> (parent' = parent \<union> {(off, par)})
\<and> (sex' = sex)))"

lemma ChangeName_L1:
"(\<exists> gendb :: GenDB.
\<exists> gendb' :: GenDB.
\<exists> parent' :: (PERSON * PERSON) set.
\<exists> sex' :: (PERSON \<rightharpoonup> GENDER).
\<exists> old :: PERSON.
\<exists> new :: PERSON.
(old \<in> dom sex)
\<and> (new \<notin> dom sex)
\<and> (sex' = (**) sex(new \<mapsto> the (sex old)))
(*\<and> parent' =\<and> (parent' = {\<exists> q. \<exists> t.  ({(q,t)})})
\<and> ( ({p. (old, p) \<notin> parent})= parent' )
\<union> {x.PERSON \<longrightarrow> x \<in> parent\<lparr>{old}\<rparr>}
\<union> {x.PERSON \<longrightarrow> x \<notin> parent^-1 \<lparr>{old}\<rparr>}*)
\<longrightarrow> (Domain parent \<union> Range parent \<subseteq> dom sex
\<and> (\<forall>p :: PERSON. (p, p) \<notin> parent^*)
\<and> (\<forall>p :: PERSON. \<forall> q :: PERSON. \<forall> r :: PERSON. ({(p,q),(p,r)} \<subseteq> parent)
\<and> q \<noteq> r \<longrightarrow> the (sex q) \<noteq> the (sex r)))
\<and> (Domain parent' \<union> Range parent' \<subseteq> dom sex'
\<and> (\<forall>p :: PERSON. (p, p) \<notin> parent'^*)
\<and> (\<forall>p :: PERSON. \<forall> q :: PERSON. \<forall> r :: PERSON. ({(p,q),(p,r)} \<subseteq> parent')
\<and> q \<noteq> r \<longrightarrow> the (sex' q) \<noteq> the (sex' r))))"
sorry

lemma ChangeSex_L2:
"(\<exists> gendb :: GenDB.
\<exists> gendb' :: GenDB.
\<exists> parent' :: (PERSON * PERSON) set.
\<exists> sex' :: (PERSON \<rightharpoonup> GENDER).
\<exists> p :: PERSON.
(p \<in> dom sex)
(*\<and> sex' = sex \<oplus>
({q s. (q \<in> PERSON) \<and> s \<in> GENDER \<longleftrightarrow>}
((q \<in> (parent^-1 semi parent)^* \<lparr>{p?}\<rparr>)
\<and> (s \<noteq> the sex q)})) *)
\<and> (parent' = parent)
\<longrightarrow> (Domain parent \<union> Range parent \<subseteq> dom sex
\<and> (\<forall>p :: PERSON. (p, p) \<notin> parent^*)
\<and> (\<forall>p :: PERSON. \<forall> q :: PERSON. \<forall> r :: PERSON. ({(p,q),(p,r)} \<subseteq> parent)
\<and> q \<noteq> r \<longrightarrow> the (sex q) \<noteq> the (sex r)))
\<and> (Domain parent' \<union> Range parent' \<subseteq> dom sex'
\<and> (\<forall>p :: PERSON. (p, p) \<notin> parent'^*)
\<and> (\<forall>p :: PERSON. \<forall> q :: PERSON. \<forall> r :: PERSON. ({(p,q),(p,r)} \<subseteq> parent')
\<and> q \<noteq> r \<longrightarrow> the (sex' q) \<noteq> the (sex' r))))"
sorry

lemma CS1_L3:
"(\<exists> (*CS1_VARIABLESANDTYPES*).
(PRE1)
\<and> (PO2)
\<longrightarrow> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

lemma CS2_L4:
"(\<exists> (*CS2_VARIABLESANDTYPES*).
(PRE2)
\<and> (PO3)
\<longrightarrow> (SI1\<and>SI1)
\<and> (SI1\<and>SI1'))"
sorry

end
end
