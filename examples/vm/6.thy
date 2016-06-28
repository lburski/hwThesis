theory 6
imports 
Main 

begin 

record VMSTATE = 
STOCK :: nat
TAKINGS :: nat

locale zmathlang_vm =
fixes price :: nat
begin

definition insufficient_cash :: 
 "nat  => bool"
where 
" insufficient_cash  cash_tendered ==
 cash_tendered < price "

definition exact_cash :: 
 "nat  \<Rightarrow> bool"
where 
"exact_cash cash_tendered  ==
 cash_tendered = price"
 
 definition VM_operation :: 
"VMSTATE => VMSTATE => nat => nat => nat => bool"
where 
" VM_operation vmstate vmstate' cash_tendered cash_refunded bars_delivered == True"

definition some_stock :: 
 "nat => bool"
where 
" some_stock stock ==  stock > 0  " 

definition VM_nosale :: 
 "nat => nat => nat => nat => nat => nat => nat => bool"
where 
" VM_nosale stock takings stock' takings'
cash_tendered cash_refunded bars_delivered == ((stock' = stock) 
\<and> (bars_delivered = 0) 
\<and> (cash_refunded = cash_tendered) 
\<and> (takings' = takings))"

definition VM2 :: 
 "nat  => nat => nat => nat => nat => nat => nat => bool"
where 
" VM2  cash_tendered stock takings stock' takings' cash_refunded bars_delivered ==
(insufficient_cash  cash_tendered)
 \<and> (VM_nosale stock takings stock' takings' cash_tendered cash_refunded bars_delivered)"

definition VM_sale :: " nat => nat => nat \<Rightarrow>nat => nat => nat => nat => bool"
where 
" VM_sale  stock takings stock' takings' cash_tendered cash_refunded bars_delivered ==
(stock' = stock - 1) 
\<and> (bars_delivered = 1) 
\<and> (cash_refunded = cash_tendered - price) 
\<and> (takings' = takings + price) "

definition VM1 :: 
 "nat \<Rightarrow> nat  => nat => nat => nat => nat  => nat => bool"
where 
" VM1  cash_tendered stock takings stock' takings' cash_refunded bars_delivered ==
(exact_cash cash_tendered )
\<and> (some_stock stock)
\<and> (VM_sale  stock takings stock' takings'
 cash_tendered cash_refunded bars_delivered)"

definition VM3 :: 
 "nat  => nat => nat => nat => nat => nat => nat => bool"
where 
" VM3  cash_tendered stock takings stock' takings' cash_refunded bars_delivered =
((VM1  cash_tendered stock takings stock' takings' 
cash_refunded bars_delivered)
 \<or> (VM2  cash_tendered stock takings stock' takings' cash_refunded bars_delivered)) "

lemma pre_VM1: 
"(\<exists> stock' takings' cash_refunded bars_delivered.
 VM1 cash_tendered stock takings stock' takings' 
 cash_refunded bars_delivered)
 \<longleftrightarrow> (0 < stock) \<and> 
 (cash_tendered = price) \<and> (0 \<le> takings)"
 apply (unfold VM1_def exact_cash_def 
 some_stock_def VM_sale_def)
 apply auto
 done
  
  lemma pre_VM2: 
"(\<exists> stock' takings' cash_refunded bars_delivered.
 VM2 cash_tendered stock takings stock' takings' cash_refunded bars_delivered)
 \<longleftrightarrow> (cash_tendered < price) \<and>
(cash_tendered \<ge> 0) \<and> (stock \<ge> 0) \<and> (takings \<ge> 0)"
apply (unfold VM2_def insufficient_cash_def VM_nosale_def )
apply auto
done

  lemma pre_VM3: 
"(\<exists> stock' takings' cash_refunded bars_delivered.
 VM3 cash_tendered stock takings stock' 
 takings' cash_refunded bars_delivered)
 \<longleftrightarrow> (0 < stock \<and> 
 cash_tendered = price \<and> 0 \<le> takings) \<or> (cash_tendered < price)
\<and> (0 \<le> cash_tendered)
\<and> (0 \<le> stock)
\<and> (0 \<le> takings)"
apply (unfold VM3_def VM2_def VM1_def 
some_stock_def exact_cash_def VM_sale_def
  VM_nosale_def insufficient_cash_def)
apply auto
done

lemma cash_lemma: "\<not> (insufficient_cash 
cash_tendered \<and> exact_cash cash_tendered)"
apply (unfold insufficient_cash_def exact_cash_def)
apply auto
done


lemma VM3_refines_VM1:
"(\<exists> stock' takings' cash_refunded bars_delivered.
((VM1 cash_tendered stock takings stock' takings' cash_refunded
bars_delivered)
\<longrightarrow>
(VM3 cash_tendered stock takings stock' takings' cash_refunded
bars_delivered))
\<and>
(((VM1 cash_tendered stock takings stock' takings' cash_refunded
bars_delivered)
\<and>
(VM3 cash_tendered stock takings stock' takings' cash_refunded
bars_delivered))
\<longrightarrow>
(VM1 cash_tendered stock takings stock' takings' cash_refunded
bars_delivered)))"
apply (unfold VM3_def VM1_def VM_sale_def
 exact_cash_def some_stock_def)
apply auto
done

lemma VM3_ok:
"(\<exists> stock' takings cash_refunded bars_delivered.
(VM3 cash_tendered stock takings stock' takings' cash_refunded
bars_delivered)
\<longrightarrow>
((takings' - takings) \<ge> price * (stock - stock' )))"
apply (unfold VM3_def VM1_def VM2_def exact_cash_def some_stock_def
  VM_sale_def VM_nosale_def insufficient_cash_def)
apply auto
done

end
end