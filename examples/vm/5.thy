theory 5
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
" VM_operation vmstate vmstate' cash_tendered 
cash_refunded bars_delivered == True"

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
" VM2  cash_tendered stock takings stock' takings' 
cash_refunded bars_delivered ==
(insufficient_cash  cash_tendered)
 \<and> (VM_nosale stock takings stock' takings' cash_tendered
 cash_refunded bars_delivered)"

definition VM_sale :: " nat => nat => nat \<Rightarrow>nat => nat =>
nat => nat => bool"
where 
" VM_sale  stock takings stock' takings' cash_tendered
cash_refunded bars_delivered ==
(stock' = stock - 1) 
\<and> (bars_delivered = 1) 
\<and> (cash_refunded = cash_tendered - price) 
\<and> (takings' = takings + price) "

definition VM1 :: 
 "nat \<Rightarrow> nat  => nat => nat => nat => nat  => nat => bool"
where 
" VM1  cash_tendered stock takings stock' takings'
cash_refunded bars_delivered ==
(exact_cash cash_tendered )
\<and> (some_stock stock)
\<and> (VM_sale  stock takings stock' takings'
 cash_tendered cash_refunded bars_delivered)"

definition VM3 :: 
 "nat  => nat => nat => nat => nat => nat => nat => bool"
where 
" VM3  cash_tendered stock takings stock' takings'
cash_refunded bars_delivered =
((VM1  cash_tendered stock takings stock' takings' 
cash_refunded bars_delivered)
 \<or> (VM2  cash_tendered stock takings stock' takings'
 cash_refunded bars_delivered)) "
 
 end
 end