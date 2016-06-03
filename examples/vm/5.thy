\begin{verbatim}
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
" insufficient_cash  cash_tendered \<equiv>
if cash_tendered < price then True else False "

definition exact_cash :: 
 "nat  \<Rightarrow> bool"
where 
"exact_cash cash_tendered  \<equiv>
if cash_tendered = price then True else False"

definition some_stock :: 
 "nat => bool"
where 
" some_stock stock \<equiv> if stock > 0 then True else False " 

definition VM_operation :: 
"VMSTATE => VMSTATE => nat => nat => nat => bool"
where 
" VM_operation vmstate vmstate' cash_tendered cash_refunded bars_delivered == True"

definition VM_nosale :: 
 "nat => nat => nat => nat => nat => nat => nat => bool"
where 
" VM_nosale stock takings stock' takings'
cash_tendered cash_refunded bars_delivered \<equiv> if
((stock' = stock) 
\<and> (bars_delivered = 0) 
\<and> (cash_refunded = cash_tendered) 
\<and> (takings' = takings)) then True else False"

definition VM_sale :: " nat => nat => nat =>
nat => nat => nat => nat => bool"
where 
" VM_sale  stock takings stock' takings' cash_tendered
cash_refunded bars_delivered \<equiv> if
(stock' = stock - 1) 
& (bars_delivered = 1) 
& (cash_refunded = cash_tendered - price) 
& (takings' = takings + price) then True else False"

definition VM1 :: 
 "nat \<Rightarrow> nat  => nat => nat => nat => nat
 => nat => bool"
where 
" VM1  cash_tendered stock takings stock' takings'
cash_refunded bars_delivered \<equiv> if
(exact_cash cash_tendered = True)
 & (some_stock stock = True)
 & (VM_sale  stock takings stock' takings'
 cash_tendered cash_refunded bars_delivered = True)
 then True else False"

definition VM2 :: 
 "nat  => nat => nat => nat => nat => nat => nat => bool"
where 
" VM2  cash_tendered stock takings stock' takings' 
cash_refunded bars_delivered \<equiv> if
(insufficient_cash  cash_tendered= True)
 & (VM_nosale stock takings stock' takings'
 cash_tendered cash_refunded bars_delivered = True)
then True else False "

definition VM3 :: 
 "nat  => nat => nat => nat => nat => nat => nat => bool"
where 
" VM3  cash_tendered stock takings stock' takings' 
cash_refunded bars_delivered = (
(VM1  cash_tendered stock takings stock' takings' 
cash_refunded bars_delivered)
 | (VM2  cash_tendered stock takings stock' takings' 
 cash_refunded bars_delivered)
) "

 

end
end
\end{verbatim}