header "Control Flow Graph"

theory CPSScheme
  imports Main 
begin

types label = nat
types var = "label \<times> string"

definition "binder" :: "var \<Rightarrow> label" where  [simp]:"binder v = fst v"
 
datatype lambda = Lambda label "var list" call
     and call = App label val "val list"
              | Let label "(var \<times> lambda) list" call
     and val = L lambda | R label var | C label int | P prim
     and prim = Plus label | If label label

types prog = lambda

abbreviation "ex1 == Lambda 1 [(1,''cont'')] (App 2 (R 3 ((1,''cont''))) [C 4 0])"


end

