header "Control Flow Graph"

theory CPSScheme
  imports Main 
begin

types label = nat
types var = "label \<times> string"

definition "binder" :: "var \<Rightarrow> label" where  [simp]:"binder v = fst v"

datatype prim = Plus label | If label label
datatype lambda = Lambda label "var list" call
     and call = App label val "val list"
              | Let label "(var \<times> lambda) list" call
     and val = L lambda | R label var | C label int | P prim

types prog = lambda

abbreviation "ex1 == (Lambda 1 [(1,''cont'')] (App 2 (R 3 (1,''cont'')) [(C 4 0)]))"
abbreviation "ex2 == (Lambda 1 [(1,''cont'')] (App 2 (P (Plus 3)) [(C 4 1), (C 5 1), (R 6 (1,''cont''))]))"
abbreviation "ex3 == (Lambda 1 [(1,''cont'')] (Let 2 [((2,''rec''),(Lambda 3 [(3,''p''), (3,''i''), (3,''c_'')] (App 4 (P (If 5 6)) [(R 7 (3,''i'')), (L (Lambda 8 [] (App 9 (P (Plus 10)) [(R 11 (3,''p'')), (R 12 (3,''i'')), (L (Lambda 13 [(13,''p_'')] (App 14 (P (Plus 15)) [(R 16 (3,''i'')), (C 17 -1), (L (Lambda 18 [(18,''i_'')] (App 19 (R 20 (2,''rec'')) [(R 21 (13,''p_'')), (R 22 (18,''i_'')), (R 23 (3,''c_''))])))])))]))), (L (Lambda 24 [] (App 25 (R 26 (3,''c_'')) [(R 27 (3,''p''))])))])))] (App 28 (R 29 (2,''rec'')) [(C 30 0), (C 31 10), (R 32 (1,''cont''))])))"
              
end

