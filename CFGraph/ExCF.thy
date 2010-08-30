theory ExCF
  imports CPSScheme 
begin

types contour = nat
      benv = "label \<rightharpoonup> contour"
      closure = "lambda \<times> benv"

datatype d = DI int
           | DC closure
           | DP prim
           | Stop

types venv = "var \<times> contour \<rightharpoonup> d"

types ccache = "label \<times> benv \<rightharpoonup> d"
      ans = unit

fun evalV :: "val \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> d"
  where "evalV (C _ i) \<beta> ve = DI i"
  |     "evalV (P prim) \<beta> ve = DP prim"
  |     "evalV (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> (case ve (var,l) of Some d \<Rightarrow> d))"
  |     "evalV (L lam) \<beta> ve = DC (lam, \<beta>)"

fun evalF :: "d \<Rightarrow> (d list) \<Rightarrow> venv \<Rightarrow> contour \<Rightarrow> ans"
and evalC :: "call \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> contour \<Rightarrow> ans"
  where "evalF (DC (Lambda lab vs c, \<beta>)) as ve b = ()"
  |     "evalF (DP (Plus c)) [DI a1, DI a2, cont] ve b = ()"
  |     "evalF (DP (If ct cf)) [DI v, contt, contf] ve b = ()"
  |     "evalF Stop [DI i] _ _ = ()"
  |     "evalC (App lab f vs) \<beta> ve b = ()"
  |     "evalC (Let lab ls c') \<beta> ve b = ()"

end
