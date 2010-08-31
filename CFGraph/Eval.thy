theory Eval
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

types ans = int

fun evalV :: "val \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> d"
  where "evalV (C _ i) \<beta> ve = DI i"
  |     "evalV (P prim) \<beta> ve = DP prim"
  |     "evalV (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> (case ve (var,l) of Some d \<Rightarrow> d))"
  |     "evalV (L lam) \<beta> ve = DC (lam, \<beta>)"

function (sequential,domintros)
         evalF :: "d \<Rightarrow> (d list) \<Rightarrow> venv \<Rightarrow> contour \<Rightarrow> ans"
     and evalC :: "call \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> contour \<Rightarrow> ans"
  where "evalF (DC (Lambda lab vs c, \<beta>)) as ve b
          = (case length vs = length as of True \<Rightarrow>
            let \<beta>' = \<beta> (lab \<mapsto> b);
                ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
            in evalC c \<beta>' ve' b
            )"
  |     "evalF (DP (Plus c)) as ve b 
          = (case as of
               [DI a1, DI a2, cont] \<Rightarrow> 
                  (let b' = Suc b
                   in evalF cont [DI (a1 + a2)] ve b'))"
  |     "evalF (DP (If ct cf)) as ve b
          = (case as of
               [DI v, contt, contf] \<Rightarrow> (      
                  let b' = Suc b
                   in if v \<noteq> 0 then evalF contt [] ve b'
                               else evalF contt [] ve b'))"
  |     "evalF Stop as _ _ = (
                case as of [DI i] \<Rightarrow> i)"

  |     "evalC (App lab f vs) \<beta> ve b
          = (let f' = evalV f \<beta> ve;
                 as = map (\<lambda>v. evalV v \<beta> ve) vs;
                 b' = Suc b
             in evalF f' as ve b')"
  |     "evalC (Let lab ls c') \<beta> ve b
          = (let b' = Suc b;
                 \<beta>' = \<beta> (lab \<mapsto> b');
                 ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), evalV (L l) \<beta>' ve)) ls)
            in evalC c' \<beta>' ve' b')"
  by pat_completeness auto

print_theorems

end
