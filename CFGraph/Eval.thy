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

function (sequential,domintros,tailrec)
         evalF :: "d \<Rightarrow> (d list) \<Rightarrow> venv \<Rightarrow> contour \<Rightarrow> ans"
     and evalC :: "call \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> contour \<Rightarrow> ans"
  where "evalF (DC (Lambda lab vs c, \<beta>)) as ve b
          = (if length vs = length as
             then let \<beta>' = \<beta> (lab \<mapsto> b);
                      ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
                  in evalC c \<beta>' ve' b
             else undefined
            )"
  |     "evalF (DP (Plus c)) as ve b 
          = (case as of [DI a1, DI a2, cont] \<Rightarrow> 
                  (let b' = Suc b
                   in evalF cont [DI (a1 + a2)] ve b'))"
  |     "evalF (DP (If ct cf)) as ve b
          = (case as of [DI v, contt, contf] \<Rightarrow> (      
                  let b' = Suc b
                   in if v \<noteq> 0 then evalF contt [] ve b'
                               else evalF contt [] ve b'))"
  |     "evalF Stop as _ _
          = (case as of [DI i] \<Rightarrow> i)"

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
  apply pat_completeness
  apply auto
done

print_theorems

thm evalF_evalC.domintros(1)

definition evalCPS :: "prog \<Rightarrow> int"
  where "evalCPS l = (let ve = empty;
                          \<beta> = empty;
                          f = evalV (L l) \<beta> ve
                      in  evalF f [Stop] ve 0)"

definition eval_terminates :: "prog \<Rightarrow> bool" where
    "eval_terminates l = (
       let ve = empty;
           \<beta> = empty;
           f = evalV (L l) \<beta> ve
       in evalF_evalC_dom (Inl (f, [Stop], ve, 0)))"

lemma ex1_terminates[simp]: "eval_terminates ex1"
unfolding eval_terminates_def
by (auto intro!:evalF_evalC.domintros)

lemma ex1_correct: "evalCPS ex1 = 0"
unfolding evalCPS_def
apply simp
apply (insert ex1_terminates)
unfolding eval_terminates_def
apply simp
thm evalF_evalC.domintros(1)
thm evalC.psimps(1)
apply (erule evalC.psimps(1))

apply (auto intro!:evalF_evalC.domintros)

apply simp

apply