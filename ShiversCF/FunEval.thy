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

declare id_apply[simp del]
function (sequential,domintros)
         evalF :: "d \<Rightarrow> (d list) \<Rightarrow> venv \<Rightarrow> contour \<Rightarrow> ans"
     and evalC :: "call \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> contour \<Rightarrow> ans"
  where "evalF (DC (Lambda lab vs c, \<beta>)) as ve b
          = (case length vs = length as of
              True \<Rightarrow> let \<beta>' = \<beta> (lab \<mapsto> b);
                          ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
                      in evalC c \<beta>' ve' b
            )"
  |     "evalF (DP (Plus c)) as ve b
          = (case id as of [DI a1, DI a2, cont] \<Rightarrow>
                   let b' = Suc b
                   in evalF cont [DI (a1 + a2)] ve b')"
  |     "evalF (DP (If ct cf)) [DI v, contt, contf] ve b
          = (      if id (v \<noteq> 0) then
                        let b' = Suc b
                        in evalF contt [] ve b'
                   else let b' = Suc b
                        in evalF contf [] ve b')"
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
declare id_apply[simp]

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

lemma ex2_terminates[simp]: "eval_terminates ex2"
unfolding eval_terminates_def
by (auto intro!:evalF_evalC.domintros)

(* Does not work without termination or tailrec *)
(*
lemma ex1_correct: "evalCPS ex1 = 0"
unfolding evalCPS_def
by simp

lemma ex2_correct: "evalCPS ex2 = 2"
unfolding evalCPS_def
by simp
*)

(* These lemmas take some time, thus skipping them *)
(*
lemma ex3_correct: "evalCPS ex3 = 55"
unfolding evalCPS_def
by simp

lemma ex3_terminates[simp]: "eval_terminates ex3"
unfolding eval_terminates_def
by (auto intro!:evalF_evalC.domintros)
*)
end