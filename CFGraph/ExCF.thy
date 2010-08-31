theory ExCF
  imports CPSScheme Eval
begin

(* Data types imported from Eval where possible *)

types ccache = "label \<times> benv \<rightharpoonup> d"
      ans = ccache

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
          = (case as of  [DI a1, DI a2, cont] \<Rightarrow>
                   let b' = Suc b;
                       \<beta>  = [c \<mapsto> b]
                   in evalF cont [DI (a1 + a2)] ve b' ((c, \<beta>) \<mapsto> cont))"
  |     "evalF (DP (If ct cf)) [DI v, contt, contf] ve b
          = (      if v \<noteq> 0
                   then let b' = Suc b;
                            \<beta> = [ct \<mapsto> b]
                        in evalF contt [] ve b
                   else let b' = Suc b;
                            \<beta> = [cf \<mapsto> b]
                        in evalF contf [] ve b')"
  |     "evalF Stop as _ _
          = (case as of [DI i] \<Rightarrow> empty)"

  |     "evalC (App lab f vs) \<beta> ve b
          = (let f' = evalV f \<beta> ve;
                 as = map (\<lambda>v. evalV v \<beta> ve) vs;
                 b' = Suc b
             in evalF f' as ve b' ((lab,\<beta>) \<mapsto> f'))"
  |     "evalC (Let lab ls c') \<beta> ve b
          = (let b' = Suc b;
                 \<beta>' = \<beta> (lab \<mapsto> b');
                 ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), evalV (L l) \<beta>' ve)) ls)
            in evalC c' \<beta>' ve' b')"
  apply pat_completeness
  apply auto
done

lemma "ExCF.evalF_evalC_rel = Eval.evalF_evalC_rel"
unfolding ExCF.evalF_evalC_rel_def and Eval.evalF_evalC_rel_def
by auto

definition evalCPS :: "prog \<Rightarrow> ans"
  where "evalCPS l = (let ve = empty;
                          \<beta> = empty;
                          f = evalV (L l) \<beta> ve
                      in  evalF f [Stop] ve 0)"

termination sorry
lemma correct_ex1: "evalCPS ex1 = [(2,[1 \<mapsto> 0]) \<mapsto> Stop]"
unfolding evalCPS_def
by simp

lemma correct_ex2: "evalCPS ex2 = [(2, [1 \<mapsto> 0]) \<mapsto> DP (Plus 3), (3, [3 \<mapsto> 1]) \<mapsto> Stop]"
unfolding evalCPS_def
apply (rule ext) (* Otherwise simp fails because the order of entries differs *)
by simp






end
