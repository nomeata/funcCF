theory HOLCFAbsCF
  imports CPSUtils HOLCF HOLCFUtils HOLCFList HOLCFOption CPSScheme Utils
begin

class contour =
  fixes nb :: "'a \<Rightarrow> label \<Rightarrow> 'a"

types 'c benv = "label \<rightharpoonup> 'c"
      'c closure = "lambda \<times> 'c benv"

datatype 'c proc = PC "'c closure"
                 | PP prim
                 | Stop

types 'c d = "'c proc set"

types 'c venv = "var \<times> 'c \<rightharpoonup> 'c d"

fun evalV :: "val \<Rightarrow> 'c benv \<Rightarrow> 'c venv \<Rightarrow> 'c d"
  where "evalV (C _ i) \<beta> ve = {}"
  |     "evalV (P prim) \<beta> ve = {PP prim}"
  |     "evalV (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> (case ve (var,l) of Some d \<Rightarrow> d))"
  |     "evalV (L lam) \<beta> ve = {PC (lam, \<beta>)}"

types 'c ccache = "((label \<times> 'c benv) \<times> 'c proc) set"
      'c ans = "'c ccache"

types 'c fstate = "('c proc \<times> 'c d list \<times> 'c venv \<times> 'c)"
      'c cstate = "(call \<times> 'c benv \<times> 'c venv \<times> 'c)"

lemma cont2cont_lambda_case [simp, cont2cont]:
  assumes "\<And>a b c. cont (\<lambda>x. f x a b c)"
  shows "cont (\<lambda>x. lambda_case (f x) l)"
using assms
by (cases l) auto

lemma cont2cont_proc_case [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x y)"
     and  "\<And>y. cont (\<lambda>x. f2 x y)"
     and  "cont (\<lambda>x. f3 x)"
  shows "cont (\<lambda>x. proc_case (f1 x) (f2 x) (f3 x) d)"
using assms
by (cases d) auto

lemma cont2cont_call_case [simp, cont2cont]:
  assumes "\<And>a b c. cont (\<lambda>x. f1 x a b c)"
     and  "\<And>a b c. cont (\<lambda>x. f2 x a b c)"
  shows "cont (\<lambda>x. call_case (f1 x) (f2 x) c)"
using assms
by (cases c) auto

lemma cont2cont_prim_case [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x y)"
     and  "\<And>y z. cont (\<lambda>x. f2 x y z)"
  shows "cont (\<lambda>x. prim_case (f1 x) (f2 x) p)"
using assms
by (cases p) auto


fixrec  evalF :: "'c::contour fstate discr \<rightarrow> 'c ans"
     and evalC :: "'c cstate discr \<rightarrow> 'c ans"
  where "evalF\<cdot>fstate = (case undiscr fstate of
             (PC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
                     in evalC\<cdot>(Discr (c,\<beta>',ve',b))
                else \<bottom>)
            | (PP (Plus c),[_,_,cnts],ve,b) \<Rightarrow>
                     let b' = nb b c;
                         \<beta>  = [c \<mapsto> b]
                     in (\<Union>cnt\<in>cnts. evalF\<cdot>(Discr (cnt,[{}],ve,b')))
                        \<union>
                        {((c, \<beta>), cont) | cont . cont \<in> cnts}
            | (PP (prim.If ct cf),[_, cntts, cntfs],ve,b) \<Rightarrow>
                  ((   let b' = nb b ct;
                            \<beta> = [ct \<mapsto> b]
                        in (\<Union>cnt\<in>cntts . evalF\<cdot>(Discr (cnt,[],ve,b')))
                           \<union>{((ct, \<beta>), cnt) | cnt . cnt \<in> cntts}
                   )\<union>(
                       let b' = nb b cf;
                            \<beta> = [cf \<mapsto> b]
                        in (\<Union>cnt\<in>cntfs . evalF\<cdot>(Discr (cnt,[],ve,b')))
                           \<union>{((cf, \<beta>), cnt) | cnt . cnt \<in> cntfs}
                   ))
            | (Stop,[_],_,_) \<Rightarrow> {}
            | _ \<Rightarrow> \<bottom>
        )"
      | "evalC\<cdot>cstate = (case undiscr cstate of
             (App lab f vs,\<beta>,ve,b) \<Rightarrow>
                 let fs = evalV f \<beta> ve;
                     as = map (\<lambda>v. evalV v \<beta> ve) vs;
                     b' = nb b lab
                  in (\<Union>f' \<in> fs. evalF\<cdot>(Discr (f',as,ve,b')))
                     \<union>{((lab, \<beta>),f') | f' . f'\<in> fs}
            | (Let lab ls c',\<beta>,ve,b) \<Rightarrow>
                 let b' = nb b lab;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                    ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), evalV (L l) \<beta>' ve)) ls)
                 in evalC\<cdot>(Discr (c',\<beta>',ve',b'))
        )"

print_theorems
lemmas evalF_evalC_induct = evalF_evalC.induct[case_names Admissibility Bottom Next]

fun evalF_cases
 where "evalF_cases (DC (Lambda lab vs c, \<beta>)) as ve b = undefined"
     | "evalF_cases (DP (Plus cp)) [DI a1, DI a2, cnt] ve b = undefined"
     | "evalF_cases (DP (prim.If cp1 cp2)) [DI v,cntt,cntf] ve b = undefined"
     | "evalF_cases  Stop [DI v] ve b = undefined"

lemmas fstate_case =  evalF_cases.cases[
  OF case_split, of _ "\<lambda>_ vs _ _ as _ _ . length vs = length as",
  OF _ _ _ case_split, of _ _ "\<lambda>_ _ v _ _ _ _ . v\<noteq>0",
  case_names "Closure" "Closure_inv" "Plus" "If_True" "If_False" "Stop"]

(* unsuccesfully attempt to define a more useful induction rule:

lemma eval_induct:
  assumes admF: "adm PF"
      and amdC: "adm PC"
      and bottomF: "PF {}"
      and bottomC: "PC {}"
      and lamF: "\<And> (evalC::cstate discr \<rightarrow> ans) lab vs c \<beta> as ve b.
        \<lbrakk> PC (evalC\<cdot>(Discr (c, \<beta>(lab \<mapsto> b), ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] as), b)))
        ;  length vs = length as
        \<rbrakk>
        \<Longrightarrow> PF (evalC\<cdot>(Discr (c, \<beta>(lab \<mapsto> b), ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] as), b)))"
      and plusF: "\<And> (evalF::fstate discr \<rightarrow> ans) c a1 a2 cnt ve b.
        PF (evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, Suc b)))
         \<Longrightarrow> PF (evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, Suc b)) \<union> {((c, [c \<mapsto> b]), cnt)})"
      and ifF_True:  "\<And> (evalF::fstate discr \<rightarrow> ans) ct (v::int) cntt ve b.
        \<lbrakk> PF (evalF\<cdot>(Discr (cntt, [], ve, Suc b)))
        ; v \<noteq> 0
        \<rbrakk>
         \<Longrightarrow> PF (evalF\<cdot>(Discr (cntt, [], ve, Suc b)) \<union> {((ct, [ct \<mapsto> b]), cntt)})"
      and ifF_False:  "\<And> (evalF::fstate discr \<rightarrow> ans) cf  cntf ve b.
        PF (evalF\<cdot>(Discr (cntf, [], ve, Suc b)))
         \<Longrightarrow> PF (evalF\<cdot>(Discr (cntf, [], ve, Suc b)) \<union> {((cf, [cf \<mapsto> b]), cntf)})"
      and appC: "\<And> (evalF::fstate discr \<rightarrow> ans) c f vs ve \<beta> b.
         PF (evalF\<cdot>(Discr (evalV f \<beta> ve, map (\<lambda>v. evalV v \<beta> ve) vs, ve, Suc b)))
         \<Longrightarrow> PC ((evalF\<cdot>(Discr (evalV f \<beta> ve, map (\<lambda>v. evalV v \<beta> ve) vs, ve, Suc b)))
                  \<union> {((c, \<beta>), evalV f \<beta> ve)})"
shows "PF (evalF\<cdot>fstate)" and "PC (evalC\<cdot>cstate)"
proof(induct arbitrary: fstate cstate rule: evalF_evalC.induct)
print_cases
case 1 from admF and amdC show ?case
 by (intro adm_lemmas adm_prod_split)
    (auto intro:adm_subst[of _ "PF"] adm_subst[of _ "PC"])
next
case 2 case 1 from bottomF show ?case by simp next
case 2 case 2 from bottomC show ?case by simp next
case (3 evalF evalC)
{
  print_cases
  case (1 fstate)
  from "3.hyps" and bottomF and bottomC and plusF and ifF_True and ifF_False and lamF
  show ?case
    apply (auto split: d.split prod.split lambda.split)
    apply (auto split: d.split prod.split list.split prim.split lambda.split)
    done
  next
  case (2 cstate)
  from "3.hyps" and appC
  show ?case
    by (auto split: call.split prod.split simp add:HOL.Let_def)
}
qed
*)

definition evalCPS :: "prog \<Rightarrow> ans"
  where "evalCPS l = (let ve = empty;
                          \<beta> = empty;
                          f = evalV (L l) \<beta> ve
                      in  evalF\<cdot>(Discr (f,[Stop],ve,initial_contour)))"

lemma correct_ex1: "evalCPS ex1 = {((2,[1 \<mapsto> initial_contour]), Stop)}"
unfolding evalCPS_def
by simp

lemma correct_ex2: "evalCPS ex2 = {((2, [1 \<mapsto> initial_contour]), DP (Plus 3)),
                                   ((3, [3 \<mapsto> nb initial_contour 2]),  Stop)}"
unfolding evalCPS_def
by (simp)

fun benv_in_d
  where "benv_in_d (DC (l,\<beta>)) = {\<beta>}"
      | "benv_in_d _ = {}"

definition benv_in_ve
  where "benv_in_ve ve = \<Union>{benv_in_d d | d . d \<in> ran ve}"

fun contours_in_d
  where "contours_in_d (DC (l,\<beta>)) = ran \<beta>"
      | "contours_in_d _ = {}"

definition contours_in_ve :: "venv \<Rightarrow> contour set"
  where "contours_in_ve ve = \<Union>{contours_in_d d | d . d \<in> ran ve}"

lemma benv_in_ve_upds:
  assumes eq_length: "length vs = length ds"
      and "\<forall>\<beta>\<in>benv_in_ve ve. Q \<beta>"
      and "\<forall>d'\<in>set ds. \<forall>\<beta>\<in>benv_in_d d'. Q \<beta>"
  shows   "\<forall>\<beta>\<in>benv_in_ve (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds)). Q \<beta>"
proof
  fix \<beta>
  assume ass:"\<beta> \<in> benv_in_ve (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds))"
  then obtain d where "\<beta>\<in>benv_in_d d" and "d \<in> ran (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds))" unfolding benv_in_ve_def by auto
  moreover have "ran (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds)) \<subseteq> ran ve \<union> set ds" using eq_length by(auto intro!:ran_upds)
  ultimately
  have "d \<in> ran ve \<or> d \<in> set ds" by auto
  thus "Q \<beta>" using assms(2,3) `\<beta>\<in>benv_in_d d` unfolding benv_in_ve_def by auto
qed

lemma benv_in_eval:
  assumes "\<forall>\<beta>'\<in>benv_in_ve ve. Q \<beta>'"
      and "Q \<beta>"
  shows "\<forall>\<beta>\<in>benv_in_d (evalV v \<beta> ve). Q \<beta>"
proof(cases v)
  case (R _ var)
  thus ?thesis
  proof (cases "\<beta> (fst var)")
    case None with R show ?thesis by simp next
    case (Some cnt) show ?thesis
    proof (cases "ve (var,cnt)")
      case None with Some R show ?thesis by simp next
      case (Some d)
        hence "d \<in> ran ve" unfolding ran_def by blast
        thus ?thesis using Some `\<beta> (fst var) = Some cnt` R assms(1)
          unfolding benv_in_ve_def by auto
    qed
  qed next
  case (L l) thus ?thesis using assms(2) by simp next
  case C thus ?thesis by simp next
  case P thus ?thesis by simp
qed

lemma contours_in_ve_empty[simp]: "contours_in_ve empty = {}"
  unfolding contours_in_ve_def by auto

lemma contours_in_ve_upds:
  assumes eq_length: "length vs = length ds"
      and "\<forall>b'\<in>contours_in_ve ve. Q b'"
      and "\<forall>d'\<in>set ds. \<forall>b'\<in>contours_in_d d'. Q b'"
  shows   "\<forall>b'\<in>contours_in_ve (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds)). Q b'"
proof-
  have "ran (ve(map (\<lambda>v. (v, b'')) vs [\<mapsto>] ds)) \<subseteq> ran ve \<union> set ds" using eq_length by(auto intro!:ran_upds)
  thus ?thesis using assms(2,3) unfolding contours_in_ve_def  by blast
qed

lemma contours_in_ve_upds_binds:
  assumes "\<forall>b'\<in>contours_in_ve ve. Q b'"
      and "\<forall>b'\<in>ran \<beta>'. Q b'"
  shows   "\<forall>b'\<in>contours_in_ve (ve ++ map_of (map (\<lambda>(v,l). ((v,b''), evalV (L l) \<beta>' ve)) ls)). Q b'"
proof
  fix b' assume "b'\<in>contours_in_ve (ve ++ map_of (map (\<lambda>(v,l). ((v,b''), evalV (L l) \<beta>' ve)) ls))"
  then obtain d where d:"d \<in> ran (ve ++ map_of (map (\<lambda>(v,l). ((v,b''), evalV (L l) \<beta>' ve)) ls))" and b:"b' \<in> contours_in_d d" unfolding contours_in_ve_def by auto

  have "ran (ve ++ map_of (map (\<lambda>(v,l). ((v,b''), evalV (L l) \<beta>' ve)) ls)) \<subseteq> ran ve \<union> ran (map_of (map (\<lambda>(v,l). ((v,b''), evalV (L l) \<beta>' ve)) ls))"
    by(auto intro!:ran_concat)
  also
  have "\<dots> \<subseteq> ran ve \<union> snd ` set (map (\<lambda>(v,l). ((v,b''), evalV (L l) \<beta>' ve)) ls)"
    by (rule Un_mono[of "ran ve" "ran ve", OF subset_refl ran_map_of])
  also
  have "\<dots> \<subseteq> ran ve \<union> set (map (\<lambda>(v,l). (evalV (L l) \<beta>' ve)) ls)"
    by (rule Un_mono[of "ran ve" "ran ve", OF subset_refl ])auto
  finally
  have "d \<in>  ran ve \<union> set (map (\<lambda>(v,l). (evalV (L l) \<beta>' ve)) ls)" using d by auto
  thus "Q b'"  using assms b unfolding contours_in_ve_def by auto
qed

lemma contours_in_eval:
  assumes "\<forall>b'\<in>contours_in_ve ve. Q b'"
      and "\<forall>b'\<in> ran \<beta>. Q b'"
  shows "\<forall>b'\<in>contours_in_d (evalV f \<beta> ve). Q b'"
unfolding contours_in_ve_def
proof(cases f)
  case (R _ var)
  thus ?thesis
  proof (cases "\<beta> (fst var)")
    case None with R show ?thesis by simp next
    case (Some cnt) show ?thesis
    proof (cases "ve (var,cnt)")
      case None with Some R show ?thesis by simp next
      case (Some d)
        hence "d \<in> ran ve" unfolding ran_def by blast
        thus ?thesis using Some `\<beta> (fst var) = Some cnt` R `\<forall>b'\<in>contours_in_ve ve. Q b'`
          unfolding contours_in_ve_def
          by auto
    qed
  qed next
  case (L l) thus ?thesis using `\<forall>b'\<in> ran \<beta>. Q b'` by simp next
  case C thus ?thesis by simp next
  case P thus ?thesis by simp
qed

end