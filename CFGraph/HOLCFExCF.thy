theory HOLCFExCF
  imports CPSUtils HOLCF HOLCFUtils CPSScheme Utils
begin

typedef contour = "UNIV::label list set" by auto

definition initial_contour
  where "initial_contour = Abs_contour []"

definition nb 
  where "nb b c = Abs_contour (c # Rep_contour b)"

instantiation contour :: preorder
begin
definition le_contour_def: "b \<le> b' \<longleftrightarrow> length (Rep_contour b) \<le> length (Rep_contour b')"
definition less_contour_def: "b < b' \<longleftrightarrow> length (Rep_contour b) < length (Rep_contour b')"
instance proof
qed(auto simp add:le_contour_def less_contour_def Rep_contour_inverse Abs_contour_inverse contour_def)
end

lemma nb_le_less[iff]: "nb b c \<le> b' \<longleftrightarrow> b < b'"
  unfolding nb_def
  by (auto simp add:le_contour_def less_contour_def Rep_contour_inverse Abs_contour_inverse contour_def)

lemma nb_less[iff]: "b' < nb b c \<longleftrightarrow> b' \<le> b"
  unfolding nb_def
  by (auto simp add:le_contour_def less_contour_def Rep_contour_inverse Abs_contour_inverse contour_def)

declare less_imp_le[where 'a = contour, intro]

instantiation contour :: discrete_cpo
begin
definition [simp]: "(x::contour) \<sqsubseteq> y \<longleftrightarrow> x = y"
instance by default simp
end

types benv = "label \<rightharpoonup> contour"
      closure = "lambda \<times> benv"

datatype d = DI int
           | DC closure
           | DP prim
           | Stop

primrec isProc 
  where "isProc (DI _) = False"
      | "isProc (DC _) = True"
      | "isProc (DP _) = True"
      | "isProc Stop   = True"

instantiation d :: discrete_cpo begin
definition  [simp]: "(x::d) \<sqsubseteq> y \<longleftrightarrow> x = y"
instance by default simp
end

instantiation call :: discrete_cpo begin
definition  [simp]: "(x::call) \<sqsubseteq> y \<longleftrightarrow> x = y"
instance by default simp
end

types venv = "var \<times> contour \<rightharpoonup> d"

fun evalV :: "val \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> d"
  where "evalV (C _ i) \<beta> ve = DI i"
  |     "evalV (P prim) \<beta> ve = DP prim"
  |     "evalV (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> (case ve (var,l) of Some d \<Rightarrow> d | None \<Rightarrow> DI 0) (* I prefer this to be total\<dots> *)
             | None \<Rightarrow> DI 0)"
  |     "evalV (L lam) \<beta> ve = DC (lam, \<beta>)"


types ccache = "((label \<times> benv) \<times> d) set"
      ans = ccache

(*
definition covers :: "prog \<Rightarrow> benv \<Rightarrow>venv \<Rightarrow> bool" where
     "covers prog \<beta> ve = (\<forall> l\<in>dom \<beta>. \<forall> v \<in> vars prog. (binder v = l \<longrightarrow> (case \<beta> l of Some cnt \<Rightarrow> (v,cnt) \<in> dom ve)))"

definition ve_consistent :: "prog \<Rightarrow> call \<Rightarrow> benv \<Rightarrow> venv \<Rightarrow> bool" where
     "ve_consistent prog c \<beta> ve =
        ((\<forall> ctx \<in> subterms (Inl prog). (Inr c \<in> subterms ctx \<longrightarrow> label ctx \<in> dom \<beta>))
         \<and> covers prog \<beta> ve)"

definition closure_consistent :: "prog \<Rightarrow> closure \<Rightarrow> venv \<Rightarrow> bool" where
     "closure_consistent prog cls ve =
        ((\<forall> ctx \<in> subterms (Inl prog). (Inl (fst cls) \<in> subterms ctx \<longrightarrow> label ctx \<in> dom (snd cls)))
         \<and> covers prog (snd cls) ve)"

definition cstate_ok :: "cstate \<Rightarrow> bool" where
     "cstate_ok s = (case s of (c,\<beta>,ve,_) \<Rightarrow> ve_consistent c \<beta> ve)"
*)

types fstate = "(d \<times> d list \<times> venv \<times> contour)"
      cstate = "(call \<times> benv \<times> venv \<times> contour)"

lemma cont2cont_lambda_case [simp, cont2cont]:
  assumes "\<And>a b c. cont (\<lambda>x. f x a b c)"
  shows "cont (\<lambda>x. lambda_case (f x) l)"
using assms
by (cases l) auto

lemma cont2cont_d_case [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x y)"
     and  "\<And>y. cont (\<lambda>x. f2 x y)"
     and  "\<And>y. cont (\<lambda>x. f3 x y)"
    and   "cont (\<lambda>x. f4 x)"
  shows "cont (\<lambda>x. d_case (f1 x) (f2 x) (f3 x) (f4 x) d)"
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


fixrec   evalF :: "fstate discr \<rightarrow> ans"
     and evalC :: "cstate discr \<rightarrow> ans"
  where "evalF\<cdot>fstate = (case undiscr fstate of
             (DC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
                     in evalC\<cdot>(Discr (c,\<beta>',ve',b))
                else \<bottom>)
            | (DP (Plus c),[DI a1, DI a2, cnt],ve,b) \<Rightarrow>
                (if isProc cnt
                 then let b' = nb b c;
                          \<beta>  = [c \<mapsto> b]
                      in evalF\<cdot>(Discr (cnt,[DI (a1 + a2)],ve,b'))
                        \<union> {((c, \<beta>),cnt)}
                 else \<bottom>)
            | (DP (prim.If ct cf),[DI v, contt, contf],ve,b) \<Rightarrow>
                (if isProc contt \<and> isProc contf
                 then
                  (if v \<noteq> 0
                   then let b' = nb b ct;
                            \<beta> = [ct \<mapsto> b]
                        in (evalF\<cdot>(Discr (contt,[],ve,b'))
                            \<union> {((ct, \<beta>),contt)})
                   else let b' = nb b cf;
                            \<beta> = [cf \<mapsto> b]
                        in (evalF\<cdot>(Discr (contf,[],ve,b')))
                            \<union> {((cf, \<beta>),contf)})
                 else \<bottom>)
            | (Stop,[DI i],_,_) \<Rightarrow> {}
            | _ \<Rightarrow> \<bottom>
        )"
      | "evalC\<cdot>cstate = (case undiscr cstate of
             (App lab f vs,\<beta>,ve,b) \<Rightarrow>
                 let f' = evalV f \<beta> ve;
                     as = map (\<lambda>v. evalV v \<beta> ve) vs;
                     b' = nb b lab
                  in evalF\<cdot>(Discr (f',as,ve,b'))
                     \<union> {((lab, \<beta>),f')}
            | (Let lab ls c',\<beta>,ve,b) \<Rightarrow>
                 let b' = nb b lab;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                    ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), evalV (L l) \<beta>' ve)) ls)
                 in evalC\<cdot>(Discr (c',\<beta>',ve',b'))
        )"
lemmas evalF_evalC_induct = evalF_evalC.induct[case_names Admissibility Bottom Next]

lemmas cl_cases = prod.exhaust[OF lambda.exhaust, of _ "\<lambda> a _ . a"]
lemmas ds_cases_plus = list.exhaust[
  OF _ d.exhaust, of _ _ "\<lambda>a _. a",
  OF _ list.exhaust, of _ _ "\<lambda>_ x _. x",
  OF _ _ d.exhaust, of _ _ "\<lambda>_ _ _ a _. a",
  OF _ _ list.exhaust,of _ _ "\<lambda>_ _ _ _ x _. x",
  OF _ _ _ list.exhaust,of _ _ "\<lambda>_ _ _ _ _ _ _ x. x"
  ]
lemmas ds_cases_if = list.exhaust[OF _ d.exhaust, of _ _ "\<lambda>a _. a",
  OF _ list.exhaust[OF _ list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"], of _ _ "\<lambda>_ x. x"], of _ _ "\<lambda>_ x _. x"]
lemmas ds_cases_stop = list.exhaust[OF _ d.exhaust, of _ _ "\<lambda>a _. a",
  OF _ list.exhaust, of _ _ "\<lambda>_ x _. x"]
lemmas fstate_case = prod_cases4[OF d.exhaust, of _ "\<lambda>x _ _ _ . x",
  OF _ cl_cases prim.exhaust, of _ _ "\<lambda> _ _ _ _ a . a" "\<lambda> _ _ _ _ a. a",
  OF _ case_split ds_cases_plus ds_cases_if ds_cases_stop,
  of _ _ "\<lambda>_ as _ _ _ _ _ _ vs _ . length vs = length as" "\<lambda> _ ds _ _ _ _ . ds" "\<lambda> _ ds _ _ _ _ _. ds" "\<lambda> _ ds _ _. ds",
  case_names "x" "Closure" "x" "x"  "x" "x" "Plus" "x" "x" "x" "x" "x" "x" "x" "x"   "x" "x" "If_True" "If_False" "x" "x" "x" "x" "x" "Stop"  "x" "x" "x" "x" "x"]

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