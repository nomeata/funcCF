theory HOLCFEval
  imports CPSUtils HOLCF HOLCFUtils HOLCFList HOLCFOption CPSScheme Utils
begin

types contour = nat
      benv = "label \<rightharpoonup> contour"
      closure = "lambda \<times> benv"

datatype d = DI int
           | DC closure
           | DP prim
           | Stop

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
                     let b' = Suc b;
                         \<beta>  = [c \<mapsto> b]
                     in evalF\<cdot>(Discr (cnt,[DI (a1 + a2)],ve,b'))
                        \<union> {((c, \<beta>),cnt)}
            | (DP (prim.If ct cf),[DI v, contt, contf],ve,b) \<Rightarrow>
                  (if v \<noteq> 0
                   then let b' = Suc b;
                            \<beta> = [ct \<mapsto> b]
                        in (evalF\<cdot>(Discr (contt,[],ve,b'))
                            \<union> {((ct, \<beta>),contt)})
                   else let b' = Suc b;
                            \<beta> = [cf \<mapsto> b]
                        in (evalF\<cdot>(Discr (contf,[],ve,b')))
                            \<union> {((cf, \<beta>),contf)})
            | (Stop,[DI i],_,_) \<Rightarrow> {}
            | _ \<Rightarrow> \<bottom>
        )"
      | "evalC\<cdot>cstate = (case undiscr cstate of
             (App lab f vs,\<beta>,ve,b) \<Rightarrow>
                 let f' = evalV f \<beta> ve;
                     as = map (\<lambda>v. evalV v \<beta> ve) vs;
                     b' = Suc b
                  in evalF\<cdot>(Discr (f',as,ve,b'))
                     \<union> {((lab, \<beta>),f')}
            | (Let lab ls c',\<beta>,ve,b) \<Rightarrow>
                 let b' = Suc b;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                    ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), evalV (L l) \<beta>' ve)) ls)
                 in evalC\<cdot>(Discr (c',\<beta>',ve',b'))
        )"

print_theorems

fun evalF_cases
 where "evalF_cases (DC (Lambda lab vs c, \<beta>)) as ve b = undefined"
     | "evalF_cases (DP (Plus cp)) [DI a1, DI a2, cnt] ve b = undefined"
     | "evalF_cases (DP (prim.If cp1 cp2)) [DI v,cntt,cntf] ve b = undefined"
     | "evalF_cases  Stop [DI v] ve b = undefined"

lemmas fstate_case =  evalF_cases.cases[
  OF case_split, of _ "\<lambda>_ vs _ _ as _ _ . length vs = length as",
  OF _ _ _ case_split, of _ _ "\<lambda>_ _ v _ _ _ _ . v\<noteq>0",
  case_names "Closure" "Closure_inv" "Plus" "If_True" "If_False" "Stop"]


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


definition evalCPS :: "prog \<Rightarrow> ans"
  where "evalCPS l = (let ve = empty;
                          \<beta> = empty;
                          f = evalV (L l) \<beta> ve
                      in  evalF\<cdot>(Discr (f,[Stop],ve,0)))"

lemma correct_ex1: "evalCPS ex1 = {((2,[1 \<mapsto> 0]), Stop)}"
unfolding evalCPS_def
by simp

lemma correct_ex2: "evalCPS ex2 = {((2, [1 \<mapsto> 0]), DP (Plus 3)),
                                   ((3, [3 \<mapsto> 1]),  Stop)}"
unfolding evalCPS_def
by simp

fun benv_in_d 
  where "benv_in_d (DC (l,\<beta>)) = {\<beta>}"
      | "benv_in_d _ = {}"

definition benv_in_ve
  where "benv_in_ve ve = \<Union>{benv_in_d d | d . d \<in> ran ve}"

fun contours_in_d
  where "contours_in_d (DC (l,\<beta>)) = ran \<beta>"
      | "contours_in_d _ = {}"

definition contours_in_ve :: "venv \<Rightarrow> nat set"
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


lemma cc_single_valued':
      "\<lbrakk> \<forall>b' \<in> contours_in_ve ve. b' < b
       ; \<forall>b' \<in> contours_in_d d. b' < b
       ; \<forall>d' \<in> set ds. \<forall>b' \<in> contours_in_d d'. b' < b
       \<rbrakk>
       \<Longrightarrow>
       (   single_valued (evalF\<cdot>(Discr (d,ds,ve,b)))
       &&& (\<And> lab \<beta> t. ((lab,\<beta>),t) \<in> evalF\<cdot>(Discr (d,ds,ve, b)) \<Longrightarrow> \<exists> b'. b' \<in> ran \<beta> \<and> b \<le> b')
       )"
  and "\<lbrakk> b \<in> ran \<beta>'
       ; \<forall>b'\<in>ran \<beta>'. b' \<le> b
       ; \<forall>b' \<in> contours_in_ve ve. b' \<le> b
       \<rbrakk>
       \<Longrightarrow>
       (   single_valued (evalC\<cdot>(Discr (c,\<beta>',ve,b)))
       &&& (\<And> lab \<beta> t. ((lab,\<beta>),t) \<in> evalC\<cdot>(Discr (c,\<beta>',ve,b)) \<Longrightarrow> \<exists> b'. b' \<in> ran \<beta> \<and> b \<le> b' )
       )"
proof(induct arbitrary:d ds ve b c \<beta>' b' rule:evalF_evalC.induct)
print_cases
case 1 show ?case
  (* admissibility *)
  by (intro adm_lemmas adm_prod_split adm_not_conj adm_not_mem adm_single_valued cont2cont)
next
  case 2 {
    case 1 thus ?case by (auto simp add:mem_def) next
    case 2 thus ?case by (auto simp add:mem_def) next
    case 3 thus ?case by (auto simp add:mem_def) next
    case 4 thus ?case by (auto simp add:mem_def)
  }
next
  case (3 evalF evalC)
  {
  print_cases
  case (1 d ds ve b)
  show ?case
  proof (cases rule:fstate_case)
  print_cases

  proof (cases d)
    case (DI i)
    thus ?thesis by simp
  next
    case (DC closure)
    show ?thesis
    proof (cases closure)
    case (Pair lambda \<beta>')
      show ?thesis
      proof (cases lambda)
      case (Lambda lab' vs c)
        show ?thesis
        proof (cases "length vs = length ds")
          case False with Lambda Pair DC show ?thesis by simp next
          case True 
            have new: "b\<in>ran (\<beta>'(lab' \<mapsto> b))" by simp

            have b_dom_beta: "\<forall>b'\<in> ran (\<beta>'(lab' \<mapsto> b)). b' \<le> b"
            proof fix b' assume "b' \<in> ran (\<beta>'(lab' \<mapsto> b))"
              hence "b' \<in> ran \<beta>' \<or> b' \<le> b" by (auto dest:ran_upd[THEN subsetD])
              thus "b' \<le> b" using  "3.prems"(2) DC Pair by auto
            qed
            
            have "\<forall>b'\<in>contours_in_ve (ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds)). b' < b"
              by (rule contours_in_ve_upds[OF True "3.prems"(1) "3.prems"(3)])
            hence b_dom_ve: "\<forall>b'\<in>contours_in_ve (ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds)). b' \<le> b"
                by auto
            
            from "3.hyps"(3)[OF new b_dom_beta b_dom_ve, of c]
            show ?thesis using True Lambda Pair DC
               by (auto simp del:fun_upd_apply)
        qed
      qed
    qed
  next
  case (DP prim)
    show ?thesis
    proof (cases prim)
      case (Plus cp)
      show ?thesis
      proof (cases "\<exists> i1 i2 cnt. ds = [DI i1, DI i2, cnt]")
        case True then obtain i1 i2 cnt where ds: "ds = [DI i1, DI i2, cnt]" by auto
        
        have b_dom_d: "\<forall>b'\<in>contours_in_d cnt. b' < Suc b" using "3.prems"(3) and ds by auto
        have b_dom_ds: "\<forall>d' \<in> set [DI (i1+i2)]. \<forall>b'\<in>contours_in_d d'. b' < Suc b" by auto
        have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < Suc b" using "3.prems"(1) by auto
        {
          fix t
          assume "((cp,[cp \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, Suc b))"
          hence "\<exists>b'. b' \<in> ran [cp \<mapsto> b] \<and> Suc b \<le> b'" using b_dom_d b_dom_ds b_dom_ve
          by -(rule "3.hyps"(2)[rotated 3])
          hence False by simp
        }
        with "3.hyps"(1) and  b_dom_d b_dom_ds b_dom_ve
        have "single_valued ((evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, Suc b)))
                            \<union> {((cp, [cp \<mapsto> b]), cnt)})"
        by (auto intro!:single_valued_insert split:prod.split)blast
        thus ?thesis using ds Plus DP by auto
      next
        case False
        show ?thesis using DP Plus False by (simp split: list.split d.split) 
      qed
    next
      case (If cp1 cp2)
      show ?thesis
      proof (cases "\<exists> i cntt cntf. ds = [DI i, cntt, cntf]")
        case True then obtain i cntt cntf where ds:"ds = [DI i, cntt, cntf]" by auto

        have b_dom_d1: "\<forall>b'\<in>contours_in_d cntt. b' < Suc b" using "3.prems"(3) and ds by auto
        have b_dom_d2: "\<forall>b'\<in>contours_in_d cntf. b' < Suc b" using "3.prems"(3) and ds by auto
        have b_dom_ds: "\<forall>d' \<in> set []. \<forall>b'\<in>contours_in_d d'. b' < Suc b" by auto
        have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < Suc b" using "3.prems"(1) by auto

        show ?thesis proof(cases "i\<noteq>0")
        case True
        {
          fix t
          assume "((cp1,[cp1 \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, Suc b))"
          hence "\<exists>b'. b' \<in> ran [cp1 \<mapsto> b] \<and> Suc b \<le> b'" using b_dom_d1 b_dom_ds b_dom_ve
            by -(rule "3.hyps"(2)[rotated 3])
          hence False by simp
        }
        with "3.hyps"(1)
        have "single_valued ((evalF\<cdot>(Discr (cntt, [], ve, Suc b)))
                            \<union> {((cp1, [cp1 \<mapsto> b]), cntt)})"  using b_dom_d1 b_dom_ds b_dom_ve
        by (auto intro!:single_valued_insert split:prod.split)blast 
        thus ?thesis using ds If DP True by auto
      next
        case False
        {
          fix t
          assume "((cp2,[cp2 \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cntf, [], ve, Suc b))"
          hence "\<exists>b'. b' \<in> ran [cp2 \<mapsto> b] \<and> Suc b \<le> b'" using b_dom_d2 b_dom_ds b_dom_ve
            by -(rule "3.hyps"(2)[rotated 3])
          hence False by simp
        }
        with "3.hyps"(1)
        have "single_valued ((evalF\<cdot>(Discr (cntf, [], ve, Suc b)))
                            \<union> {((cp2, [cp2 \<mapsto> b]), cntf)})"  using b_dom_d2 b_dom_ds b_dom_ve
        by (auto intro!:single_valued_insert split:prod.split)blast
        thus ?thesis using ds If DP False by auto
      qed
    next
        case False
        show ?thesis using DP If False
          by(simp split: list.split d.split)
      qed
    qed
  next
    case Stop
    thus ?thesis by (simp split: list.split d.split)
  qed
next
  case (2 d ds ve b lab \<beta> t)
  show ?case
  proof (cases d)
    case (DI i)
    thus ?thesis using "3.prems" by simp
  next 
    case (DC closure)
    show ?thesis
    proof (cases closure)
    case (Pair lambda \<beta>')
      show ?thesis
      proof (cases lambda)
      case (Lambda lab' vs c)        
        have eq_length: "length vs = length ds" 
          using "3.prems" Lambda Pair DC
          by -(rule ccontr,simp)

        have new: "b\<in>ran (\<beta>'(lab' \<mapsto> b))" by simp
        
        have b_dom_beta: "\<forall>b'\<in> ran (\<beta>'(lab' \<mapsto> b)). b' \<le> b"
        proof fix b' assume "b' \<in> ran (\<beta>'(lab' \<mapsto> b))"
          hence "b' \<in> ran \<beta>' \<or> b' \<le> b" by (auto dest:ran_upd[THEN subsetD])
          thus "b' \<le> b" using  "3.prems"(2) DC Pair by auto
        qed
        
        have "\<forall>b'\<in>contours_in_ve (ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds)). b' < b"
          by (rule contours_in_ve_upds[OF eq_length "3.prems"(1) "3.prems"(3)])
        hence b_dom_ve: "\<forall>b'\<in>contours_in_ve (ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds)). b' \<le> b"
           by auto
        
        from "3.hyps"(4)[OF new b_dom_beta b_dom_ve]
        show ?thesis using eq_length Lambda Pair DC "3.prems"(4)
          by (auto simp del:fun_upd_apply)
      qed
    qed
  next
  case (DP prim)
    show ?thesis
    proof (cases prim)
      case (Plus cp)
      show ?thesis
      proof (cases "\<exists> i1 i2 cnt. ds = [DI i1, DI i2, cnt]")
        case True then obtain i1 i2 cnt where ds: "ds = [DI i1, DI i2, cnt]" by auto
        with "3.prems" DP Plus 
        have "((lab, \<beta>), t) = ((cp, [cp \<mapsto> b]), cnt)
            \<or> ((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, Suc b))"
        by (simp)
        thus ?thesis using assms
        proof
          assume "((lab, \<beta>), t) = ((cp, [cp \<mapsto> b]), cnt)"          
          hence "\<exists>b'. b' \<in> ran \<beta> \<and> b = b'" by auto
          thus ?thesis by blast
        next
        have b_dom_d: "\<forall>b'\<in>contours_in_d cnt. b' < Suc b" using "3.prems"(3) and ds by auto
        have b_dom_ds: "\<forall>d' \<in> set [DI (i1+i2)]. \<forall>b'\<in>contours_in_d d'. b' < Suc b" by auto
        have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < Suc b" using "3.prems"(1) by auto

          assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, Suc b))"
          hence "\<exists>b'. b' \<in> ran \<beta> \<and> Suc b \<le> b'" 
            using b_dom_d b_dom_ds b_dom_ve
            by -(rule "3.hyps"(2)[rotated 3])
          thus ?thesis by auto
        qed
      next
        case False
        show ?thesis using "3.prems" DP Plus False
          by(simp split: list.split_asm d.split_asm) 
      qed
    next
      case (If cp1 cp2)
      show ?thesis
      proof (cases "\<exists> i cntt cntf. ds = [DI i, cntt, cntf]")
        case True then obtain i cntt cntf where ds:"ds = [DI i, cntt, cntf]" by auto

        have b_dom_d1: "\<forall>b'\<in>contours_in_d cntt. b' < Suc b" using "3.prems"(3) and ds by auto
        have b_dom_d2: "\<forall>b'\<in>contours_in_d cntf. b' < Suc b" using "3.prems"(3) and ds by auto
        have b_dom_ds: "\<forall>d' \<in> set []. \<forall>b'\<in>contours_in_d d'. b' < Suc b" by auto
        have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < Suc b" using "3.prems"(1) by auto

        show ?thesis proof(cases "i\<noteq>0")
        case True
          with ds "3.prems" DP If
          have "((lab, \<beta>), t) = ((cp1, [cp1 \<mapsto> b]), cntt)
              \<or> ((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, Suc b))"
          by simp
          thus ?thesis using assms
          proof
            assume "((lab, \<beta>), t) = ((cp1, [cp1 \<mapsto> b]), cntt)"
            hence "\<exists>b'. b' \<in> ran \<beta> \<and> b = b'" by auto
            thus ?thesis by blast
          next
            assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, Suc b))"
            with "3.hyps"(2) b_dom_d1 b_dom_ds b_dom_ve
            have "\<exists>b'. b' \<in> ran \<beta> \<and> Suc b \<le> b'" by blast
            thus ?thesis by auto
          qed
        next
        case False
          with ds "3.prems" DP If
          have "((lab, \<beta>), t) = ((cp2, [cp2 \<mapsto> b]), cntf)
              \<or> ((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntf, [], ve, Suc b))"
          by simp
          thus ?thesis using assms
          proof
            assume "((lab, \<beta>), t) = ((cp2, [cp2 \<mapsto> b]), cntf)"
            hence "\<exists>b'. b' \<in> ran \<beta> \<and> b = b'" by auto
            thus ?thesis by blast
          next
            assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntf, [], ve, Suc b))"
            with "3.hyps"(2) b_dom_d2 b_dom_ds b_dom_ve
            have "\<exists>b'. b' \<in> ran \<beta> \<and> Suc b \<le> b'" by blast
            thus ?thesis by auto
          qed
        qed
      next
        case False
        show ?thesis using "3.prems" DP If False
          by(simp split: list.split_asm d.split_asm)
      qed
    qed
  next
    case Stop
    thus ?thesis using "3.prems" 
      by (simp split: list.split_asm d.split_asm)
  qed
next
  case (3 ve b c \<beta>')
  show ?case
  proof (cases c)
  case (App lab' f vs)
    print_facts

    have prem2': "\<forall>b'\<in>ran \<beta>'. b' < Suc b" using "3.prems"(2) by auto
    have prem3': "\<forall>b'\<in>contours_in_ve ve. b' < Suc b" using "3.prems"(3) by auto
    note c_in_e = contours_in_eval[OF prem3' prem2']

    have b_dom_d: "\<forall>b'\<in>contours_in_d (evalV f \<beta>' ve). b' < Suc b" by(rule c_in_e)
    have b_dom_ds: "\<forall>d' \<in> set (map (\<lambda>v. evalV v \<beta>' ve) vs). \<forall>b'\<in>contours_in_d d'. b' < Suc b"
      using c_in_e by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < Suc b" by (rule prem3')
   
    have new_elem: "\<forall>y. ((lab', \<beta>'), y) \<notin> evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, Suc b))" 
    proof(rule allI, rule notI)
      fix y assume e: "((lab', \<beta>'), y) \<in> evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, Suc b))"
      from e b_dom_d b_dom_ve b_dom_ds
      have "\<exists>b'. b' \<in> ran \<beta>' \<and> Suc b \<le> b'" by(auto elim!:"3.hyps"(2))
      thus False using prem2' by auto
    qed
     
    from "3.hyps"(1)[OF b_dom_ve b_dom_d b_dom_ds]
    show ?thesis using App new_elem
      by(auto simp add:HOL.Let_def intro!:single_valued_insert)     
  next
  case (Let lab' ls c')
    have prem2': "\<forall>b'\<in>ran (\<beta>'(lab' \<mapsto> Suc b)). b' \<le> Suc b"
    proof
      fix b' assume "b'\<in>ran (\<beta>'(lab' \<mapsto> Suc b))"
      hence "b' \<in> ran \<beta>' \<or> b' = Suc b" by (auto dest:ran_upd[THEN subsetD])
      thus "b' \<le> Suc b" using  "3.prems"(2) by auto
    qed
    have prem3': "\<forall>b'\<in>contours_in_ve ve. b' \<le> Suc b" using "3.prems"(3) by auto

    note c_in_e = contours_in_eval[OF prem3' prem2']
    note c_in_ve' = contours_in_ve_upds_binds[OF prem3' prem2']

    have b_dom_ve: "\<forall>b' \<in> contours_in_ve (ve ++ map_of (map (\<lambda>(v,l). ((v,Suc b), evalV (L l) ((\<beta>'(lab' \<mapsto> Suc b))) ve)) ls)). b' \<le> Suc b"
      by (rule c_in_ve')
    have b_dom_beta: "\<forall>b'\<in>ran (\<beta>'(lab' \<mapsto> Suc b)). b' \<le> Suc b" by (rule prem2')
    have new: "Suc b \<in> ran (\<beta>'(lab' \<mapsto> Suc b))" by simp
      
    from "3.hyps"(3)[OF new b_dom_beta b_dom_ve]
    show ?thesis using Let
      by(auto simp add:HOL.Let_def simp del: fun_upd_apply)
  qed
next
  case (4 ve b c \<beta>' lab \<beta> t)
  show ?case
  proof (cases c)
  case (App lab' f vs)
    have prem2': "\<forall>b'\<in>ran \<beta>'. b' < Suc b" using "3.prems"(2) by auto
    have prem3': "\<forall>b'\<in>contours_in_ve ve. b' < Suc b" using "3.prems"(3) by auto
    note c_in_e = contours_in_eval[OF prem3' prem2']

    have b_dom_d: "\<forall>b'\<in>contours_in_d (evalV f \<beta>' ve). b' < Suc b" by(rule c_in_e)
    have b_dom_ds: "\<forall>d' \<in> set (map (\<lambda>v. evalV v \<beta>' ve) vs). \<forall>b'\<in>contours_in_d d'. b' < Suc b"
      using c_in_e by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < Suc b" by (rule prem3')

    from App "3.prems"(4)
    have "((lab, \<beta>), t)
         \<in> {((lab', \<beta>'), evalV f \<beta>' ve)}
         \<union> evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, Suc b))"
    by (simp add: HOL.Let_def)
    hence "((lab, \<beta>), t) = ((lab', \<beta>'), evalV f \<beta>' ve)
          \<or> ((lab, \<beta>), t) \<in> (evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, Suc b)))"
    by simp
    thus ?thesis proof
      assume "((lab, \<beta>), t) = ((lab', \<beta>'), evalV f \<beta>' ve)"
      hence "\<beta>' = \<beta>" by simp
      with "3.prems"(1)
      show ?thesis by auto
    next
      assume "((lab, \<beta>), t) \<in> (evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, Suc b)))"
      with "3.hyps"(2)[OF b_dom_ve b_dom_d b_dom_ds]
      have "\<exists>b'. b' \<in> ran \<beta> \<and> Suc b \<le> b'" by auto
      thus ?thesis by auto
    qed
  next
  case (Let lab' ls c)
    have prem2': "\<forall>b'\<in>ran (\<beta>'(lab' \<mapsto> Suc b)). b' \<le> Suc b"
    proof
      fix b' assume "b'\<in>ran (\<beta>'(lab' \<mapsto> Suc b))"
      hence "b' \<in> ran \<beta>' \<or> b' = Suc b" by (auto dest:ran_upd[THEN subsetD])
      thus "b' \<le> Suc b" using  "3.prems"(2) by auto
    qed
    have prem3': "\<forall>b'\<in>contours_in_ve ve. b' \<le> Suc b" using "3.prems"(3) by auto

    note c_in_e = contours_in_eval[OF prem3' prem2']
    note c_in_ve' = contours_in_ve_upds_binds[OF prem3' prem2']

    have b_dom_ve: "\<forall>b' \<in> contours_in_ve (ve ++ map_of (map (\<lambda>(v,l). ((v,Suc b), evalV (L l) ((\<beta>'(lab' \<mapsto> Suc b))) ve)) ls)). b' \<le> Suc b"
      by (rule c_in_ve')
    have b_dom_beta: "\<forall>b'\<in>ran (\<beta>'(lab' \<mapsto> Suc b)). b' \<le> Suc b" by (rule prem2')
    have new: "Suc b \<in> ran (\<beta>'(lab' \<mapsto> Suc b))" by simp

    from Let and "3.prems"(4)
    have "((lab, \<beta>), t)
         \<in> evalC\<cdot>(Discr (c, \<beta>'(lab' \<mapsto> Suc b),ve ++
                               map_of (map (\<lambda>(v, l). ((v, Suc b), evalV (L l) (\<beta>'(lab' \<mapsto> Suc b)) ve)) ls), Suc b))" by (simp add: HOL.Let_def)
    with "3.hyps"(4)[OF new b_dom_beta b_dom_ve]
    have "\<exists>b'. b' \<in> ran \<beta> \<and> Suc b \<le> b'"  by(auto simp add:HOL.Let_def simp del: fun_upd_apply)
    thus ?thesis by auto
  qed
}
qed
print_theorems (* Unselect-blocker *)

lemma "single_valued (evalCPS prog)"
unfolding evalCPS_def
by ((subst HOL.Let_def)+, rule cc_single_valued'[THEN conjunctionD1], auto)
end
