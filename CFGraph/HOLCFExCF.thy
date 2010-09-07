theory HOLCFEval
  imports CPSUtils HOLCF HOLCFUtils HOLCFList HOLCFOption CPSScheme
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
              Some l \<Rightarrow> (case ve (var,l) of Some d \<Rightarrow> d))"
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

value call_case
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

find_theorems name: ".induct"

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

lemma single_valued_empty[simp]:"single_valued {}"
by (rule single_valuedI) auto

(*
lemma "\<lbrakk> ((lab,\<beta>),t) \<in> evalF\<cdot>(Discr (d,ds,ve, b)); Some b' \<in> range \<beta> \<rbrakk> \<Longrightarrow> b \<le> b'"
  and "\<lbrakk> ((lab,\<beta>),t) \<in> evalC\<cdot>(Discr (c,\<beta>',ve,b)); Some b' \<in> range \<beta> \<rbrakk> \<Longrightarrow> b < b'"
proof(induct arbitrary:d ds ve b \<beta> c \<beta>' lab b' t rule:evalF_evalC.induct)
print_cases
case 1 show ?case
  (* admissibility *)
  by (intro adm_lemmas adm_prod_split adm_not_conj adm_not_mem cont2cont)
next
  case 2 case 1 thus ?case
  by (auto simp add:mem_def)
next
  case 2 case 2 thus ?case
  by (auto simp add:mem_def)
next
  case (3 evalF evalC)
  print_cases
  case (1 d ds ve b \<beta> lab b' t)
  show ?case
  proof (cases d)
  print_cases
    case (DI i)
    thus ?thesis using "3.prems" by simp
    next 
    case (DC closure)
    show ?thesis
    proof (cases closure)
    case (Pair lambda cnt)
      show ?thesis
      proof (cases lambda)
      case (Lambda lab' as c)
        (* from "3.prems" Lambda Pair DC  *)
        have "length as = length ds"
        proof(rule ccontr)
          assume "length as \<noteq> length ds"
          with "3.prems" Lambda Pair DC show False by simp
        qed
        with "3.prems" Lambda Pair DC
        have "((lab, \<beta>), t)
         \<in> evalC\<cdot>(Discr (c, cnt(lab' \<mapsto> b), ve(map (\<lambda>v. (v, b)) as [\<mapsto>] ds), b))"
          by simp
        with "3.hyps"(2) "3.prems"(2)
        have "b < b'" by auto
        thus ?thesis by auto
      qed
    qed
  next
  case (DP prim)
    show ?thesis
    proof (cases prim)
      case (Plus cp)
      show ?thesis
      proof (cases "\<exists> i1 i2 cnt. ds = [DI i1, DI i2, cnt]")
        case True then obtain i1 i2 cnt where "ds = [DI i1, DI i2, cnt]" by auto
        with "3.prems" DP Plus 
        have "((lab, \<beta>), t) = ((cp, [cp \<mapsto> b]), cnt)
            \<or> ((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, Suc b))"
        by (simp)
        thus ?thesis using assms
        proof
          assume "((lab, \<beta>), t) = ((cp, [cp \<mapsto> b]), cnt)"
          with "3.prems"(2)
          have "b' = b" by auto
          thus ?thesis by simp
        next
          assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, Suc b))"
          with "3.prems"(2) "3.hyps"(1)
          have "Suc b \<le> b'" by auto
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
        show ?thesis proof(cases "i\<noteq>0")
        case True
          with ds "3.prems" DP If
          have "((lab, \<beta>), t) = ((cp1, [cp1 \<mapsto> b]), cntt)
              \<or> ((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, Suc b))"
          by simp
          thus ?thesis using assms
          proof
            assume "((lab, \<beta>), t) = ((cp1, [cp1 \<mapsto> b]), cntt)"
            with "3.prems"(2)
            have "b' = b" by auto
            thus ?thesis by simp
          next
            assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, Suc b))"
            with "3.prems"(2) "3.hyps"(1)
            have "Suc b \<le> b'" by auto
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
            with "3.prems"(2)
            have "b' = b" by auto
            thus ?thesis by simp
          next
            assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntf, [], ve, Suc b))"
            with "3.prems"(2) "3.hyps"(1)
            have "Suc b \<le> b'" by auto
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
  case (3 evalF evalC)
  case (2 ve b \<beta> c \<beta>' lab b' t)
  show ?case
  proof (cases c)
  case (App lab' f vs)
    with "3.prems"
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
      print_facts
*)

lemma  "single_valued (evalF\<cdot>fstate)"
   and "single_valued (evalC\<cdot>cstate)"
proof(induct rule:eval_induct)
print_cases
  case 1 show ?case by (auto intro: adm_single_valued)
next
  case 2 show ?case by (auto intro: adm_single_valued)
next
  case 3 show ?case by simp
next
  case 4 show ?case by simp
next
  case (5 evalC lab vs c \<beta> as ve b) thus ?case by auto
next
  case (6 evalF c a1 a2 cnt ve b) thus ?case
  apply auto


lemma  "single_valued (evalF\<cdot>fstate)"
   and "single_valued (evalC\<cdot>cstate)"
unfolding evalCPS_def
proof(induct arbitrary:fstate cstate rule:evalF_evalC.induct)
print_cases
  case 1 (*Admissibility*)
  show ?case
  by (intro adm_prod_split adm_conj adm_all adm_single_valued cont2cont)
next
  case 2 (* True for bottom *)
  {
    print_cases
    case 1
    show ?case by (auto simp add: empty_def)
    next
    case 2
    show ?case by (auto simp add: empty_def)
  }
  next 
  case (3 evalF evalC)
  { 
    case (1 fstate)
    show ?case
    (* Now I need something about b *)


  unfolding single_valued



  apply(rule adm_subst)
  apply simp

  apply (auto intro:single_valuedI)




end
