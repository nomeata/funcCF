theory AbsCFComp
imports AbsCF Computability FixTransform CPSUtils
begin

default_sort type

fixrec abs_g :: "('c::contour \<afstate> + 'c \<acstate>) discr \<rightarrow> 'c \<aans>"
  where "abs_g\<cdot>x = (case undiscr x of
              (Inl (PC (Lambda lab vs c, \<beta>), as, ve, b)) \<Rightarrow> {}
            | (Inl (PP (Plus c),[_,_,cnts],ve,b)) \<Rightarrow>
                     let b' = \<anb> b c;
                         \<beta>  = [c \<mapsto> b]
                     in {((c, \<beta>), cont) | cont . cont \<in> cnts}
            | (Inl (PP (prim.If ct cf),[_, cntts, cntfs],ve,b)) \<Rightarrow>
                  ((   let b' = \<anb> b ct;
                            \<beta> = [ct \<mapsto> b]
                        in {((ct, \<beta>), cnt) | cnt . cnt \<in> cntts}
                   )\<union>(
                       let b' = \<anb> b cf;
                            \<beta> = [cf \<mapsto> b]
                        in {((cf, \<beta>), cnt) | cnt . cnt \<in> cntfs}
                   ))
            | (Inl (AStop,[_],_,_)) \<Rightarrow> {}
            | (Inl _) \<Rightarrow> \<bottom>
            | (Inr (App lab f vs,\<beta>,ve,b)) \<Rightarrow>
                 let fs = \<aA> f \<beta> ve;
                     as = map (\<lambda>v. \<aA> v \<beta> ve) vs;
                     b' = \<anb> b lab
                  in {((lab, \<beta>),f') | f' . f'\<in> fs}
            | (Inr (Let lab ls c',\<beta>,ve,b)) \<Rightarrow> {}
        )"

fixrec abs_R :: "('c::contour \<afstate> + 'c \<acstate>) discr \<rightarrow> ('c::contour \<afstate> + 'c \<acstate>) discr set"
  where "abs_R\<cdot>x = (case undiscr x of
              (Inl (PC (Lambda lab vs c, \<beta>), as, ve, b)) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = ve \<union>. (\<Union>. (map (\<lambda>(v,a). {(v,b) := a}.) (zip vs as)))
                     in {Discr (Inr (c,\<beta>',ve',b))}
                else \<bottom>)
            | (Inl (PP (Plus c),[_,_,cnts],ve,b)) \<Rightarrow>
                     let b' = \<anb> b c;
                         \<beta>  = [c \<mapsto> b]
                     in (\<Union>cnt\<in>cnts. {Discr (Inl (cnt,[{}],ve,b'))})
            | (Inl (PP (prim.If ct cf),[_, cntts, cntfs],ve,b)) \<Rightarrow>
                  ((   let b' = \<anb> b ct;
                            \<beta> = [ct \<mapsto> b]
                        in (\<Union>cnt\<in>cntts . {Discr (Inl (cnt,[],ve,b'))})
                   )\<union>(
                       let b' = \<anb> b cf;
                            \<beta> = [cf \<mapsto> b]
                        in (\<Union>cnt\<in>cntfs . {Discr (Inl (cnt,[],ve,b'))})
                   ))
            | (Inl (AStop,[_],_,_)) \<Rightarrow> {}
            | (Inl _) \<Rightarrow> \<bottom>
            | (Inr (App lab f vs,\<beta>,ve,b)) \<Rightarrow>
                 let fs = \<aA> f \<beta> ve;
                     as = map (\<lambda>v. \<aA> v \<beta> ve) vs;
                     b' = \<anb> b lab
                  in (\<Union>f' \<in> fs. {Discr (Inl (f',as,ve,b'))})
            | (Inr (Let lab ls c',\<beta>,ve,b)) \<Rightarrow>
                 let b' = \<anb> b lab;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                     ve' = ve \<union>. (\<Union>. (map (\<lambda>(v,l). {(v,b') := (\<aA> (L l) \<beta>' ve)}.) ls))
                 in {Discr (Inr (c',\<beta>',ve',b'))}
        )"

definition maps_over :: "'a::type set \<Rightarrow> 'b::type set \<Rightarrow> ('a \<rightharpoonup> 'b) set"
  where "maps_over A B = {m. dom m \<subseteq> A \<and> ran m \<subseteq> B}"

lemma maps_over_empty[simp]:
  "empty \<in> maps_over A B"
unfolding maps_over_def by simp

lemma maps_over_upd:
  assumes "m \<in> maps_over A B"
  and "v \<in> A" and "k \<in> B"
shows "m(v \<mapsto> k) \<in> maps_over A B"
  using assms unfolding maps_over_def
  by (auto dest: subsetD[OF ran_upd])

lemma maps_over_finite[intro]:
  assumes "finite A" and "finite B" shows "finite (maps_over A B)"
proof-
  have inj_map_graph: "inj (\<lambda>f. {(x, y). Some y = f x})"
  proof (induct rule: inj_onI)
    case (1 x y)
    from "1.hyps"(3) have hyp: "\<And> a b. (Some b = x a) \<longleftrightarrow> (Some b = y a)"
      by (simp add:expand_set_eq)
    show ?case
    proof (rule ext)
    fix z show "x z = y z"
      using hyp[of _ z]
      by (cases "x z", cases "y z", auto)
    qed
  qed

  have "(\<lambda>f. {(x, y). Some y = f x}) ` maps_over A B \<subseteq> Pow( A \<times> B )" (is "?graph \<subseteq> _")
    unfolding maps_over_def
    by (auto dest!:subsetD[of _ A] subsetD[of _ B] intro:ranI)
  moreover
  have "finite (Pow( A \<times> B ))" using assms by auto
  ultimately
  have "finite ?graph" by (rule finite_subset)
  thus ?thesis
    by (rule finite_imageD[OF _ subset_inj_on[OF inj_map_graph subset_UNIV]])
qed

definition smaps_over :: "'a::type set \<Rightarrow> 'b::type set \<Rightarrow> ('a \<Rightarrow> 'b set) set"
  where "smaps_over A B = {m. sdom m \<subseteq> A \<and> sran m \<subseteq> B}"

lemma smaps_over_empty[simp]:
  "{}. \<in> smaps_over A B"
unfolding smaps_over_def by simp

lemma smaps_over_singleton:
  assumes "k \<in> A" and "vs \<subseteq> B"
shows "{k := vs}. \<in> smaps_over A B"
  using assms unfolding smaps_over_def
  by(auto dest: subsetD[OF sdom_singleton])

lemma smaps_over_un:
  assumes "m1 \<in> smaps_over A B" and "m2 \<in> smaps_over A B"
  shows "m1 \<union>. m2 \<in> smaps_over A B"
using assms unfolding smaps_over_def
by (auto simp add:smap_union_def)

lemma smaps_over_Union:
  assumes "set ms \<subseteq> smaps_over A B"
  shows "\<Union>.ms \<in> smaps_over A B"
using assms
by (induct ms)(auto intro: smaps_over_un)

lemma smaps_over_im:
 "\<lbrakk> f \<in> m a ; m \<in> smaps_over A B \<rbrakk> \<Longrightarrow> f \<in> B"
unfolding smaps_over_def by (auto simp add:sran_def)

lemma smaps_over_finite[intro]: 
  assumes "finite A" and "finite B" shows "finite (smaps_over A B)"
proof-
  have inj_smap_graph: "inj (\<lambda>f. {(x, y). y = f x \<and> y \<noteq> {}})" (is "inj ?gr")
  proof (induct rule: inj_onI)
    case (1 x y)
    from "1.hyps"(3) have hyp: "\<And> a b. (b = x a \<and> b \<noteq> {}) = (b = y a \<and> b \<noteq> {})"
      by -(subst (asm) (3) expand_set_eq, simp)
    show ?case
    proof (rule ext)
    fix z show "x z = y z"
      using hyp[of _ z]
      by (cases "x z \<noteq> {}", cases "y z \<noteq> {}", auto)
    qed
  qed

  have "?gr ` smaps_over A B \<subseteq> Pow( A \<times> Pow  B )" (is "?graph \<subseteq> _")
    unfolding smaps_over_def
    by (auto dest!:subsetD[of _ A] subsetD[of _ "Pow B"] sdom_not_mem intro:sranI)
  moreover
  have "finite (Pow( A \<times> Pow B ))" using assms by auto
  ultimately
  have "finite ?graph" by (rule finite_subset)
  thus ?thesis
    by (rule finite_imageD[OF _ subset_inj_on[OF inj_smap_graph subset_UNIV]])
qed

definition proc_poss :: "prog \<Rightarrow> 'c::contour proc set"
  where "proc_poss p = PC ` (lambdas p \<times> maps_over (labels p) UNIV) \<union> PP ` prims p \<union> {AStop}"

definition fstate_poss :: "prog \<Rightarrow> 'c::contour a_fstate set"
  where "fstate_poss p = (proc_poss p \<times> NList (Pow (proc_poss p)) (call_list_lengths p) \<times> smaps_over (vars p \<times> UNIV) (proc_poss p) \<times> UNIV)"

definition cstate_poss :: "prog \<Rightarrow> 'c::contour a_cstate set"
  where "cstate_poss p = (calls p \<times> maps_over (labels p) UNIV \<times> smaps_over (vars p \<times> UNIV) (proc_poss p) \<times> UNIV)"

definition arg_poss :: "prog \<Rightarrow> ('c::contour a_fstate + 'c a_cstate) discr set"
  where "arg_poss p = Discr ` (fstate_poss p <+> cstate_poss p)"

lemma finite_arg_space: "finite (arg_poss p)"
  unfolding arg_poss_def and cstate_poss_def and fstate_poss_def and proc_poss_def
  by (auto intro!: finite_cartesian_product finite_imageI maps_over_finite smaps_over_finite contour_finite finite_Nlist)

lemma adm_subset: "cont (\<lambda>x. f x) \<Longrightarrow>  adm (\<lambda>x. f x \<subseteq> S)"
by (subst sqsubset_is_subset[THEN sym], intro adm_lemmas cont2cont)

lemma evalV_possible:
  assumes f: "f \<in> \<aA> d \<beta> ve"
  and d: "d \<in> vals p"
  and ve: "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
  and \<beta>: "\<beta> \<in> maps_over (labels p) UNIV"
shows "f \<in> proc_poss p"
proof (cases "(d,\<beta>,ve)" rule: evalV_a.cases)
case (1 cl \<beta>' ve')
  thus ?thesis using f by auto next
case (2 prim \<beta>' ve')
  thus ?thesis using d f
    by (auto dest: vals1 simp add:proc_poss_def)
next
case (3 l var \<beta>' ve') 
  thus ?thesis using f d smaps_over_im[OF _ ve]
  by (auto split:option.split_asm dest: vals2)
next
case (4 l \<beta> ve)
  thus ?thesis using f d \<beta>
  by (auto dest!: vals3 simp add:proc_poss_def)
qed


lemma arg_space_complete:
  "state \<in> arg_poss p \<Longrightarrow> abs_R\<cdot>state \<subseteq> arg_poss p"
proof(induct rule: abs_R.induct[case_names Admissibility Bot Step])
case Admissibility show ?case
   by (intro adm_lemmas adm_subset cont2cont)
next
case Bot show ?case by simp next
case (Step abs_R) 
  note state = Step(2)
  show ?case
  proof (cases state)
  case (Discr state') show ?thesis
   proof (cases state')
     case (Inl fstate) show ?thesis
     using Inl Discr state
     proof (cases fstate rule:a_fstate_case)
     apply_end(auto)
     (* Lambda *)
     fix l vs c \<beta> as ve b
     assume "Discr (Inl (PC (Lambda l vs c, \<beta>), as, ve, b)) \<in> arg_poss p"
       hence lam: "Lambda l vs c \<in> lambdas p"
       and  beta: "\<beta> \<in> maps_over (labels p) UNIV "
       and  ve: "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
       and  as: "as \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       unfolding arg_poss_def fstate_poss_def proc_poss_def by auto

     from lam have "c \<in> calls p"
       by (rule lambdas1)

     moreover
     from lam have "l \<in> labels p"
       by (rule lambdas2)
     with beta have "\<beta>(l \<mapsto> b) \<in> maps_over (labels p) UNIV"
       by (rule maps_over_upd, auto)

     moreover
     from lam have vs: "set vs \<subseteq> vars p" by (rule lambdas3)
     from as have "\<forall> x \<in> set as. x \<in> Pow (proc_poss p)"
        unfolding NList_def nList_def by auto
     with vs have "ve \<union>. \<Union>.map (\<lambda>(v, y). { (v, b) := y}.) (zip vs as)
       \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)" (is "?ve' \<in> _")
       by (auto intro!: smaps_over_un[OF ve] smaps_over_Union smaps_over_singleton)
          (auto simp add:set_zip)

     ultimately
     have "(c, \<beta>(l \<mapsto> b), ?ve', b) \<in> cstate_poss p" (is "?cstate \<in> _")
       unfolding cstate_poss_def by simp
     thus "Discr (Inr ?cstate) \<in> arg_poss p"
       unfolding arg_poss_def by auto
     next

     (* Plus *)
     fix ve b l v1 v2 cnts cnt
     assume "Discr (Inl (PP (prim.Plus l), [v1, v2, cnts], ve, b)) \<in> arg_poss p"
         and "cnt \<in> cnts"
     hence "cnt \<in> proc_poss p" 
         and "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
       unfolding arg_poss_def fstate_poss_def NList_def nList_def
       by auto
     moreover
     have "[{}] \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       unfolding call_list_lengths_def NList_def nList_def by auto
     ultimately
     have "(cnt, [{}], ve, \<anb> b l) \<in> fstate_poss p"
       unfolding fstate_poss_def by auto
     thus "Discr (Inl (cnt, [{}], ve, \<anb> b l)) \<in> arg_poss p"
       unfolding arg_poss_def by auto
     next
  
     (* If True *)
     fix ve b l1 l2 v cntst cntsf cnt
     assume "Discr (Inl (PP (prim.If l1 l2), [v, cntst, cntsf], ve, b)) \<in> arg_poss p"
         and "cnt \<in> cntst"
     hence "cnt \<in> proc_poss p"
         and "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
       unfolding arg_poss_def fstate_poss_def NList_def nList_def
       by auto
     moreover
     have "[] \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       unfolding call_list_lengths_def NList_def nList_def by auto
     ultimately
     have "(cnt, [], ve, \<anb> b l1) \<in> fstate_poss p"
       unfolding fstate_poss_def by auto
     thus "Discr (Inl (cnt, [], ve, \<anb> b l1)) \<in> arg_poss p"
       unfolding arg_poss_def by auto
     next
  
     (* If False *)
     fix ve b l1 l2 v cntst cntsf cnt
     assume "Discr (Inl (PP (prim.If l1 l2), [v, cntst, cntsf], ve, b)) \<in> arg_poss p"
         and "cnt \<in> cntsf"
     hence "cnt \<in> proc_poss p"
         and "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
       unfolding arg_poss_def fstate_poss_def NList_def nList_def
       by auto
     moreover
     have "[] \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       unfolding call_list_lengths_def NList_def nList_def by auto
     ultimately
     have "(cnt, [], ve, \<anb> b l2) \<in> fstate_poss p"
       unfolding fstate_poss_def by auto
     thus "Discr (Inl (cnt, [], ve, \<anb> b l2)) \<in> arg_poss p"
       unfolding arg_poss_def by auto
    qed
  next
  case (Inr cstate)
  show ?thesis proof(cases cstate rule: prod_cases4)
   case (fields c \<beta> ve b)
   show ?thesis using Discr Inr fields state proof(cases c, auto simp add:HOL.Let_def simp del:evalV_a.simps)
     (* App *)
     fix l d ds f
     assume arg: "Discr (Inr (App l d ds, \<beta>, ve, b)) \<in> arg_poss p"
       and f: "f \<in> \<aA> d \<beta> ve"
     hence c: "App l d ds \<in> calls p"
       and d: "d \<in> vals p"
       and ds: "set ds \<subseteq> vals p"
       and beta: "\<beta> \<in> maps_over (labels p) UNIV"
       and ve: "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
     by (auto simp add: arg_poss_def cstate_poss_def call_list_lengths_def dest: app1 app2)

     have len: "length ds \<in> call_list_lengths p"
       by (auto intro: rev_image_eqI[OF c] simp add: call_list_lengths_def)

     have "f \<in> proc_poss p"
       using f d ve beta by (rule evalV_possible)
     moreover
     have "map (\<lambda>v. \<aA> v \<beta> ve) ds \<in> NList (Pow (proc_poss p)) (call_list_lengths p)"
       using ds len
       unfolding NList_def by (auto simp add:nList_def intro!: evalV_possible[OF _ _ ve beta])
     ultimately 
     have "(f, map (\<lambda>v. \<aA> v \<beta> ve) ds, ve, \<anb> b l) \<in> fstate_poss p" (is "?fstate \<in> _")
       using ve 
       unfolding fstate_poss_def by simp
     thus "Discr (Inl ?fstate) \<in> arg_poss p"
       unfolding arg_poss_def by auto

   next
     (* Let *)
     fix l binds c'
     assume arg: "Discr (Inr (Let l binds c', \<beta>, ve, b)) \<in> arg_poss p"
     hence l: "l \<in> labels p"
       and c': "c' \<in> calls p"
       and vars: "fst ` set binds \<subseteq> vars p"
       and ls: "snd ` set binds \<subseteq> lambdas p"
       and beta: "\<beta> \<in> maps_over (labels p) UNIV"
       and ve: "ve \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)"
     by (auto simp add: arg_poss_def cstate_poss_def call_list_lengths_def
              dest:let1 let2 let3 let4)

     have beta': "\<beta>(l \<mapsto> \<anb> b l) \<in> maps_over (labels p) UNIV" (is "?\<beta>' \<in> _")
       by (auto intro: maps_over_upd[OF beta l])

     moreover
     have "ve \<union>. \<Union>.map (\<lambda>(v, lam). { (v, \<anb> b l) := \<aA> (L lam) (\<beta>(l \<mapsto> \<anb> b l)) ve }.)
                binds
       \<in> smaps_over (vars p \<times> UNIV) (proc_poss p)" (is "?ve' \<in> _")
       using vars ls beta'
       by (auto intro!: smaps_over_un[OF ve] smaps_over_Union)
          (auto intro!:smaps_over_singleton simp add: proc_poss_def)

     ultimately
     have "(c', ?\<beta>', ?ve', \<anb> b l) \<in> cstate_poss p" (is "?cstate \<in> _")
     using c' unfolding cstate_poss_def by simp
     thus "Discr (Inr ?cstate) \<in> arg_poss p"
       unfolding arg_poss_def by auto
   qed
 qed
qed
qed
qed

lemma UN_iterate_less: 
  assumes start: "x \<in> S"
  and step: "\<And>y. y\<subseteq>S \<Longrightarrow> (f\<cdot>y) \<subseteq> S"
  shows "(\<Union>i. iterate i\<cdot>f\<cdot>{x}) \<subseteq> S"
proof- {
  fix i
  have "iterate i\<cdot>f\<cdot>{x} \<subseteq> S"
  proof(induct i)
    case 0 show ?case using `x \<in> S` by simp next
    case (Suc i) thus ?case using step[of "iterate i\<cdot>f\<cdot>{x}"] by simp
  qed
  } thus ?thesis by auto
qed

lemma arg_space_complete_ps: "states \<subseteq> arg_poss p \<Longrightarrow> (\<^ps> abs_R)\<cdot>states \<subseteq> arg_poss p"
using arg_space_complete unfolding powerset_lift_def by auto

lemma args_finite: "finite (\<Union>i. iterate i\<cdot>(\<^ps> abs_R)\<cdot>{Discr (Inl
     (contents (\<aA> (L p) empty {}.), [{AStop}], {}., \<abinit>))})" (is "finite ?S")
proof (rule finite_subset[OF _finite_arg_space])
  have [simp]:"p \<in> lambdas p" by (cases p, simp)
  show "?S \<subseteq> arg_poss p"
  by  (rule UN_iterate_less[OF _ arg_space_complete_ps])
      (auto simp add:arg_poss_def fstate_poss_def proc_poss_def call_list_lengths_def NList_def nList_def
         intro!: imageI)
qed

lemma Un_commute_helper:"(a \<union> b) \<union> (c \<union> d) = (a \<union> c) \<union> (b \<union> d)"
by auto

lemma a_evalF_decomp:
  "\<aF> = fst (sum_to_tup\<cdot>(fix\<cdot>(\<Lambda> f x. (\<Union>y\<in>abs_R\<cdot>x. f\<cdot>y) \<union> abs_g\<cdot>x)))"
apply (subst a_evalF_def)
apply (subst fix_transform_pair_sum)
apply (rule arg_cong [of _ _ "\<lambda>x. fst (sum_to_tup\<cdot>(fix\<cdot>x))"])
apply (simp)
apply (simp only: discr_app undiscr_Discr)
apply (rule ext_cfun, rule ext_cfun, simp)
apply (case_tac xa, case_tac a, simp)
apply (case_tac aa rule:a_fstate_case, simp_all add: Un_commute_helper)

apply (case_tac b rule:prod_cases4)
apply (case_tac aa)
apply (simp_all add:HOL.Let_def)
done

lemma a_evalF_iterative:
  "\<aF>\<cdot>(Discr x) = \<^ps> abs_g\<cdot>(\<Union>i. iterate i\<cdot>(\<^ps> abs_R)\<cdot>{Discr (Inl x)})"
by (simp del:abs_R.simps abs_g.simps add: theorem12 Un_commute a_evalF_decomp)

lemma a_evalCPS_interative:
"\<aPR> x = \<^ps> abs_g\<cdot>(\<Union>i. iterate i\<cdot>(\<^ps> abs_R)\<cdot>{Discr (Inl
     (contents (\<aA> (L x) empty {}.), [{AStop}], {}., \<abinit>))})"
unfolding evalCPS_a_def
by(subst a_evalF_iterative, simp del:abs_R.simps abs_g.simps evalV_a.simps)

end