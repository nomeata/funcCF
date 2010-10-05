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

definition prim_poss :: "prog \<Rightarrow> prim set"
  where "prim_poss p = (Plus ` labels p \<union> { prim.If p1 p1 | p1 p2 .  p1 \<in> labels p \<and> p2 \<in> labels p})"

definition proc_poss :: "prog \<Rightarrow> 'c::contour proc set"
  where "proc_poss p = PC ` (lambdas p \<times> maps_over (labels p) UNIV) \<union> PP ` prim_poss p \<union> {AStop}"

definition fstate_poss :: "prog \<Rightarrow> 'c::contour a_fstate set"
  where "fstate_poss p = (proc_poss p \<times> NList (Pow (proc_poss p)) (call_list_lengths p) \<times> smaps_over (vars p \<times> UNIV) (proc_poss p) \<times> UNIV)"

definition cstate_poss :: "prog \<Rightarrow> 'c::contour a_cstate set"
  where "cstate_poss p = (calls p \<times> maps_over (labels p) UNIV \<times> smaps_over (vars p \<times> UNIV) (proc_poss p) \<times> UNIV)"

definition arg_poss :: "prog \<Rightarrow> ('c::contour a_fstate + 'c a_cstate) set"
  where "arg_poss p = fstate_poss p <+> cstate_poss p"

lemma finite_arg_space: "finite (arg_poss p)"
  unfolding prim_poss_def and arg_poss_def and cstate_poss_def and fstate_poss_def and proc_poss_def
  by (auto intro!: finite_cartesian_product finite_imageI maps_over_finite smaps_over_finite contour_finite finite_Nlist)

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