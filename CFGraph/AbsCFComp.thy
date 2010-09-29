theory AbsCFComp
imports AbsCF Computability FixTransform
begin

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