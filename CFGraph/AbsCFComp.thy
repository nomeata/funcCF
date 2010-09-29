theory AbsCFComp
imports AbsCF Computability
begin

lemma cont2cont_split_pair[cont2cont,simp]:
 assumes f1: "cont f"
     and f2: "\<And> x. cont (f x)"
     and g1: "cont g"
     and g2: "\<And> x. cont (g x)"
 shows "cont (\<lambda>(a, b). (f a b, g a b))"
apply (intro cont2cont)
apply (rule cont_apply[OF cont_snd _ cont_const])
apply (rule cont_apply[OF cont_snd f2])
apply (rule cont_apply[OF cont_fst cont2cont_fun[OF f1] cont_const])

apply (rule cont_apply[OF cont_snd _ cont_const])
apply (rule cont_apply[OF cont_snd g2])
apply (rule cont_apply[OF cont_fst cont2cont_fun[OF g1] cont_const])
done

lemma from_to_discr_pair_oo[simp]:
 assumes f1: "cont f"
     and f2: "\<And> x. cont (f x)"
     and g1: "cont g"
     and g2: "\<And> x. cont (g x)"
  shows "(from_discr_pair oo (\<Lambda> p. (\<lambda>(a,b). (f a b, g a b)) p) oo to_discr_pair)
   = (\<Lambda> p . (\<lambda>(a,b) . (from_discr\<cdot>(f (to_discr\<cdot>a) (to_discr\<cdot>b)),
                       from_discr\<cdot>(g (to_discr\<cdot>a) (to_discr\<cdot>b)))) p)"
apply (rule ext_cfun)
apply (case_tac x)
apply (auto simp add:cont2cont_split_pair[OF f1 f2 g1 g2])
apply (subst beta_cfun)
apply (auto simp add:from_discr_pair_app to_discr_pair_app)

apply (rule cont2cont_split_pair)

apply (intro cont2cont cont2cont_lambda)
apply (rule cont2cont_fun)
apply (intro cont2cont cont_compose[OF f1])
apply (intro cont2cont cont_compose[OF f2])

apply (intro cont2cont cont2cont_lambda)
apply (rule cont2cont_fun)
apply (intro cont2cont cont_compose[OF g1])
apply (intro cont2cont cont_compose[OF g2])
done

lemma tup_sum_oo[simp]:
 assumes f1: "cont f"
     and f2: "\<And> x. cont (f x)"
     and g1: "cont g"
     and g2: "\<And> x. cont (g x)"
shows  "tup_to_sum oo (\<Lambda> p. (\<lambda>(a, b). (f a b, g a b)) p) oo sum_to_tup
  = (\<Lambda> x. sum_case (f (x \<circ> Inl) (x \<circ> Inr)) (g (x \<circ> Inl) (x \<circ> Inr)))"
apply (rule ext_cfun)
apply (simp add: sum_to_tup_app tup_to_sum_app cont2cont_split_pair[OF f1 f2 g1 g2])

apply (subst beta_cfun)

apply (rule cont2cont_lambda[OF cont2cont_sum_case])
apply (rule cont_apply[OF _ f2])
apply (intro cont2cont)
apply (rule cont2cont_fun[of "\<lambda>x. f (x \<circ> Inl)"])
apply (rule cont_apply[OF cont2cont_circ f1 cont_const])

apply (rule cont_apply[OF _ g2])
apply (intro cont2cont)
apply (rule cont2cont_fun[of "\<lambda>x. g (x \<circ> Inl)"])
apply (rule cont_apply[OF cont2cont_circ g1 cont_const])

apply (rule refl)
done

lemma fst_to_discr_pair[simp]:
  "fst (to_discr_pair\<cdot>x) = to_discr\<cdot>(fst x)"
by (cases x, simp add:to_discr_pair_def)

lemma fst_sum_to_tup[simp]:
  "fst (sum_to_tup\<cdot>x) = x \<circ> Inl"
by (simp add: sum_to_tup_app)

lemma "\<aF> = undefined"
apply (subst a_evalF_def)
apply (subst fix_transform_discr_pair)
apply (subst fix_transform_pair_sum)

apply (simp add:  from_discr_app)
apply (simp only: to_discr_app')

apply (subst tup_sum_oo)



end