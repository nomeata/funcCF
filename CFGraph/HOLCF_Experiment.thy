theory HOLCF_Experiment imports HOLCF
begin

lemma "cont (\<lambda>f. f)" by (rule cont_id)

lemma  [simp, cont2cont]: "cont f \<Longrightarrow> cont (\<lambda>x. (f x) (a := ONE))"
unfolding fun_upd_def
apply (rule cont2cont_lambda)
apply (case_tac "y=a")
apply auto
apply (rule cont2cont_fun)
apply simp
done

(* Still does not work:
fixrec f :: "int \<Rightarrow> int \<Rightarrow> one" where
  "f = (\<lambda>b. (f b) (b := ONE))"
*)

 print_theorems

(* lemma "cont (\<lambda>f. f (x := ONE))" *)

thm prod_case_def

lemma cont_prod_case [simp, cont2cont]:
  "[|\<And> a b. cont (f a b)|] ==> cont (\<lambda>x. prod_case (\<lambda>a b. f a b x) p)"
unfolding prod_case_unfold
by (induct p) simp_all

fixrec g :: "(int\<times>int) discr \<rightarrow> (int \<Rightarrow> one)" where
  "g\<cdot>b = (case undiscr b of (a,c) \<Rightarrow> (g\<cdot>(Discr (c,c))) (a := ONE))"

print_theorems
declare f.simps[simp del]


thm f.induct(1)[no_vars]

lemma "f\<cdot>(Discr b) = (\<lambda> c. if b = c then ONE else \<bottom>)"
apply (rule ext)
apply auto
apply (subst f.unfold)
apply simp
apply(induct rule:f.induct)
apply auto
done

end
