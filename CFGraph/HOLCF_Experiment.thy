theory HOLCF_Experiment imports HOLCFUtils
begin

fixrec
  f :: "nat \<rightarrow> nat set"
where
  [simp del]: "f\<cdot>b = {b} \<union> f\<cdot>b"

lemma "f\<cdot>b = {b}"
apply (subst f.simps)
apply (rule f.induct)
apply (rule adm_eq, simp, simp)
apply (simp add: subset_eq Ball_def mem_def bottom_eq_False)
apply simp
done

lemma "cont (\<lambda>x. x\<cdot>(Discr True))"
by (intro cont2cont)

thm Let_def

lemma "cont (\<lambda>x. let y = True in x\<cdot>(Discr y))"
by (intro cont2cont)

end
