theory HOLCF_Experiment imports HOLCF
begin

fixrec f :: "int lift \<rightarrow> (int \<Rightarrow> one)" where
  "f\<cdot>b = (case b of \<bottom> \<Rightarrow> \<bottom> | Def a \<Rightarrow> (f\<cdot>b) (a := ONE))"
print_theorems
declare f.simps[simp del]

thm f.induct(1)[no_vars]

lemma "f\<cdot>(Def b) = (\<lambda> c. if b = c then ONE else \<bottom>)"
apply (rule ext)
apply auto
apply (subst f.unfold)
apply simp
apply(induct rule:f.induct)
apply auto
done

end
