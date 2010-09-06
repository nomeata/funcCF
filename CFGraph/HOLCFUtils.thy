theory HOLCFUtils
imports HOLCF
begin

instantiation bool :: finite_po
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> (x \<longrightarrow> y)"

instance
by (default, unfold below_bool_def, fast+)

end

instance bool :: pcpo
proof
  have "\<forall>y. False \<sqsubseteq> y" by (simp add: below_bool_def)
  thus "\<exists>x::bool. \<forall>y. x \<sqsubseteq> y" ..
qed

lemma bottom_eq_False[simp]: "\<bottom> = False"
apply (rule below_antisym [OF minimal])
apply (simp add: below_bool_def)
done

lemma cont2cont_disj [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)" and g: "cont (\<lambda>x. g x)"
  shows "cont (\<lambda>x. f x \<or> g x)"
apply (rule cont_apply [OF f])
apply (rule chfindom_monofun2cont)
apply (rule monofunI, simp add: below_bool_def)
apply (rule cont_compose [OF _ g])
apply (rule chfindom_monofun2cont)
apply (rule monofunI, simp add: below_bool_def)
done

lemma cont2cont_Collect [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont (\<lambda>x. {y. f x y})"
unfolding Collect_def using assms
by (rule cont2cont_lambda)

lemma cont2cont_mem [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)"
  shows "cont (\<lambda>x. y \<in> f x)"
unfolding mem_def using assms
by (rule cont2cont_fun)

lemma cont2cont_union [simp, cont2cont]:
  "cont (\<lambda>x. f x) \<Longrightarrow> cont (\<lambda>x. g x)
\<Longrightarrow> cont (\<lambda>x. f x \<union> g x)"
unfolding Un_def by simp

lemma cont2cont_insert [simp, cont2cont]:
  assumes "cont (\<lambda>x. f x)"
  shows "cont (\<lambda>x. insert y (f x))"
unfolding insert_def using assms
by (intro cont2cont)

instantiation nat :: discrete_cpo
begin

definition
  [simp]: "(x::nat) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance
by default simp

end

instantiation int :: discrete_cpo
begin

definition
  [simp]: "(x::int) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance
by default simp

end


lemma cont2cont_Let_simple[simp,cont2cont]:
  assumes "cont (\<lambda>x. g x t)"
  shows "cont (\<lambda>x. let y = t in g x y)"
unfolding Let_def using assms .


lemma cont2cont_list_case [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x)"
     and  "\<And>y z. cont (\<lambda>x. f2 x y z)"
  shows "cont (\<lambda>x. list_case (f1 x) (f2 x) l)"
using assms
by (cases l) auto

lemma cont2cont_prod_case [simp, cont2cont]:
  assumes "\<And>y z. cont (\<lambda>x. f x y z)"
  shows "cont (\<lambda>x. prod_case (f x) p)"
using assms
by (cases p) auto


text {* Some rules about admissibility *}

lemma adm_not_mem:
  assumes "cont (\<lambda>x. f x)"
  shows "adm (\<lambda>x. y \<notin> f x)"
using assms
apply (erule_tac t = f in adm_subst)
proof (rule admI)
fix Y :: "nat \<Rightarrow> 'b \<Rightarrow> bool"
assume chain: "chain Y"
assume "\<forall>i. y \<notin> Y i" hence  "(\<Squnion> i. Y i y) = False" unfolding mem_def by auto
thus "y \<notin> (\<Squnion> i. Y i)" using chain unfolding mem_def by (subst thelub_fun) auto
qed

lemma adm_id[simp]: "adm (\<lambda>x . x)"
proof(rule admI)
fix Y :: "nat \<Rightarrow> bool"
assume "\<forall>i. Y i" hence "Y = (\<lambda>i. True)" by -(rule ext, auto)
hence "range Y <<| True" by simp (rule lub_const)
hence "lub (range Y) = True" by (rule thelubI)
thus "\<Squnion> i. Y i" by simp
qed

lemma adm_Not[simp]: "adm Not"
proof(rule admI)
fix Y :: "nat \<Rightarrow> bool"
assume "\<forall>i. \<not> Y i" hence "Y = (\<lambda>i. False)" by -(rule ext, auto)
hence "range Y <<| False" by simp (rule lub_const)
hence "lub (range Y) = False" by (rule thelubI)
thus "\<not> (\<Squnion> i. Y i)" by simp
qed

lemma adm_prod_split:
  assumes "adm (\<lambda>p. f (fst p) (snd p))"
  shows "adm (\<lambda>(x,y). f x y)"
using assms unfolding split_def .


lemma adm_single_valued:
 assumes "cont (\<lambda>x. f x)"
 shows "adm (\<lambda>x. single_valued (f x))"
using assms
apply (erule_tac t = f in adm_subst)
unfolding single_valued_def
by (intro adm_lemmas adm_not_mem cont2cont)

lemma const_False_is_bot[simp]: "(\<lambda>a. False) = {}" 
by (rule ext, auto)

lemma bot_bool_is_emptyset[simp]: "\<bottom> = {}"
by (simp add:inst_fun_pcpo)

end