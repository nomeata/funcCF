theory SetMap
  imports HOLCF HOLCFUtils
begin

definition smap_empty ("{}.")
 where "{}. k = {}"

definition smap_union :: "('a::type \<Rightarrow> 'b::type set)  \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)" ("_ \<union>. _")
 where "smap1 \<union>. smap2 k =  smap1 k \<union> smap2 k"

primrec smap_Union :: "('a::type \<Rightarrow> 'b::type set) list \<Rightarrow> 'a \<Rightarrow> 'b set" ("\<Union>._")
  where [simp]:"\<Union>. [] = {}."
      | "\<Union>. (m#ms) = m  \<union>. \<Union>. ms"

definition smap_singleton :: "'a::type \<Rightarrow> 'b::type set \<Rightarrow> 'a \<Rightarrow> 'b set" ("{ _ := _}.")
  where "{k := vs}. = {}. (k := vs)"

lemma smap_union_mono: "\<lbrakk> ve1 \<sqsubseteq> ve1'; ve2 \<sqsubseteq> ve2' \<rbrakk> \<Longrightarrow> ve1 \<union>. ve2 \<sqsubseteq> ve1' \<union>. ve2'"
  by (subst below_fun_def, subst (asm) (1 2) below_fun_def, auto simp add:sqsubset_is_subset smap_union_def)

lemma smap_Union_union: "m1 \<union>. \<Union>.ms = \<Union>.(m1#ms)"
  by (rule ext, auto simp add: smap_union_def smap_Union_def)

lemma smap_Union_mono:
  assumes "list_all2 (op \<sqsubseteq>) ms1 ms2"
  shows "\<Union>. ms1 \<sqsubseteq> \<Union>. ms2"
using assms by (induct rule:list_induct2[OF list_all2_lengthD[OF assms], case_names Nil Cons])(auto intro:smap_union_mono)

lemma smap_singleton_mono: "v \<sqsubseteq> v'\<Longrightarrow> {k := v}. \<sqsubseteq> {k := v'}."
 by (subst below_fun_def, auto simp add: smap_singleton_def)

lemma smap_union_comm: "m1 \<union>. m2 = m2 \<union>. m1"
by (rule ext,auto simp add:smap_union_def)

lemma smap_union_empty1[simp]: "{}. \<union>. m = m"
  by(rule ext, auto simp add:smap_union_def smap_empty_def)

lemma smap_union_empty2[simp]: "m \<union>. {}. = m"
  by(rule ext, auto simp add:smap_union_def smap_empty_def)

lemma smap_union_assoc [simp]: "(m1 \<union>. m2) \<union>. m3 = m1 \<union>. (m2 \<union>. m3)"
  by (rule ext, auto simp add:smap_union_def)

lemma smap_Union_append[simp]: "\<Union>. (m1@m2) = (\<Union>. m1) \<union>. (\<Union>. m2)"
  by (induct m1) auto

lemma smap_Union_rev[simp]: "\<Union>. (rev l) = \<Union>. l"
  by(induct l)(auto simp add:smap_union_comm)

lemma smap_Union_map_rev[simp]: "\<Union>. (map f (rev l)) = \<Union>. (map f l)"
  by(subst rev_map[THEN sym], subst smap_Union_rev, rule refl)

end