theory SetMap
  imports HOLCF HOLCFUtils
begin

definition smap_empty
 where "smap_empty k = {}"

definition smap_union :: "('a::type \<Rightarrow> 'b::type set)  \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
 where "smap_union smap1 smap2 k =  smap1 k \<union> smap2 k"

primrec smap_Union :: "('a::type \<Rightarrow> 'b::type set) list \<Rightarrow> 'a \<Rightarrow> 'b set"
  where [simp]:"smap_Union [] = smap_empty"
      | "smap_Union (m#ms) = smap_union m (smap_Union ms)"

definition smap_singleton :: "'a::type \<Rightarrow> 'b::type set \<Rightarrow> 'a \<Rightarrow> 'b set"
  where "smap_singleton k vs = smap_empty (k := vs)"

lemma smap_union_mono: "\<lbrakk> ve1 \<sqsubseteq> ve1'; ve2 \<sqsubseteq> ve2' \<rbrakk> \<Longrightarrow>  smap_union ve1 ve2 \<sqsubseteq> smap_union ve1' ve2'"
  by (subst below_fun_def, subst (asm) (1 2) below_fun_def, auto simp add:sqsubset_is_subset smap_union_def)

lemma smap_Union_union: "\<And> m1 ms. smap_union m1 (smap_Union ms) = smap_Union (m1#ms)"
  by (rule ext, auto simp add: smap_union_def smap_Union_def)

lemma smap_Union_mono:
  assumes "list_all2 (op \<sqsubseteq>) ms1 ms2"
  shows "smap_Union ms1 \<sqsubseteq> smap_Union ms2"
using assms by (induct rule:list_induct2[OF list_all2_lengthD[OF assms], case_names Nil Cons])(auto intro:smap_union_mono)

lemma smap_singleton_mono: "v \<sqsubseteq> v'\<Longrightarrow> smap_singleton k v \<sqsubseteq> smap_singleton k v'"
 by (subst below_fun_def, auto simp add: smap_singleton_def)

lemma [simp]: "{}\<sqsubseteq>S"
 by (simp add:sqsubset_is_subset)


end