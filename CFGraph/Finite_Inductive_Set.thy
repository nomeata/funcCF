theory Finite_Inductive_Set
imports Main
begin

inductive tails for l
  where "tails l l"
      | "tails l (x#xs) \<Longrightarrow> tails l xs"

print_theorems

definition "Ft l = (\<lambda>p. {x. x = l \<or> (\<exists>xa. (xa # x) \<in> p)})"

thm tails_def[simplified]

primrec iterate 
  where it_0: "iterate 0 f x = x"
      | it_Suc: "iterate (Suc n) f x = f (iterate n f x)"

(* lemma "mono f \<Longrightarrow> F (\<Union>S) \<le> \<Union> (F`S)" *)

lemma assumes "\<And> S. F (\<Union>S) \<le> \<Union> (F`S)"
  shows "lfp F \<le> (\<Union>i. iterate i F {})"
by (auto
  intro!: lfp_lowerbound
  simp del:iterate.simps  Union_image_eq
  simp add: it_Suc[THEN sym, of F _ "{}"] UNION_eq_Union_image
  dest!: subsetD[OF assms]
  )

lemma union_difference: "(\<Union>i. S i) = (\<Union>i. S (Suc i) - S i) \<union> S 0" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof fix x
    def i == "LEAST i. x \<in> S i"
    assume "x \<in> (\<Union>i. S i)"
    hence i: "x \<in> S i"
      unfolding i_def
      by -(rule LeastI_ex, auto)
    show "x\<in>?rhs"
    proof(cases i)
      case 0 thus ?thesis using i by auto next
      case (Suc i')
      hence "x \<notin> S i'"
        unfolding i_def
        by -(rule not_less_Least, auto)
      with i and Suc show ?thesis by auto
    qed
  qed
qed auto

lemma UNION_event_empty:
  assumes "\<And>(i::nat). i > (i0::nat) \<Longrightarrow> S i = {}"
  shows "(\<Union>i. S i) = (\<Union>i\<in>{i. i \<le> i0}. S i)" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof fix x assume "x \<in> ?lhs"
    then obtain i where i: "x \<in> S i" by auto
    show "x\<in>?rhs"
    proof(cases "i > i0")
    case True hence "S i = {}" using assms by simp
      with i show ?thesis by auto next
    case False hence "i \<in> {i. i\<le>i0}" by  auto 
      thus?thesis using i by auto
    qed
  qed
qed auto

thm union_difference[of "\<lambda>i. iterate i f {}", simplified]
thm trans[OF union_difference[of "\<lambda>i. iterate i f {}", simplified] UNION_event_empty]

find_theorems Greatest

definition descending_functional
  where "descending_functional F = (\<forall> S. \<forall> x \<in> F (F S) - (F S).  \<exists> y \<in> (F S) - S . size x < size y)"

lemma descending_functionalD:
  "\<lbrakk> descending_functional F ; x \<in> F (F S); x \<notin> F S \<rbrakk> \<Longrightarrow> \<exists> y \<in> (F S) - S. size x < size y"
unfolding descending_functional_def by auto

lemma diff_empty_iff: "A - B = {} \<longleftrightarrow> A \<subseteq> B" by auto

lemma diff_zero:
  assumes mono: "mono F"
     and "iterate (Suc i) F {} - iterate i F {} = {}"
  shows "iterate (Suc (Suc i)) F {} - iterate (Suc i) F {} = {}"
using assms
by (auto simp add:diff_empty_iff iterate.simps dest: monoD)

lemma "descending_functional (Ft l)"
proof- {
  fix S x
  assume "x\<in>Ft l (Ft l S)" and "x \<notin> (Ft l S)"
  hence "x \<noteq> l" unfolding Ft_def  by auto
  from `x\<in>Ft l (Ft l S)` and `x \<noteq> l`
  obtain a x' where "x' \<in> (Ft l S)" and "x' =a#x"
    unfolding Ft_def by auto
  moreover
  have "x' \<notin> S" proof(rule ccontr, drule notnotD)
    assume "x' \<in> S" hence "x \<in> Ft l S" using `x' =a#x`
      unfolding Ft_def by auto
    thus False using `x \<notin> Ft l S` by contradiction
  qed
  ultimately
  have "\<exists>x'. x' \<in> (Ft l S - S) \<and> length x < length x'" by auto
  } thus ?thesis unfolding descending_functional_def by auto
qed

lemma
  assumes finite: "\<And> S. finite S \<Longrightarrow> finite (F S)"
      and mono: "mono F"
      and desc: "descending_functional F"
  shows "\<exists> i0 :: nat . \<forall>i . i > i0 \<longrightarrow> F (iterate i F {}) - iterate i F {} = {}"
proof-
  def i0 == "Max (size ` (F {}))"
  
  from finite have finite_it: "\<And> i. finite (iterate i F {})" by (induct_tac i, auto)

  { fix i
    have "iterate (Suc i) F {} - iterate i F {} \<noteq> {} \<Longrightarrow> Max (size ` (iterate (Suc i) F {} - iterate i F {} )) + i \<le> i0"
    proof(induct i)
    case 0 show ?case by (auto simp add:i0_def) next
    case (Suc i)
      from Suc(1) 
      have fin_size': "finite (size ` (iterate (Suc (Suc i)) F {} - iterate (Suc i) F {}))"        
        (is "finite (size `?Diff')") using finite_it[of "Suc (Suc i)"] by simp

      show "?Diff' \<noteq> {} \<Longrightarrow> Max (size ` ?Diff') + Suc i \<le> i0"
      proof(cases "iterate (Suc i) F {} - iterate i F {} = {}")
      case True 
        hence "?Diff' = {}" by (rule diff_zero[OF mono])
        moreover assume "?Diff' \<noteq> {}"
        ultimately show  ?thesis by contradiction next
      case False 
        hence ne_size: "size ` (iterate (Suc i) F {} - iterate i F {}) \<noteq> {}" (is "size ` ?Diff \<noteq> _")
          by simp
        from False and Suc(1) have asm: "Max (size ` ?Diff) + i \<le> i0" by simp

        assume "?Diff' \<noteq> {}"
        hence ne_size': "size ` ?Diff' \<noteq> {}" by auto

        have fin_size: "finite (size ` ?Diff)"
          using finite_it[of "Suc i"] by simp

        have "Max (size ` ?Diff') < Max (size ` ?Diff)"
        apply (subst Max_less_iff[OF fin_size' ne_size'])
        apply (subst Max_gr_iff[OF fin_size ne_size])
        by (auto dest: descending_functionalD[OF desc])

        with asm show ?thesis by auto
      qed
    qed
  } note maxbound = this

  {
    fix i
    assume "i0 < i"
    hence "iterate (Suc i) F {} - iterate i F {} = {}"
    by -(rule ccontr, drule maxbound, auto)
  }
  thus ?thesis by auto
qed


end