theory Computability
imports HOLCF HOLCFUtils
begin

lemma index_shift:
  "(\<Union>i. A (Suc i)) = (\<Union>i\<in>{1..}. A i)"
apply auto
apply (rule_tac x= "i - 1" in exI)
apply auto
done

lemma insert_0:
  "insert (0::nat) {1..} = UNIV"
by auto

lemma insert_Suc_n:
  "insert (Suc n) {0..n} = {0..Suc n}"
by auto

lemma theorem10:
  fixes g :: "'a::cpo \<rightarrow> 'b::type set" and r :: "'a \<rightarrow> 'a"
  shows "fix_syn (\<lambda> f.  (\<Lambda> x. g\<cdot>x \<union> f\<cdot>(r\<cdot>x))) = (\<Lambda> x. (\<Union>i. g\<cdot>(iterate i\<cdot>r\<cdot>x)))"
proof(induct rule:fix_eqI[OF ext_cfun below_cfun_ext, case_names fp least])
case (fp x)
  have "g\<cdot>x \<union> (\<Union>i. g\<cdot>(iterate i\<cdot>r\<cdot>(r\<cdot>x))) = g\<cdot>(iterate 0\<cdot>r\<cdot>x) \<union> (\<Union>i. g\<cdot>(iterate (Suc i)\<cdot>r\<cdot>x))"
    by (simp add: iterate_Suc2 del: iterate_Suc)
  also have "\<dots> = g\<cdot>(iterate 0\<cdot>r\<cdot>x) \<union> (\<Union>i\<in>{1..}. g\<cdot>(iterate i\<cdot>r\<cdot>x))"
    by (subst index_shift, rule refl)
  also have "\<dots>  = (\<Union>i\<in>insert 0 {1..}. g\<cdot>(iterate i\<cdot>r\<cdot>x))"
    by simp
  also have "... = (\<Union>i. g\<cdot>(iterate i\<cdot>r\<cdot>x))"
    by (subst insert_0, rule refl)
  finally
  show ?case by auto
next
case (least f x)
  hence expand: "\<And>x. f\<cdot>x = (g\<cdot>x \<union> f\<cdot>(r\<cdot>x))" by (auto simp:expand_cfun_eq)
  { fix n
    have "f\<cdot>x = (\<Union>i\<in>{0..n}. g\<cdot>(iterate i\<cdot>r\<cdot>x)) \<union> f\<cdot>(iterate (Suc n)\<cdot>r\<cdot>x)"
    proof(induct n)
      case 0 thus ?case by (auto simp add:expand[of x])
      case (Suc n)
      then have "f\<cdot>x = (\<Union>i\<in>{0..n}. g\<cdot>(iterate i\<cdot>r\<cdot>x)) \<union> f\<cdot>(iterate (Suc n)\<cdot>r\<cdot>x)" by simp
      also have "\<dots> = (\<Union>i\<in>{0..n}. g\<cdot>(iterate i\<cdot>r\<cdot>x))
                 \<union> g\<cdot>(iterate (Suc n)\<cdot>r\<cdot>x) \<union> f\<cdot>(iterate (Suc (Suc n))\<cdot>r\<cdot>x)"
             by(subst expand[of "iterate (Suc n)\<cdot>r\<cdot>x"], auto)
      also have "\<dots> = (\<Union>i\<in>insert (Suc n) {0..n}. g\<cdot>(iterate i\<cdot>r\<cdot>x)) \<union> f\<cdot>(iterate (Suc (Suc n))\<cdot>r\<cdot>x)"
             by auto
      also have "\<dots> = (\<Union>i\<in>{0..Suc n}. g\<cdot>(iterate i\<cdot>r\<cdot>x)) \<union> f\<cdot>(iterate (Suc (Suc n))\<cdot>r\<cdot>x)"
             by (simp add:insert_Suc_n)
      finally show ?case .
    qed
  } note fin = this
  have "(\<Union>i. g\<cdot>(iterate i\<cdot>r\<cdot>x)) \<subseteq> f\<cdot>x"
    proof(rule UN_least)
      fix i
      show "g\<cdot>(iterate i\<cdot>r\<cdot>x) \<subseteq> f\<cdot>x"
      using fin[of i] by auto
    qed
  thus ?case
    apply (subst sqsubset_is_subset) by auto
qed

definition powerset_lift :: "('a::cpo \<rightarrow> 'b::type set) \<Rightarrow> 'a set \<rightarrow> 'b set" ("\<^ps>")
  where "\<^ps>f = (\<Lambda> S. (\<Union>y\<in>S . f\<cdot>y))"

lemma powerset_lift_singleton[simp]:
  "\<^ps>f\<cdot>{x} = f\<cdot>x"
unfolding powerset_lift_def by simp

lemma lemma11:
  fixes f :: "'a \<rightarrow> 'b set" and g :: "'a \<rightarrow> 'b set" and R :: "'a \<rightarrow> 'a set"
  assumes "\<And>x. f\<cdot>x = g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f\<cdot>y)"
  shows "\<^ps>f\<cdot>S = \<^ps>g\<cdot>S \<union> \<^ps>f\<cdot>(\<^ps>R\<cdot>S)"
proof-
  have "\<^ps>f\<cdot>S = (\<Union>x\<in>S . f\<cdot>x)" unfolding powerset_lift_def by auto
  also have "\<dots> = (\<Union>x\<in>S . g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f\<cdot>y))" apply (subst assms) by simp
  also have "\<dots> = \<^ps>g\<cdot>S \<union> \<^ps>f\<cdot>(\<^ps>R\<cdot>S)" by (auto simp add:powerset_lift_def)
  finally
  show ?thesis .
qed

(* lemma 10 as used in lemma 12 *)
lemmas theorem10ps = theorem10[of "\<^ps>g" "\<^ps>r",standard]

lemma powerset_lift_union[simp]:
  "\<^ps>f\<cdot>(A \<union> B) = \<^ps>f\<cdot>A \<union> \<^ps>f\<cdot>B"
unfolding powerset_lift_def by auto

lemma UNION_commute:"(\<Union>x\<in>A. \<Union>y\<in>B . P x y) = (\<Union>y\<in>B. \<Union>x\<in>A . P x y)"
  by auto

lemma powerset_lift_UNION:
  "(\<Union>x\<in>S. \<^ps> g\<cdot>(A x)) = \<^ps> g\<cdot>(\<Union>x\<in>S. A x)"
unfolding powerset_lift_def by auto

lemma powerset_lift_iterate_UNION:
  "(\<Union>x\<in>S. iterate i\<cdot>(\<^ps> g)\<cdot>(A x)) = iterate i\<cdot>(\<^ps> g)\<cdot>(\<Union>x\<in>S. A x)"
by (induct i, auto simp add:powerset_lift_UNION)

lemmas powerset_distr = powerset_lift_UNION powerset_lift_iterate_UNION

(* discrete_cpo, otherwise x \<mapsto> {x} nicht continous *)
lemma theorem12:
  fixes g :: "'a::discrete_cpo \<rightarrow> 'b::type set" and R :: "'a \<rightarrow> 'a set"
  assumes F_fix: "F = fix_syn (\<lambda>F. \<Lambda> x. \<^ps> g\<cdot>x \<union> F\<cdot>(\<^ps> R\<cdot>x))"
  shows "fix_syn (\<lambda>f. \<Lambda> x. g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f\<cdot>y)) = (\<Lambda> x. F\<cdot>{x})"
proof(induct rule:fix_eqI[OF ext_cfun below_cfun_ext, case_names fp least])
have F_union: "F = (\<Lambda> x. \<Union>i. \<^ps> g\<cdot>(iterate i\<cdot>(\<^ps> R)\<cdot>x))"
  using F_fix by(simp)(rule theorem10ps)
case (fp x)
   have "g\<cdot>x \<union> (\<Union>x'\<in>R\<cdot>x. F\<cdot>{x'}) = \<^ps> g\<cdot>{x} \<union> F\<cdot>(\<^ps> R\<cdot>{x})"
    unfolding powerset_lift_singleton
    by (auto simp add: powerset_distr UNION_commute F_union)
  also have "\<dots> = F\<cdot>{x}"
    by (subst (2) fix_eq4[OF F_fix], auto)
  finally show ?case by simp
next
case (least f' x)
  hence expand: "f' = (\<Lambda> x. g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f'\<cdot>y))" by simp
  have "\<^ps>f' = (\<Lambda> S. \<^ps>g\<cdot>S \<union> \<^ps>f'\<cdot>(\<^ps> R\<cdot>S))"
    by (subst expand, rule ext_cfun, auto simp add:powerset_lift_def)
  hence "(\<Lambda> F. \<Lambda> x. \<^ps> g\<cdot>x \<union> F\<cdot>(\<^ps> R\<cdot>x))\<cdot>(\<^ps>f') = \<^ps>f'" by simp
  from fix_least[OF this] and F_fix
  have  "F \<sqsubseteq> \<^ps>f'"  by simp
  hence  "F\<cdot>{x} \<sqsubseteq> \<^ps>f'\<cdot>{x}"
    by (subst (asm)expand_cfun_below, auto simp del:powerset_lift_singleton)
  thus ?case by (auto simp add:sqsubset_is_subset)
qed

lemma
  fixes g :: "'a::discrete_cpo \<rightarrow> 'b::type set" and R :: "'a \<rightarrow> 'a set"
  shows "fix_syn (\<lambda>f. \<Lambda> x. g\<cdot>x \<union> (\<Union>y\<in>R\<cdot>x. f\<cdot>y))\<cdot>x =  \<^ps> g\<cdot>(\<Union>i.(iterate i\<cdot>(\<^ps> R)\<cdot>{x}))"
  by(subst theorem12[OF theorem10ps[THEN sym]], auto simp add:powerset_distr)

end