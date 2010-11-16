theory Finite_Inductive_Set
imports Main
begin

primrec iter
  where it_0: "iter 0 f x = x"
      | it_Suc: "iter (Suc n) f x = f (iter n f x)"

definition descending_functional :: "('a \<Rightarrow> nat) \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
  where "descending_functional p F = (\<forall> S. \<forall> x \<in> F (F S) - (F S).  \<exists> y \<in> (F S) - S . p x < p y)"

lemma descending_functionalD:
  "\<lbrakk> descending_functional p F ; x \<in> F (F S); x \<notin> F S \<rbrakk> \<Longrightarrow> \<exists> y \<in> (F S) - S. p x < p y"
unfolding descending_functional_def by auto

lemma descending_functionalI[intro]:
  "(\<And>S x. \<lbrakk> x \<in> F (F S);  x \<notin> F S \<rbrakk> \<Longrightarrow> \<exists> y \<in> (F S) - S. p x < p y) \<Longrightarrow> descending_functional p F"
unfolding descending_functional_def by auto

definition finiteness_preserving
  where "finiteness_preserving  F = (\<forall>S . finite S \<longrightarrow> finite (F S))"

lemma finiteness_preservingD:
  "\<lbrakk> finiteness_preserving F ; finite S \<rbrakk> \<Longrightarrow> finite (F S)"
unfolding finiteness_preserving_def by auto

lemma finiteness_preservingI[intro]:
  "\<lbrakk> \<And> S. finite S \<Longrightarrow> finite (F S) \<rbrakk> \<Longrightarrow> finiteness_preserving F"
unfolding finiteness_preserving_def by auto


lemma diff_empty_iff: "A - B = {} \<longleftrightarrow> A \<subseteq> B" by auto

lemma diff_zero:
  assumes mono: "mono F"
     and "iter (Suc i) F {} - iter i F {} = {}"
  shows "iter (Suc (Suc i)) F {} - iter (Suc i) F {} = {}"
using assms
by (auto simp add:diff_empty_iff iter.simps dest: monoD)

lemma iteration_stops:
  assumes mono: "mono F"
      and finite: "\<And> S. finite S \<Longrightarrow> finite (F S)"
      and desc: "descending_functional p F"
  shows "\<exists> i :: nat . F (iter i F {}) - iter i F {} = {}"
proof-
  def i0 == "Suc (Max (p ` (F {})))"
  let "?Diff i" = "iter (Suc i) F {} - iter i F {}"
  
  from finite have finite_it: "\<And> i. finite (iter i F {})" by (induct_tac i, auto)
  have finite_p: "\<And> i. finite (p ` ?Diff i)" by (intro finite_imageI finite_Diff finite_it)

  def i \<equiv> i0
  have maxbound: "?Diff i \<noteq> {} \<Longrightarrow> Max (p ` ?Diff i) + i < i0"
  proof(induct i)
    case 0 show ?case by (auto simp add:i0_def) next
    case (Suc i)
      hence ne_p': "p ` ?Diff (Suc i) \<noteq> {}" by auto

      show "?Diff (Suc i) \<noteq> {} \<Longrightarrow> Max (p ` ?Diff (Suc i)) + Suc i < i0"
      proof(cases "?Diff i = {}")
      case True 
        hence "?Diff (Suc i) = {}" by (rule diff_zero[OF mono])
        moreover assume "?Diff (Suc i) \<noteq> {}"
        ultimately show  ?thesis by contradiction next
      case False 
        hence ne_p: "p ` ?Diff i \<noteq> {}" by simp

        have "Max (p ` ?Diff (Suc i)) < Max (p ` ?Diff i)"
          apply (subst Max_less_iff[OF finite_p[of "Suc i"] ne_p'])
          apply (subst Max_gr_iff[OF finite_p[of i] ne_p])
          by (auto dest: descending_functionalD[OF desc])
        moreover
        have "Max (p ` ?Diff i) + i < i0" 
          using False and Suc(1) by simp
        ultimately
        show ?thesis by auto
      qed
  qed
  have "?Diff i0 = {}" using maxbound[unfolded i_def] by auto
  thus ?thesis by auto
qed

lemma lfp_finite:
  assumes mono: "mono F"
      and finite: "finiteness_preserving F"
      and desc: "descending_functional p F"
  shows "finite (lfp F)"
proof-
  from iteration_stops[OF mono finiteness_preservingD[OF finite] desc]
  obtain i where "F (iter i F {}) - iter i F {} = {}" by auto
  hence "F (iter i F {}) \<subseteq> iter i F {}" by auto
  hence "lfp F \<subseteq> iter i F {}" by(rule lfp_lowerbound)
  moreover
  have "finite (iter i F {})"
  apply(induct i) by (auto intro: finiteness_preservingD[OF finite])
  ultimately
  show ?thesis by (rule finite_subset)
qed

lemma finite_at_most_one:
  assumes "\<And> x x'. \<lbrakk> x \<in> S ; x' \<in> S \<rbrakk> \<Longrightarrow> x = x'"
  shows "finite S"
proof(cases "S = {}")
  case False
    then obtain x where "x \<in> S" by auto
    with assms have "S = {x}" by auto
    thus ?thesis by auto
qed auto

lemma finite_inj_collect:
  assumes inj: "\<And> x x'. f x = f x' \<Longrightarrow> x = x'"
    and  fin: "finite S" 
  shows "finite (\<lambda> x. S (f x))"
proof-
  have "finite (\<Union> z\<in>S. {x. f x = z})"
    by (auto intro: finite_UN_I[OF fin] finite_at_most_one dest: inj)
  moreover
  have "(\<Union> z\<in>S. {x. f x = z}) = {x. f x \<in> S}"
    by auto
  ultimately
  have "finite {x. f x \<in> S}" by auto
  thus ?thesis unfolding mem_def Collect_def by auto
qed

lemmas finite_inj_collect_lfp (* Help the pattern matcher *)
 = finite_inj_collect[of _ "lfp F", standard]

lemma ind_set_finite:
  assumes defn: "S = lfp F"
      and mono: "mono F"
      and finite: "finiteness_preserving F"
      and desc: "descending_functional p F"
  shows "finite S"
by (subst defn, rule lfp_finite[OF mono finite desc])

lemma finiteness_preserving_disj:
  assumes F1: "finiteness_preserving F1"
      and F2: "finiteness_preserving F2"
  shows "finiteness_preserving (\<lambda>p x.  F1 p x \<or> F2 p x)"
proof 
  fix S :: "'a set"
  assume fin: "finite S"
  from finiteness_preservingD[OF F1 fin] finiteness_preservingD[OF F2 fin]
  have "finite (F1 S \<union> F2 S)" by auto
  thus "finite (\<lambda>x. F1 S x \<or> F2 S x)"
    unfolding Un_def mem_def Collect_def by auto
qed

lemma finiteness_preserving_singleton:
  "finiteness_preserving (\<lambda>p x. x = y)"
proof
  have "finite {y}" by auto
  thus "finite (\<lambda>x. x = y)"
    unfolding insert_def mem_def Collect_def by auto
qed

lemma finiteness_preserving_bex_conj:
  assumes "finiteness_preserving (\<lambda>p x. \<exists>y. p (f x y))"
  shows "finiteness_preserving (\<lambda>p x. \<exists>y z. x = z \<and> p (f z y))"
using assms by simp

lemma finiteness_preserving_bex:
  assumes "\<And> x x' y y'. f x y = f x' y' \<Longrightarrow> x = x'"
  shows "finiteness_preserving (\<lambda>p x. \<exists>y. p (f x y))"
proof
  fix S :: "'c set"
  assume fin: "finite S"
  have "finite (\<Union> z\<in>S. {x. \<exists>y. f x y = z})"
    by (auto intro: finite_UN_I[OF fin] finite_at_most_one dest: assms)
  moreover
  have "(\<Union> z\<in>S. {x. \<exists>y. f x y = z}) = {x. \<exists>y. f x y \<in> S}"
    by auto
  ultimately
  have "finite {x. \<exists>y. f x y \<in> S}" by auto
  thus "finite (\<lambda>x. \<exists>y. S (f x y))"
    unfolding mem_def Collect_def by auto
qed

lemma finiteness_preserving_split:
  assumes "finiteness_preserving (\<lambda>p x. f p (fst x) (snd x))"
  shows "finiteness_preserving (\<lambda>p (a,b). f p a b)"
using assms by (simp add:split_def)

lemmas finiteness_preserving_lemmas =
  finiteness_preserving_disj
  finiteness_preserving_singleton
  finiteness_preserving_bex
  finiteness_preserving_bex_conj
  (* finiteness_preserving_split *)

text {* Example application *}

inductive tails for l
  where "tails l l"
      | "tails l (x#xs) \<Longrightarrow> tails l xs"

method_setup mono =
"Scan.succeed (K (SIMPLE_METHOD (EVERY [rtac @{thm monoI} 1,
      REPEAT (resolve_tac [@{thm le_funI}, @{thm le_boolI'}] 1),
      REPEAT (FIRST
        [atac 1,
         resolve_tac (Inductive.get_monos @{context}) 1,
         etac @{thm le_funE} 1, dtac @{thm le_boolD} 1])])))"
"Solves monotonicity goals"

lemma "finite (tails l)"
unfolding tails_def
proof (induct rule: lfp_finite[of _ size, case_names mono finiteness desc])
case mono show ?case by mono
next
case finiteness show ?case by (intro finiteness_preserving_lemmas, simp)
next
case desc show ?case
  by (rule, auto simp add: Bex_def mem_def fun_diff_def bool_diff_def)
qed

text {* Transform a least fixpoint with multiple parameters to one
 with one paramter, to be able to consider it a set *}

definition splitF :: "(('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)) \<Rightarrow> ((('a\<times>'b) \<Rightarrow> 'c) \<Rightarrow> (('a\<times>'b) \<Rightarrow> 'c))"
  where [simp]:"splitF f = (\<lambda>S. split (f (curry S)))"

lemma split_mono_iff[simp]:
  "split S \<le> split S' \<longleftrightarrow> S \<le> S'"
proof
  assume "split S \<le> split S'"
  show "S \<le> S'"
  apply (rule le_funI, rule le_funI)
  proof-
    fix x y 
    from le_funD[OF `split S \<le> split S'`, of "(x,y)"]
    show "S x y \<le> S' x y"
      by auto
  qed 
qed (auto intro: le_funI dest:le_funD simp add:split_def)

lemma split_mono: "mono split" by (rule monoI, auto)

lemma curry_mono_iff[simp]:
  "curry S \<le> curry S' \<longleftrightarrow> S \<le> S'"
apply (subst (3 4) split_curry[THEN sym])
apply (subst split_mono_iff)
apply (rule refl)
done

lemma curry_mono: "mono curry" by (rule monoI, auto)

lemma splitF_mono:
  assumes "mono f" shows "mono (splitF f)"
unfolding splitF_def
by(intro monoI monoD[OF split_mono] monoD[OF assms] monoD[OF curry_mono])

lemma lfp_curry':
  assumes mono: "mono f"
  shows  "lfp(\<lambda> p x y. f p x y) = curry (lfp (splitF f))" (is "?lhs = ?rhs")
proof(rule antisym)
  show "lfp f \<le> curry (lfp (splitF f))"
  proof (rule lfp_lowerbound)
    have "f (curry (lfp (splitF f))) = curry (split (f (curry (lfp (splitF f)))))" by simp
    also
    have "\<dots> = curry (splitF f (lfp (splitF f)))" by simp
    also
    have "\<dots> = curry (lfp (splitF f))"
      by (subst lfp_unfold[OF splitF_mono[OF mono], THEN sym], rule refl)
    finally
    show "f (curry (lfp (splitF f))) \<le> curry (lfp (splitF f))" by simp
  qed

  have "lfp (splitF f) \<le> split (lfp f)"
  proof (rule lfp_lowerbound)
    have "splitF f (split (lfp f)) = split (f (lfp f))" by simp
    also
    have "\<dots> = split (lfp f)"
      by (subst lfp_unfold[OF mono, THEN sym], rule refl)
    finally
    show "splitF f (split (lfp f)) \<le> split (lfp f)" by simp
  qed
  hence "curry (lfp (splitF f)) \<le> curry (split (lfp f))"
    by (rule monoD[OF curry_mono])
  thus "curry (lfp (splitF f)) \<le> lfp f" by simp
qed

lemmas lfp_curry = lfp_curry'[simplified splitF_def curry_def]

lemma lfp_curryD':
  assumes mono: "mono f"
  and curried: "mono (splitF f) \<Longrightarrow> P (curry (lfp (splitF f)))"
  shows  "P (lfp f)"
by (subst lfp_curry'[OF mono], rule curried[OF splitF_mono[OF mono]])

lemmas lfp_curryD = lfp_curryD'[simplified splitF_def curry_def split_def]

text {* Now lets try this for a recursively defined functorial *}

inductive tails' and elems' for l
  where "tails' l l"
      | "tails' l (x#xs) \<Longrightarrow> tails' l xs"
      | "tails' l (x#xs) \<Longrightarrow> elems' l x"

lemma "finite (tails' l)"
unfolding tails'_def
unfolding tails'_elems'_def
apply (rule lfp_curryD[of _ "\<lambda>l. finite (l False undefined)"])
apply mono
apply (erule lfp_curryD)
apply (rule finite_inj_collect_lfp)
apply auto[1]
apply (erule lfp_finite[of _ size])
apply (intro finiteness_preserving_lemmas)

oops


(*
inductive tailselems for l
  where "tailselems l (Inl l)"
      | "tailselems l (Inl (x#xs)) \<Longrightarrow> tailselems l (Inl xs)"
      | "tailselems l (Inl (x#xs)) \<Longrightarrow> tailselems l (Inr x)"

lemma "finite (tailselems (l::'a::size list))"
unfolding tailselems_def
proof (induct rule: lfp_finite[of _ "sum_case (list_size size) size", case_names mono finiteness desc])
case mono show ?case by mono 
next
case finiteness show ?case
apply (intro finiteness_preserving_lemmas)
sorry
next
case desc show ?case
  apply (rule)
  apply (simp add:mem_def Bex_def Ball_def fun_diff_def bool_diff_def)
oops
*)

end
