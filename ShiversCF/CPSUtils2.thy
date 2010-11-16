header  {* Syntax tree helpers *}

theory CPSUtils2
imports CPSScheme Finite_Inductive_Set
begin

text {*
This theory defines the sets @{text "lambdas p"}, @{text "calls p"}, @{text "calls p"}, @{text "vars p"}, @{text "labels p"} and @{text "prims p"} as the subexpressions of the program @{text "p"}. Finiteness is shown for each of these sets, and some rules about how these sets relate. All these rules are proven more or less the same ways, which is very inelegent due to the nesting of the type and the shape of the derived induction rule.

It would be much nicer to start with these rules and define the set inductively. Unfortunately, that approach would make it very hard to show the finiteness of the sets in question.
*}

inductive_set lambdas' and calls' and values'
  for p
  where self: "p \<in> lambdas' p"
      | lamC: "Lambda l vs c \<in> lambdas' p \<Longrightarrow> c \<in> calls' p"
      | appD: "App l d ds \<in> calls' p \<Longrightarrow> d \<in> values' p"
      | appDs: "\<lbrakk> App l d ds \<in> calls' p ; d' \<in> set ds \<rbrakk> \<Longrightarrow> d' \<in> values' p"
      | letC: "Let l binds c' \<in> calls' p \<Longrightarrow> c' \<in> calls' p"
      | letLs: "\<lbrakk> Let l binds c' \<in> calls' p ; l' \<in> snd ` set binds \<rbrakk> \<Longrightarrow> l' \<in> lambdas' p"
      | val: "L l \<in> values' p \<Longrightarrow> l \<in> lambdas' p"

types pos = "nat list"

find_consts "'a list \<Rightarrow> (nat \<times> 'a) list"
find_theorems upt

function (sequential) Pos :: "lambda \<Rightarrow> pos set"
and PosC:: "call \<Rightarrow> pos set"
and PosV:: "val \<Rightarrow> pos set"
 where "Pos  (Lambda l vs c) = {[]} \<union> Cons 0 ` PosC c"
    | "PosC (App l d ds) = {[]} \<union> Cons 0 ` PosV d \<union> (\<Union>(d,n) \<in> set (zip ds [0..<size ds]). Cons (Suc n) ` PosV d)"
    | "PosC (Let l binds c') = {[]} \<union> (\<Union> ((_,l),n) \<in> set (zip binds [0..<size binds]). Cons (Suc n) ` Pos l)
                                    \<union> Cons 0 ` PosC c'"
    | "PosV (L l) = {[]} \<union> Cons 0 ` Pos l"
    | "PosV _     = {[]}"
by (pat_completeness, auto)
termination
apply (relation "measure (sum_case size (sum_case size size))")
apply (auto simp add:set_zip)
apply (subst less_Suc_eq_le)
apply (rule trans_le_add2)
apply (rule list_size_estimation')
apply auto
apply (subst less_Suc_eq_le)
apply (rule trans_le_add1)
apply (rule_tac xs= binds and x = "binds!i" in list_size_estimation')
apply auto
apply (case_tac "binds!i")
apply auto
done

lemma emptypos[simp]: "[] \<in> Pos l"  "[] \<in> PosC c"  "[] \<in> PosV v" 
apply (cases l, auto)[1]
apply (cases c, auto)[1]
apply (cases v, auto)[1]
done

lemma finite_Pos: "finite (Pos l)" and "finite (PosC c)" "finite (PosV v)"
by (induct rule: Pos_PosC_PosV.induct, auto simp add:set_zip intro!:finite_imageI, blast+)

fun subterm :: "lambda + call + val \<Rightarrow> pos \<rightharpoonup> lambda + call + val"
where
   "subterm t [] = Some t"
 | "subterm (Inl (Lambda l vs c)) (x#xs) = (case x of  0 \<Rightarrow> subterm (Inr (Inl c)) xs | Suc _ \<Rightarrow> None)"
 | "subterm (Inr (Inl (App l d ds))) (x#xs) = (case x of 0 \<Rightarrow> subterm (Inr (Inr d)) xs | Suc n \<Rightarrow> if n < length ds then subterm (Inr (Inr (ds!n))) xs else None)"
 | "subterm (Inr (Inl (Let l binds c'))) (x#xs) = (case x of 0 \<Rightarrow> subterm (Inr (Inl c')) xs | Suc n \<Rightarrow> if n < length binds then subterm (Inl (snd (binds!n))) xs else None)"
 | "subterm (Inr (Inr (L l))) (x#xs) = (case x of 0 \<Rightarrow> subterm (Inl l) xs | Suc _ \<Rightarrow> None)"
 | "subterm (Inr (Inr _)) (x#xs) = None"

lemma subterm_Pos: "subterm t pos = Some t' \<Longrightarrow> pos \<in> (case t of Inl l \<Rightarrow> Pos l | Inr (Inl c) \<Rightarrow> PosC c | Inr (Inr v) \<Rightarrow> PosV v)"
apply(induct rule:subterm.induct)
apply (auto simp add:set_zip split:sum.split nat.split_asm split_if_asm)
apply (erule_tac x=nat in meta_allE)
apply (erule_tac x="ds!nat" in allE)
apply (erule_tac x="nat" in allE)
apply auto 
apply (erule_tac x="nat" in allE)
apply auto

apply (erule_tac x=nat in meta_allE, auto)
apply (rule_tac x="fst (fst (binds ! nat))" in exI)
apply (rule_tac x="snd (fst (binds ! nat))" in exI)
apply (rule_tac x="snd (binds ! nat)" in exI)
apply (rule_tac x="nat" in exI)
apply auto
done

lemma subterm_comp: "subterm p (pos@pos') = (case subterm p pos of Some t \<Rightarrow> subterm t pos' | None \<Rightarrow> None)"
apply (induct p "pos@pos'" arbitrary:pos rule:subterm.induct)
by (auto simp add:Cons_eq_append_conv split:nat.split)


lemma subterm_ran_subsets: shows "Inl ` lambdas' prog \<subseteq> ran (subterm (Inl prog))" (is ?P1)
  and "Inr ` Inl ` calls' prog \<subseteq> ran (subterm (Inl prog))" (is ?P2)
  and "Inr ` Inr ` values' prog \<subseteq> ran (subterm (Inl prog))" (is ?P3)
proof-
{
fix l c v 
have "l \<in> lambdas' prog \<Longrightarrow> Inl l \<in> ran (subterm (Inl prog))"
  and "c \<in> calls' prog \<Longrightarrow> Inr (Inl c) \<in> ran (subterm (Inl prog))"
  and "v \<in> values' prog \<Longrightarrow> Inr (Inr v) \<in> ran (subterm (Inl prog))"
proof(induct rule:lambdas'_calls'_values'.inducts)
case self show ?case by(cases prog, auto simp add:ran_def intro: exI[where x="[]"])
next

case (lamC l vs c)
then obtain pos where "subterm (Inl prog) pos = Some (Inl (Lambda l vs c))" by (auto simp add:ran_def)
thus ?case by (auto intro: ranI[of _ "pos@[0]"] simp add:subterm_comp)
next

case (appD l d ds)
then obtain pos where "subterm (Inl prog) pos = Some (Inr (Inl (App l d ds)))" by (auto simp add:ran_def)
thus ?case by (auto intro: ranI[of _ "pos@[0]"] simp add:subterm_comp)
next

case (appDs l d ds d')
then obtain n and pos
  where "d' = ds ! n"  and "n < length ds"
    and "subterm (Inl prog) pos = Some (Inr (Inl (App l d ds)))"
  by (auto simp add:in_set_conv_nth ran_def)
thus ?case by (auto intro: ranI[of _ "pos@[Suc n]"] simp add:subterm_comp)
next

case (letC l binds c')
then obtain pos where "subterm (Inl prog) pos = Some (Inr (Inl (Let l binds c')))" by (auto simp add:ran_def)
thus ?case by (auto intro: ranI[of _ "pos@[0]"] simp add:subterm_comp)
next

case (letLs l binds c' l')
then obtain bind and pos
  where "l' = snd bind" and "bind \<in> set binds" 
    and "subterm (Inl prog) pos = Some (Inr (Inl (Let l binds c')))"
  by (auto simp add:in_set_conv_nth ran_def)
then obtain n where "l' = snd (binds ! n)" and "n < length binds"
    and "subterm (Inl prog) pos = Some (Inr (Inl (Let l binds c')))"
  by (auto simp add:in_set_conv_nth ran_def)
thus ?case by (auto intro: ranI[of _ "pos@[Suc n]"] simp add:subterm_comp)
next

case (val l)
then obtain pos where "subterm (Inl prog) pos = Some (Inr (Inr (L l)))" by (auto simp add:ran_def)
thus ?case by (auto intro: ranI[of _ "pos@[0]"] simp add:subterm_comp)
qed
}
thus ?P1 and ?P2 and ?P3 by auto
qed

lemma finite_dom_ran:
  assumes "finite (dom m)"
  shows "finite (ran m)"
proof-
  have "Some ` ran m \<subseteq> m `(dom m)"
  proof 
    fix x assume "x\<in> Some ` ran m"
    then obtain v k where "x = Some v" and "x = m k" by (auto simp add:ran_def)
    hence "k \<in> dom m" and "x = m k" by (auto simp add:dom_def)
    thus "x \<in>  m `(dom m)" by auto
  qed
  moreover
  from assms have "finite (m` dom m)" by auto
  ultimately
  have "finite (Some ` ran m)" by (rule finite_subset)
  thus "finite (ran m)" by (auto dest:finite_imageD)
qed

lemma "finite (lambdas' prog)"
proof-
have "dom (subterm (Inl prog)) \<subseteq> Pos prog"
  by (auto dest: subterm_Pos)
thus "finite (lambdas' prog)"
  by (rule finite_imageD[of Inl, OF finite_subset, OF subterm_ran_subsets(1), OF finite_dom_ran, OF finite_subset[OF _ finite_Pos[of prog]]], auto)
qed  

lemma "finite (calls' prog)"
proof-
have "dom (subterm (Inl prog)) \<subseteq> Pos prog"
  by (auto dest: subterm_Pos)
thus "finite (calls' prog)"
  by (rule finite_imageD[of Inl, OF finite_imageD[of Inr], OF finite_subset, OF subterm_ran_subsets(2), OF finite_dom_ran, OF finite_subset[OF _ finite_Pos[of prog]]], auto)
qed  

lemma "finite (values' prog)"
proof-
have "dom (subterm (Inl prog)) \<subseteq> Pos prog"
  by (auto dest: subterm_Pos)
thus "finite (values' prog)"
  by (rule finite_imageD[of Inr, OF finite_imageD[of Inr], OF finite_subset, OF subterm_ran_subsets(3), OF finite_dom_ran, OF finite_subset[OF _ finite_Pos[of prog]]], auto)
qed  


end

