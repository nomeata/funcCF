theory CPSUtils
imports CPSScheme
begin

fun lambdas :: "lambda \<Rightarrow> lambda set"
and lambdasC :: "call \<Rightarrow> lambda set"
and lambdasV :: "val \<Rightarrow> lambda set"
where "lambdas  (Lambda l vs c) = ({Lambda l vs c} \<union> lambdasC c)"
    | "lambdasC (App l d ds) = lambdasV d \<union> (UNION (set ds) lambdasV)"
    | "lambdasC (Let l binds c') = (UNION (set binds) (\<lambda>(_,l). lambdas l)
                                    \<union> lambdasC c')"
    | "lambdasV (L l) = lambdas l"
    | "lambdasV _     = {}"

fun calls :: "lambda \<Rightarrow> call set"
and callsC :: "call \<Rightarrow> call set"
and callsV :: "val \<Rightarrow> call set"
where "calls  (Lambda l vs c) = callsC c"
    | "callsC (App l d ds) = {App l d ds} \<union> callsV d \<union> (UNION (set ds) callsV)"
    | "callsC (Let l binds c') = {Let l binds c'}
                                    \<union> (UNION (set binds) (\<lambda>(_,l). calls l)
                                    \<union> callsC c')"
    | "callsV (L l) = calls l"
    | "callsV _     = {}"

lemma finite_lambdas[simp]: "finite (lambdas l)" and "finite (lambdasC c)" "finite (lambdasV v)"
by (induct rule: lambdas_lambdasC_lambdasV.induct, auto, blast)

lemma finite_calls[simp]: "finite (calls l)" and "finite (callsC c)" "finite (callsV v)"
by (induct rule: calls_callsC_callsV.induct, auto, blast)

fun vars :: "lambda \<Rightarrow> var set"
and varsC :: "call \<Rightarrow> var set"
and varsV :: "val \<Rightarrow> var set"
where "vars (Lambda _ vs c) = set vs \<union> varsC c"
    | "varsC (App _ a as) = varsV a \<union> UNION (set as) varsV"
    | "varsC (Let _ binds c') = UNION (set binds) (\<lambda>(v,l). {v} \<union> vars l) \<union> varsC c'"
    | "varsV (L l) = vars l"
    | "varsV (R _ v) = {v}"
    | "varsV _  = {}"

lemma finite_vars[simp]: "finite (vars l)" and "finite (varsC c)" "finite (varsV v)"
by (induct rule: vars_varsC_varsV.induct, auto, blast)

fun label :: "lambda + call \<Rightarrow> label"
where "label (Inl (Lambda l _ _)) = l"
    | "label (Inr (App l _ _)) = l"
    | "label (Inr (Let l _ _)) = l"

fun labels :: "lambda \<Rightarrow> label set"
and labelsC :: "call \<Rightarrow> label set"
and labelsV :: "val \<Rightarrow> label set"
where "labels (Lambda l vs c) = {l} \<union> labelsC c"
    | "labelsC (App l a as) = {l} \<union> UNION (set as) labelsV"
    | "labelsC (Let _ binds c') = UNION (set binds) (\<lambda>(v,l). labels l) \<union> labelsC c'"
    | "labelsV (L l) = labels l"
    | "labelsV (R l _) = {l}"
    | "labelsV _  = {}"

lemma finite_labels[simp]: "finite (labels l)" and "finite (labelsC c)" "finite (labelsV v)"
by (induct rule: labels_labelsC_labelsV.induct, auto, blast)


definition nList :: "'a set => nat => 'a list set"
where "nList A n \<equiv> {l. set l \<le> A \<and> length l = n}"

lemma finite_nList[intro]:
  assumes finA: "finite A"
  shows "finite (nList A n)"
proof(induct n)
case 0 thus ?case by (simp add:nList_def) next
case (Suc n) hence finn: "finite (nList (A) n)" by simp
  have "nList A (Suc n) = (split op #) ` (A \<times> nList A n)" (is "?lhs = ?rhs")
  proof(rule subset_antisym[OF subsetI subsetI])
  fix l assume "l \<in> ?lhs" thus "l \<in> ?rhs"
    by (cases l, auto simp add:nList_def)
  next
  fix l assume "l \<in> ?rhs" thus "l \<in> ?lhs"
    by (auto simp add:nList_def)
  qed
  thus "finite ?lhs" using finA and finn
    by auto
qed

definition NList :: "'a set => nat set => 'a list set"
where "NList A N \<equiv> \<Union> n \<in> N. nList A n"

lemma finite_Nlist[intro]:
  "\<lbrakk> finite A; finite N \<rbrakk> \<Longrightarrow> finite (NList A N)"
unfolding NList_def using assms by auto

definition call_list_lengths
  where "call_list_lengths p = (\<lambda>c. case c of (App _ _ ds) \<Rightarrow> length ds | _ \<Rightarrow> 0) ` calls p"

lemma finite_call_list_lengths[simp]: "finite (call_list_lengths p)"
  unfolding call_list_lengths_def by auto

end