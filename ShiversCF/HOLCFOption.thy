theory HOLCFOption imports HOLCF
begin

instantiation option :: (po) po
begin

fun below_option
 where [simp]: "None \<sqsubseteq> _    = True"
             | "Some _ \<sqsubseteq> None = False"
             | "Some a \<sqsubseteq> Some b = a \<sqsubseteq> b"
print_theorems

lemma [simp,dest]:"x \<sqsubseteq> None \<Longrightarrow> x = None"
by (cases rule:below_option.cases) auto

instance (* I am lazy here\<dots> *)
apply default
apply (case_tac x)
apply auto
apply (case_tac x)
apply auto
apply (case_tac y)
apply auto
apply (case_tac z)
apply auto
apply (auto elim:below_trans)
apply (case_tac x)
apply auto
apply (case_tac y)
apply (auto elim:below_antisym)
done
end

instance option :: (cpo) cpo 
apply default
proof-
  fix S :: "nat \<Rightarrow> 'a option"
  assume "chain S"
  show  "\<exists>x\<Colon>'a option. range S <<| x"
  proof(cases "\<forall>i. S i = None")
  case True
    have "range S <| None" using True by -(rule ub_rangeI,auto)
    moreover
    { fix u :: "'a option"
      assume "range S <| u"
      hence "S 0 \<sqsubseteq> u" by (rule ub_rangeD)
      hence "None \<sqsubseteq> u" using True by auto
    } ultimately
    show "\<exists>x\<Colon>'a option. range S <<| x" by (blast intro:is_lubI)
  next
  case False
  then obtain i where first: "S i \<noteq> None" by blast
  { fix j
    have "j \<ge> i \<Longrightarrow> S j \<noteq> None"
    proof(induct j)
    case 0 thus "S 0 \<noteq> None" using first by simp
    next
    case (Suc j)
      hence "S j \<noteq> None \<or> i = Suc j" apply (cases "i=Suc j")
        by (auto simp del:not_None_eq iff del:not_None_eq)
      moreover
      from `chain S` have "S j \<sqsubseteq> S (Suc j)" by (auto dest: chainE)
      ultimately
      show "S (Suc j) \<noteq> None" using first
       by (auto simp del:not_None_eq iff del:not_None_eq)
    qed
  } hence "\<forall>j. j\<ge>i \<longrightarrow> S j \<noteq> None" by auto

  def S' \<equiv> "\<lambda>j. the (S (i+j))"
  have "chain S'"
  proof(rule chainI)
    fix j
    from `\<forall>j. j\<ge>i \<longrightarrow> S j \<noteq> None` have "S (i+j) \<noteq> None" and "S (i+Suc j) \<noteq> None" by auto
    moreover
    from `chain S` have "S (i+j) \<sqsubseteq> S (i + Suc j)" by (auto dest: chainE)
    ultimately
    show "S' j \<sqsubseteq> S' (Suc j)" unfolding S'_def  by auto
  qed
  then obtain x' where "range S' <<| x'" by (auto dest:cpo)
  
  have "range S <<| Some x'"
  proof(rule is_lubI)
    show "range S <| Some x'"
    proof(rule is_ubI)
      fix x
      assume "x \<in> range S"
      then obtain j where "x = S j" by blast
      show "x \<sqsubseteq> Some x'"
      proof(cases "j \<ge> i")
      case True then obtain j' where "j = i + j'" by (auto iff:le_iff_add)
        hence "S j \<noteq> None" using  `\<forall>j. j\<ge>i \<longrightarrow> S j \<noteq> None` by auto
        then obtain a where "S j = Some a" by auto
        hence "a = S' j'" using `j = i + j'` unfolding S'_def by auto
        hence "a \<sqsubseteq> x'" using `range S' <<| x'` by (auto dest:is_lubD1 ub_rangeD)
        thus "x \<sqsubseteq> Some x'" using `x = S j` and `S j = Some a` by auto
      next
      case False hence "j < i " by auto
        hence "S j \<sqsubseteq> S i" using `chain S` by (auto dest:chain_mono_less)
        from `S i \<noteq> None` obtain a where "S i = Some a" by auto
        hence "a = S' 0"  unfolding S'_def by auto
        hence "a \<sqsubseteq> x'" using `range S' <<| x'` by (auto dest:is_lubD1 ub_rangeD)
        hence "S i \<sqsubseteq> Some x'" using `S i = Some a` by auto
        with `S j \<sqsubseteq> S i` and `x = S j` show "x \<sqsubseteq> Some x'" by (auto dest:below_trans)
     qed
    qed
    next
    fix u :: "'a option"
    assume "range S <| u"
    hence "S i \<sqsubseteq> u" by (auto dest:ub_rangeD)
    with `S i \<noteq> None` have "u \<noteq> None" by (cases u) auto

    have "range S' <| the u"
    proof (rule is_ubI)
      fix x
      assume "x\<in>range S'"
      then obtain j where "x = S' j" by blast
      hence "x = the (S (i+j))" unfolding S'_def by simp
      from `\<forall>j. j\<ge>i \<longrightarrow> S j \<noteq> None` have "S (i+j)\<noteq> None" by auto
      hence "Some x = S (i+j)" using `x = the (S (i+j))` by auto
      with `range S <| u` have "Some x \<sqsubseteq> u" by (auto dest:ub_rangeD)
      thus "x \<sqsubseteq> the u"by (cases u) auto
   qed
   with `range S' <<| x'` have "x' \<sqsubseteq> the u" by (rule is_lub_lub)
   hence "Some x' \<sqsubseteq> Some (the u)" by auto
   thus "Some x' \<sqsubseteq> u" using `u \<noteq> None` by auto
  qed
  thus "\<exists>x. range S <<| x" by auto
  qed
qed

instance option :: (cpo) pcpo 
apply default
apply (rule_tac x=None in exI)
by auto


end
