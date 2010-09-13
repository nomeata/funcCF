theory HOLCFExSV
imports HOLCFExCF
begin


lemma cc_single_valued':
      "\<lbrakk> \<forall>b' \<in> contours_in_ve ve. b' < b
       ; \<forall>b' \<in> contours_in_d d. b' < b
       ; \<forall>d' \<in> set ds. \<forall>b' \<in> contours_in_d d'. b' < b
       \<rbrakk>
       \<Longrightarrow>
       (   single_valued (evalF\<cdot>(Discr (d,ds,ve,b)))
       \<and> (\<forall> lab \<beta> t. ((lab,\<beta>),t) \<in> evalF\<cdot>(Discr (d,ds,ve, b)) \<longrightarrow> (\<exists> b'. b' \<in> ran \<beta> \<and> b \<le> b'))
       )"
  and "\<lbrakk> b \<in> ran \<beta>'
       ; \<forall>b'\<in>ran \<beta>'. b' \<le> b
       ; \<forall>b' \<in> contours_in_ve ve. b' \<le> b
       \<rbrakk>
       \<Longrightarrow>
       (   single_valued (evalC\<cdot>(Discr (c,\<beta>',ve,b)))
       \<and> (\<forall> lab \<beta> t. ((lab,\<beta>),t) \<in> evalC\<cdot>(Discr (c,\<beta>',ve,b)) \<longrightarrow> (\<exists> b'. b' \<in> ran \<beta> \<and> b \<le> b'))
       )"
proof(induct arbitrary:d ds ve b c \<beta>' b' rule:evalF_evalC_induct)
print_cases
case Admissibility show ?case
  (* admissibility *)
  by (intro adm_lemmas adm_prod_split adm_not_conj adm_not_mem adm_single_valued cont2cont)
next
  case Bottom {
    case 1 thus ?case by (auto simp add:mem_def) next
    case 2 thus ?case by (auto simp add:mem_def)
  }
next
  case (Next evalF evalC)
  print_cases
  {
  case (1 d ds ve b)
  show ?case
  proof (cases "(d,ds,ve,b)" rule:fstate_case)
  case (Closure lab' vs c \<beta>')
    hence eq_length: "length vs = length ds" by simp
    have new: "b\<in>ran (\<beta>'(lab' \<mapsto> b))" by simp

    have b_dom_beta: "\<forall>b'\<in> ran (\<beta>'(lab' \<mapsto> b)). b' \<le> b"
    proof fix b' assume "b' \<in> ran (\<beta>'(lab' \<mapsto> b))"
      hence "b' \<in> ran \<beta>' \<or> b' \<le> b" by (auto dest:ran_upd[THEN subsetD])
      thus "b' \<le> b" using  Next.prems(2) Closure by auto
    qed

    from contours_in_ve_upds[OF eq_length Next.prems(1) Next.prems(3)]
    have b_dom_ve: "\<forall>b'\<in>contours_in_ve (ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds)). b' \<le> b"
      by auto

    from Next.hyps(2)[OF new b_dom_beta b_dom_ve, of c]
    show ?thesis using Closure by (auto simp del:fun_upd_apply)
  next
  case (Plus cp i1 i2 cnt)
    have b_dom_d: "\<forall>b'\<in>contours_in_d cnt. b' < nb b cp" using Next.prems(3) and Plus by auto
    have b_dom_ds: "\<forall>d' \<in> set [DI (i1+i2)]. \<forall>b'\<in>contours_in_d d'. b' < nb b cp" by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < nb b cp" using Next.prems(1) by auto
    {
      fix t
      assume "((cp,[cp \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, nb b cp))"
      hence "\<exists>b'. b' \<in> ran [cp \<mapsto> b] \<and> nb b cp \<le> b'"
        by (rule Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct2, rule_format])
      hence False by simp
    }
    with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct1]
    have "single_valued ((evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, nb b cp)))
                      \<union> {((cp, [cp \<mapsto> b]), cnt)})"
      by (auto intro:single_valued_insert)
    moreover
    {
      fix lab \<beta> t
      assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cnt, [DI (i1 + i2)], ve, nb b cp))"
      with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct2, rule_format]
      have "\<exists>b'. b' \<in> ran \<beta> \<and> nb b cp \<le> b'" by auto
      hence "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'" by auto
    }
    ultimately
    show ?thesis using Plus by auto
  next
  case (If_True cp1 cp2 i cntt cntf)
    have b_dom_d: "\<forall>b'\<in>contours_in_d cntt. b' < nb b cp1" using Next.prems(3) and If_True by auto
    have b_dom_ds: "\<forall>d' \<in> set []. \<forall>b'\<in>contours_in_d d'. b' < nb b cp1" by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < nb b cp1" using Next.prems(1) by auto
    {
      fix t
      assume "((cp1,[cp1 \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, nb b cp1))"
      hence "\<exists>b'. b' \<in> ran [cp1 \<mapsto> b] \<and> nb b cp1 \<le> b'"
        by (rule Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct2, rule_format])
      hence False by simp
    }
    with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct1]
    have "single_valued ((evalF\<cdot>(Discr (cntt, [], ve, nb b cp1)))
                       \<union> {((cp1, [cp1 \<mapsto> b]), cntt)})"
      by (auto intro:single_valued_insert)
    moreover
    {
      fix lab \<beta> t
      assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, nb b cp1))"
      with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct2, rule_format]
      have "\<exists>b'. b' \<in> ran \<beta> \<and> nb b cp1 \<le> b'" by auto
      hence "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'" by auto
    }
    ultimately
    show ?thesis using If_True by auto
   next
   case (If_False cp2 cp1 i cntf cntt)
    have b_dom_d: "\<forall>b'\<in>contours_in_d cntt. b' < nb b cp1" using Next.prems(3) and If_False by auto
    have b_dom_ds: "\<forall>d' \<in> set []. \<forall>b'\<in>contours_in_d d'. b' < nb b cp1" by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < nb b cp1" using Next.prems(1) by auto
    {
      fix t
      assume "((cp1,[cp1 \<mapsto> b]), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, nb b cp1))"
      hence "\<exists>b'. b' \<in> ran [cp1 \<mapsto> b] \<and> nb b cp1 \<le> b'"
        by (rule Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct2, rule_format])
      hence False by simp
    }
    with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct1]
    have "single_valued ((evalF\<cdot>(Discr (cntt, [], ve, nb b cp1)))
                       \<union> {((cp1, [cp1 \<mapsto> b]), cntt)})"
      by (auto intro:single_valued_insert)
    moreover
    {
      fix lab \<beta> t
      assume "((lab, \<beta>), t) \<in> evalF\<cdot>(Discr (cntt, [], ve, nb b cp1))"
      with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct2, rule_format]
      have "\<exists>b'. b' \<in> ran \<beta> \<and> nb b cp1 \<le> b'" by auto
      hence "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'" by auto
    }
    ultimately
    show ?thesis using If_False by auto
  next
    case (Stop i)
    thus ?thesis by simp
  qed (auto split:d.split prim.split)
next
  case (2 ve b c \<beta>')
  show ?case
  proof (cases c)
  case (App lab' f vs)
    print_facts

    have prem2': "\<forall>b'\<in>ran \<beta>'. b' < nb b lab'" using Next.prems(2) by auto
    have prem3': "\<forall>b'\<in>contours_in_ve ve. b' < nb b lab'" using Next.prems(3) by auto
    note c_in_e = contours_in_eval[OF prem3' prem2']

    have b_dom_d: "\<forall>b'\<in>contours_in_d (evalV f \<beta>' ve). b' < nb b lab'" by(rule c_in_e)
    have b_dom_ds: "\<forall>d' \<in> set (map (\<lambda>v. evalV v \<beta>' ve) vs). \<forall>b'\<in>contours_in_d d'. b' < nb b lab'"
      using c_in_e by auto
    have b_dom_ve: "\<forall>b' \<in> contours_in_ve ve. b' < nb b lab'" by (rule prem3')

    have new_elem: "\<forall>y. ((lab', \<beta>'), y) \<notin> evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab'))"
    proof(rule allI, rule notI)
      fix y assume e: "((lab', \<beta>'), y) \<in> evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab'))"
      have "\<exists>b'. b' \<in> ran \<beta>' \<and> nb b lab' \<le> b'"
        by(rule Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct2, rule_format, OF e])
      thus False using prem2' by (auto iff:less_le_not_le)
    qed

    from Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct1]
    have "single_valued (evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab'))
                       \<union> {((lab', \<beta>'), evalV f \<beta>' ve)})"
      using new_elem
    by(auto intro:single_valued_insert)
    moreover
    {
      fix lab \<beta> t
      assume "((lab, \<beta>), t) \<in> (evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab'))
                            \<union> {((lab', \<beta>'), evalV f \<beta>' ve)})"
      hence "((lab, \<beta>), t) = ((lab', \<beta>'), evalV f \<beta>' ve)
             \<or> ((lab, \<beta>), t) \<in> (evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab')))"
        by simp
      hence "\<exists>b'. b' \<in> ran \<beta> \<and> b \<le> b'"
      proof
        assume "((lab, \<beta>), t) = ((lab', \<beta>'), evalV f \<beta>' ve)"
        hence "\<beta>' = \<beta>" by simp
        with Next.prems(1)
        show ?thesis by auto
      next
        assume "((lab, \<beta>), t) \<in> (evalF\<cdot>(Discr (evalV f \<beta>' ve, map (\<lambda>v. evalV v \<beta>' ve) vs, ve, nb b lab')))"
        with Next.hyps(1)[OF b_dom_ve b_dom_d b_dom_ds, THEN conjunct2, rule_format]
        have "\<exists>b'. b' \<in> ran \<beta> \<and> nb b lab' \<le> b'" by auto
        thus ?thesis by auto
      qed
    }
    ultimately
    show ?thesis using App by(auto simp add:HOL.Let_def)
  next
  case (Let lab' ls c')
    have prem2': "\<forall>b'\<in>ran (\<beta>'(lab' \<mapsto> nb b lab')). b' \<le> nb b lab'"
    proof
      fix b' assume "b'\<in>ran (\<beta>'(lab' \<mapsto> nb b lab'))"
      hence "b' \<in> ran \<beta>' \<or> b' = nb b lab'" by (auto dest:ran_upd[THEN subsetD])
      thus "b' \<le> nb b lab'" using  Next.prems(2) by auto
    qed
    have prem3': "\<forall>b'\<in>contours_in_ve ve. b' \<le> nb b lab'" using Next.prems(3)
      by auto

    note c_in_e = contours_in_eval[OF prem3' prem2']
    note c_in_ve' = contours_in_ve_upds_binds[OF prem3' prem2']

    have b_dom_ve: "\<forall>b' \<in> contours_in_ve (ve ++ map_of (map (\<lambda>(v,l). ((v,nb b lab'), evalV (L l) ((\<beta>'(lab' \<mapsto> nb b lab'))) ve)) ls)). b' \<le> nb b lab'"
      by (rule c_in_ve')
    have b_dom_beta: "\<forall>b'\<in>ran (\<beta>'(lab' \<mapsto> nb b lab')). b' \<le> nb b lab'" by (rule prem2')
    have new: "nb b lab' \<in> ran (\<beta>'(lab' \<mapsto> nb b lab'))" by simp
      
    from Next.hyps(2)[OF new b_dom_beta b_dom_ve, of c']
    show ?thesis using Let
      by(auto simp add:HOL.Let_def simp del: fun_upd_apply)blast
  qed
 }
qed
print_theorems (* Unselect-blocker *)

lemma "single_valued (evalCPS prog)"
unfolding evalCPS_def
by ((subst HOL.Let_def)+, rule cc_single_valued'[THEN conjunctionD1], auto)
end