theory HOLCFAbsCF
  imports CPSUtils HOLCF HOLCFUtils List_Cpo CPSScheme Utils HOLCFExCF SetMap
begin

class contour = discrete_cpo +
  fixes nb :: "'a \<Rightarrow> label \<Rightarrow> 'a"
    and initial_contour :: 'a
    and abs_cnt :: "HOLCFExCF.contour \<Rightarrow> 'a"
  assumes abs_cnt_nb: "abs_cnt b \<sqsubseteq> b_a \<Longrightarrow> abs_cnt (HOLCFExCF.nb b lab) \<sqsubseteq> nb b_a lab"

instantiation unit :: contour
begin
definition "nb _ _ = ()"
definition "initial_contour = ()"
definition "abs_cnt _ = ()"
instance by default auto
end

types 'c benv = "label \<rightharpoonup> 'c"
      'c closure = "lambda \<times> 'c benv"

datatype 'c proc = PC "'c closure"
                 | PP prim
                 | Stop

instantiation proc :: (type)discrete_cpo
begin
definition [simp]: "(x::'a proc) \<sqsubseteq> y \<longleftrightarrow> x = y"
instance by default simp
end

instantiation option :: (type)discrete_cpo
begin
definition [iff]: "(x::'a option) \<sqsubseteq> y \<longleftrightarrow> x = y"
instance by default simp
end

types 'c d = "'c proc set"

types 'c venv = "var \<times> 'c \<Rightarrow> 'c d"

text {* Abstraction functions *}

definition abs_benv :: "HOLCFExCF.benv \<Rightarrow> 'c::contour benv"
  where "abs_benv \<beta> = Option.map abs_cnt \<circ> \<beta>"

primrec abs_closure :: "HOLCFExCF.closure \<Rightarrow> 'c::contour closure"
  where "abs_closure (l,\<beta>) = (l,abs_benv \<beta>)"

primrec abs_d :: "HOLCFExCF.d \<Rightarrow> 'c::contour d"
  where "abs_d (DI _) = {}"
      | "abs_d (DP p) = {PP p}"
      | "abs_d (DC cl) = {PC (abs_closure cl)}"
      | "abs_d (HOLCFExCF.Stop) = {Stop}"

lemma contents_is_Proc:
  assumes "isProc cnt"
  shows "contents (abs_d cnt) \<in> abs_d cnt"
using assms by (cases cnt)auto

definition abs_venv :: "HOLCFExCF.venv \<Rightarrow> 'c::contour venv"
  where "abs_venv ve = (\<lambda>(v,b_a). \<Union>{(case ve (v,b) of Some d \<Rightarrow> abs_d d | None \<Rightarrow> {})| b . abs_cnt b = b_a})"

fun evalV :: "val \<Rightarrow> 'c benv \<Rightarrow> 'c venv \<Rightarrow> 'c d"
  where "evalV (C _ i) \<beta> ve = {}"
  |     "evalV (P prim) \<beta> ve = {PP prim}"
  |     "evalV (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> ve (var,l)
            | None \<Rightarrow> {})"
  |     "evalV (L lam) \<beta> ve = {PC (lam, \<beta>)}"

types 'c ccache = "((label \<times> 'c benv) \<times> 'c proc) set"
      'c ans = "'c ccache"

definition abs_ccache :: "HOLCFExCF.ccache \<Rightarrow> 'c::contour ccache"
  where "abs_ccache cc = (\<Union>((c,\<beta>),d) \<in> cc . {((c,abs_benv \<beta>), p) | p . p\<in>abs_d d})"
(* equivalent, but I already have cont2cont for UNION
  where "abs_ccache cc = { ((c,abs_benv \<beta>),p) | c \<beta> p d . ((c,\<beta>),d) \<in> cc \<and> p \<in> abs_d d}" *)

types 'c fstate = "('c proc \<times> 'c d list \<times> 'c venv \<times> 'c)"
      'c cstate = "(call \<times> 'c benv \<times> 'c venv \<times> 'c)"

fun abs_fstate :: "HOLCFExCF.fstate \<Rightarrow> 'c::contour fstate"
  where "abs_fstate (d,ds,ve,b) = (contents (abs_d d), map abs_d ds, abs_venv ve, abs_cnt b)"

fun abs_cstate :: "HOLCFExCF.cstate \<Rightarrow> 'c::contour cstate"
  where "abs_cstate (c,\<beta>,ve,b) = (c, abs_benv \<beta>, abs_venv ve, abs_cnt b)"

lemma cont2cont_lambda_case [simp, cont2cont]:
  assumes "\<And>a b c. cont (\<lambda>x. f x a b c)"
  shows "cont (\<lambda>x. lambda_case (f x) l)"
using assms
by (cases l) auto

lemma cont2cont_proc_case [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x y)"
     and  "\<And>y. cont (\<lambda>x. f2 x y)"
     and  "cont (\<lambda>x. f3 x)"
  shows "cont (\<lambda>x. proc_case (f1 x) (f2 x) (f3 x) d)"
using assms
by (cases d) auto

lemma cont2cont_call_case [simp, cont2cont]:
  assumes "\<And>a b c. cont (\<lambda>x. f1 x a b c)"
     and  "\<And>a b c. cont (\<lambda>x. f2 x a b c)"
  shows "cont (\<lambda>x. call_case (f1 x) (f2 x) c)"
using assms
by (cases c) auto

lemma cont2cont_prim_case [simp, cont2cont]:
  assumes "\<And>y. cont (\<lambda>x. f1 x y)"
     and  "\<And>y z. cont (\<lambda>x. f2 x y z)"
  shows "cont (\<lambda>x. prim_case (f1 x) (f2 x) p)"
using assms
by (cases p) auto

lemma abs_venv_union: "\<And> ve1 ve2. abs_venv (ve1 ++ ve2) \<sqsubseteq> smap_union (abs_venv ve1) (abs_venv ve2)"
  by (subst below_fun_def, auto simp add: sqsubset_is_subset abs_venv_def smap_union_def, split option.split_asm, auto)

lemma abs_venv_map_of: "abs_venv (map_of (rev l)) \<sqsubseteq> smap_Union (map (\<lambda>(v,k). abs_venv [v \<mapsto> k]) l)"
proof (induct l)
  case Nil show ?case unfolding abs_venv_def by (subst below_fun_def, auto simp: sqsubset_is_subset) next
  case (Cons a l)
    obtain v k where "a=(v,k)" by (rule prod.exhaust)
    hence "abs_venv (map_of (rev (a # l))) \<sqsubseteq> (smap_union (abs_venv [v \<mapsto> k]) (abs_venv (map_of (rev l))) :: 'a venv)"
      by (auto intro: abs_venv_union)
    also
    have "\<dots> \<sqsubseteq> smap_union (abs_venv [v \<mapsto> k]) (smap_Union (map (\<lambda>(v,k). abs_venv [v  \<mapsto> k]) l))"
      by (rule smap_union_mono[OF below_refl Cons])
    also
    have "\<dots> = smap_Union (abs_venv [v \<mapsto> k] # map (\<lambda>(v,k). abs_venv [v \<mapsto> k]) l)"
      by (rule smap_Union_union)
    also
    have "\<dots> = smap_Union (map (\<lambda>(v,k). abs_venv [v \<mapsto> k]) (a#l))"
      using `a = (v,k)`
      by auto 
    finally
    show ?case .
qed

lemma abs_venv_singleton: "abs_venv [(v,b) \<mapsto> d] = smap_singleton (v,abs_cnt b) (abs_d d)"
  by (rule ext, auto simp add:abs_venv_def smap_singleton_def smap_empty_def)

lemma abs_ccache_union: "abs_ccache (c1 \<union> c2) \<sqsubseteq> abs_ccache c1 \<union> abs_ccache c2"
  unfolding abs_ccache_def by (auto simp add:sqsubset_is_subset)

lemma [simp]: "abs_ccache {} = {}" unfolding abs_ccache_def by auto

lemma abs_cache_singleton [simp]: "abs_ccache {((c,\<beta>),d)} = {((c, abs_benv \<beta>), p) |p. p \<in> abs_d d}"
  unfolding abs_ccache_def by simp

lemma abs_d_evalV:
  assumes "abs_venv ve \<sqsubseteq> ve_a"
  shows "abs_d (HOLCFExCF.evalV f \<beta> ve) \<subseteq> HOLCFAbsCF.evalV f (abs_benv \<beta>) ve_a"
proof(cases f)
case (R _ v)
  from assms have assm': "\<And>v b. option_case {} abs_d (ve (v,b)) \<subseteq> ve_a (v,abs_cnt b)"
    by (subst (asm) less_fun_def, auto simp add:abs_venv_def sqsubset_is_subset elim!:allE)
  show ?thesis
    proof(cases "\<beta> (binder v)")
    case None thus ?thesis using R by auto next
    case (Some b)
      thus ?thesis using R assm'[of v b]
         by (auto simp add:abs_benv_def split:option.split)
  qed
qed auto

lemma lemma7:
  assumes "abs_venv ve \<sqsubseteq> ve_a"
  shows "abs_d (HOLCFExCF.evalV a \<beta> ve) \<sqsubseteq> evalV a (abs_benv \<beta>) ve_a"
proof(cases a)
case C thus ?thesis by simp next
case P thus ?thesis by simp next
case (L closure) thus ?thesis by simp next
case (R lab v)
  show ?thesis
  proof (cases v)
  case (Pair vn vb)
    show ?thesis
    proof (cases "\<beta> (binder v)")
    case None thus ?thesis using R by auto next
    case (Some cnt) note Some' = Some
      show ?thesis
      proof (cases "ve (v,cnt)")
      case None  thus ?thesis using R and Some by auto next
      case (Some d)
        have "abs_d (HOLCFExCF.evalV a \<beta> ve) \<subseteq> abs_venv ve (v, abs_cnt cnt)"
          using Some Some' R unfolding abs_venv_def by auto
        also
        have "evalV a (abs_benv \<beta>) ve_a = ve_a (v,abs_cnt cnt)"
          using Some' R unfolding abs_benv_def by simp
        hence "abs_venv ve (v, abs_cnt cnt) \<subseteq> evalV a (abs_benv \<beta>) ve_a"
          using assms and Pair by (subst (asm) less_fun_def, simp add:sqsubset_is_subset)
        finally
        show ?thesis by (auto iff:sqsubset_is_subset)
      qed
    qed
  qed
qed

fixrec   evalF :: "'c::contour fstate discr \<rightarrow> 'c ans"
     and evalC :: "'c::contour cstate discr \<rightarrow> 'c ans"
  where "evalF\<cdot>fstate = (case undiscr fstate of
             (PC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = smap_union ve (smap_Union (map (\<lambda>(v,a). smap_singleton (v,b) a) (zip vs as)))
                     in evalC\<cdot>(Discr (c,\<beta>',ve',b))
                else \<bottom>)
            | (PP (Plus c),[_,_,cnts],ve,b) \<Rightarrow>
                     let b' = nb b c;
                         \<beta>  = [c \<mapsto> b]
                     in (\<Union>cnt\<in>cnts. evalF\<cdot>(Discr (cnt,[{}],ve,b')))
                        \<union>
                        {((c, \<beta>), cont) | cont . cont \<in> cnts}
            | (PP (prim.If ct cf),[_, cntts, cntfs],ve,b) \<Rightarrow>
                  ((   let b' = nb b ct;
                            \<beta> = [ct \<mapsto> b]
                        in (\<Union>cnt\<in>cntts . evalF\<cdot>(Discr (cnt,[],ve,b')))
                           \<union>{((ct, \<beta>), cnt) | cnt . cnt \<in> cntts}
                   )\<union>(
                       let b' = nb b cf;
                            \<beta> = [cf \<mapsto> b]
                        in (\<Union>cnt\<in>cntfs . evalF\<cdot>(Discr (cnt,[],ve,b')))
                           \<union>{((cf, \<beta>), cnt) | cnt . cnt \<in> cntfs}
                   ))
            | (Stop,[_],_,_) \<Rightarrow> {}
            | _ \<Rightarrow> \<bottom>
        )"
      | "evalC\<cdot>cstate = (case undiscr cstate of
             (App lab f vs,\<beta>,ve,b) \<Rightarrow>
                 let fs = evalV f \<beta> ve;
                     as = map (\<lambda>v. evalV v \<beta> ve) vs;
                     b' = nb b lab
                  in (\<Union>f' \<in> fs. evalF\<cdot>(Discr (f',as,ve,b')))
                     \<union>{((lab, \<beta>),f') | f' . f'\<in> fs}
            | (Let lab ls c',\<beta>,ve,b) \<Rightarrow>
                 let b' = nb b lab;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                     ve' = smap_union ve (smap_Union (map (\<lambda>(v,l). smap_singleton (v,b') (evalV (L l) \<beta>' ve)) ls))
                 in evalC\<cdot>(Discr (c',\<beta>',ve',b'))
        )"

print_theorems
lemmas evalF_evalC_induct = evalF_evalC.induct[case_names Admissibility Bottom Next]

fun evalF_cases
 where "evalF_cases (PC (Lambda lab vs c, \<beta>)) as ve b = undefined"
     | "evalF_cases (PP (Plus cp)) [a1, a2, cnt] ve b = undefined"
     | "evalF_cases (PP (prim.If cp1 cp2)) [v,cntt,cntf] ve b = undefined"
     | "evalF_cases  Stop [v] ve b = undefined"

lemmas fstate_case = evalF_cases.cases[
  OF case_split, of _ "\<lambda>_ vs _ _ as _ _ . length vs = length as",
  case_names "Closure" "Closure_inv" "Plus" "If" "Stop"]

lemma cont2cont_abs_ccache[cont2cont,simp]:
  assumes "cont f"
  shows "cont (\<lambda>x. abs_ccache(f x))"
unfolding abs_ccache_def
using assms
by (rule cont2cont)(rule cont_const)

lemma lemma89:
 shows "abs_fstate fstate \<sqsubseteq> (fstate_a::'c::contour fstate) \<Longrightarrow> abs_ccache (HOLCFExCF.evalF\<cdot>(Discr fstate)) \<sqsubseteq> evalF\<cdot>(Discr fstate_a)"
   and "abs_cstate cstate \<sqsubseteq> (cstate_a::'c::contour cstate) \<Longrightarrow> abs_ccache (HOLCFExCF.evalC\<cdot>(Discr cstate)) \<sqsubseteq> evalC\<cdot>(Discr cstate_a)" 
proof(induct arbitrary: fstate fstate_a cstate cstate_a rule: HOLCFExCF.evalF_evalC_induct)
print_cases
case Admissibility show ?case
  by (intro adm_lemmas adm_prod_split adm_not_conj adm_not_mem adm_single_valued cont2cont)
next
case Bottom {
  case 1 show ?case by simp next
  case 2 show ?case by simp next
}
next
case (Next evalF evalC) {
  case 1 
  obtain d ds ve b where fstate: "fstate = (d,ds,ve,b)" 
    by (cases fstate, auto)
  moreover
  obtain proc ds_a ve_a b_a where fstate_a: "fstate_a = (proc,ds_a,ve_a,b_a)" 
    by (cases fstate_a, auto)
  ultimately
  have abs_d: "contents (abs_d d) = proc"
   and abs_ds: "map abs_d ds \<sqsubseteq> ds_a"
   and abs_ve: "abs_venv ve \<sqsubseteq> ve_a"
   and abs_b: "abs_cnt b \<sqsubseteq> b_a"
  using 1 by auto

  from abs_ds have dslength: "length ds = length ds_a" by (auto dest: below_same_length)

  from fstate fstate_a abs_d abs_ds abs_ve abs_ds dslength
  show ?case
  proof(cases fstate rule:HOLCFExCF.fstate_case, auto simp del:evalF.simps evalC.simps set_map)
  fix \<beta> and lab and vs:: "var list" and c
  assume ds_a_length: "length vs = length ds_a"

  have "abs_benv (\<beta>(lab \<mapsto> b)) \<sqsubseteq> (abs_benv \<beta>) (lab \<mapsto> b_a)"
    unfolding below_fun_def and abs_benv_def using abs_b
    by auto
  moreover

  { have "abs_venv (ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds))
          \<sqsubseteq> smap_union (abs_venv ve) (abs_venv (map_of (rev (zip (map (\<lambda>v. (v, b)) vs) ds))))"
      unfolding map_upds_def by (intro abs_venv_union)
    also
    have "\<dots> \<sqsubseteq> smap_union ve_a (smap_Union (map (\<lambda>(v,k). abs_venv [v \<mapsto> k]) (zip (map (\<lambda>v. (v, b)) vs) ds)))"
      by (rule smap_union_mono[OF abs_ve abs_venv_map_of])
    also
    have "\<dots> = smap_union ve_a (smap_Union (map (\<lambda>(v,y). abs_venv [(v,b) \<mapsto> y]) (zip vs ds)))"
      by (auto simp add: zip_map1 o_def split_def)
    also
    have "\<dots> \<sqsubseteq> smap_union ve_a (smap_Union (map (\<lambda>(v,y). smap_singleton (v, b_a) y) (zip vs ds_a)))"
    proof-
      from abs_b abs_ds
      have"list_all2 op \<sqsubseteq> (map (\<lambda>(v, y). abs_venv [(v, b) \<mapsto> y]) (zip vs ds))
                          (map (\<lambda>(v, y). smap_singleton (v, b_a) y) (zip vs ds_a))"
      by (auto simp add: abs_venv_singleton below_list_def list_all2_conv_all_nth intro:smap_singleton_mono list_all2I)
      thus ?thesis
        by(rule smap_union_mono[OF below_refl smap_Union_mono])
    qed
    finally
    have "abs_venv (ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds))
          \<sqsubseteq> smap_union ve_a (smap_Union (map (\<lambda>(v,y). smap_singleton (v, b_a) y) (zip vs ds_a)))".
  }
  ultimately
  have prem: "abs_cstate (c, \<beta>(lab \<mapsto> b), ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds), b)
        \<sqsubseteq> (c, abs_benv \<beta>(lab \<mapsto> b_a), smap_union ve_a (smap_Union(map (\<lambda>(v, y). smap_singleton (v, b_a) y) (zip vs ds_a))), b_a)"
    using abs_b
    by(auto simp only:Pair_below_iff abs_cstate.simps)

  show "abs_ccache (evalC\<cdot>(Discr (c, \<beta> (lab \<mapsto> b), ve(map (\<lambda>v. (v, b)) vs [\<mapsto>] ds), b)))
        \<sqsubseteq> HOLCFAbsCF.evalF\<cdot>(Discr (PC (Lambda lab vs c, abs_benv \<beta>), ds_a, ve_a, b_a))" 
  using Next.hyps(2)[OF prem] ds_a_length
  by (subst HOLCFAbsCF.evalF.simps, simp del:HOLCFAbsCF.evalF.simps HOLCFAbsCF.evalC.simps)

  next
  fix lab a1 a2 cnt
  assume "isProc cnt"
  assume abs_ds': "[{}, {}, abs_d cnt] \<sqsubseteq> ds_a"
  then obtain a1_a a2_a cnt_a where ds_a: "ds_a = [a1_a, a2_a, cnt_a]" and abs_cnt: "abs_d cnt \<sqsubseteq> cnt_a"
    using below_same_length[OF abs_ds']
    by (cases ds_a rule:list.exhaust[OF _ list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"],  of _ _ "\<lambda>_ x. x"]) auto
  
  have new_elem: "abs_ccache {((lab, [lab \<mapsto> b]), cnt)} \<sqsubseteq> {((lab, [lab \<mapsto> b_a]), cont) |cont. cont \<in> cnt_a}"
    using abs_cnt and abs_b by (auto simp add:sqsubset_is_subset abs_benv_def)

  have prem: "abs_fstate (cnt, [DI (a1 + a2)], ve, HOLCFExCF.nb b lab) \<sqsubseteq>
              (contents (abs_d cnt), [{}], ve_a, contour_class.nb b_a lab)"
    using abs_ve and abs_cnt_nb[OF abs_b]
    by (simp)
  have "abs_ccache (evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, HOLCFExCF.nb b lab)))
       \<sqsubseteq> HOLCFAbsCF.evalF\<cdot>(Discr (contents (abs_d cnt), [{}], ve_a, contour_class.nb b_a lab))"
    by (rule Next.hyps(1)[OF prem])
  also have "\<dots> \<sqsubseteq> (\<Union>cnt\<in>cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [{}], ve_a, contour_class.nb b_a lab)))"
    using abs_cnt
    by (auto intro: contents_is_Proc[OF `isProc cnt`] simp del: evalF.simps simp add:sqsubset_is_subset)
  finally
  have old_elems: "abs_ccache (evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, HOLCFExCF.nb b lab)))
       \<sqsubseteq> (\<Union>cnt\<in>cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [{}], ve_a, contour_class.nb b_a lab)))".
   
  have "abs_ccache ((evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, HOLCFExCF.nb b lab)))
          \<union> {((lab, [lab \<mapsto> b]), cnt)})
        \<sqsubseteq> abs_ccache ((evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, HOLCFExCF.nb b lab))))
          \<union> abs_ccache {((lab, [lab \<mapsto> b]), cnt)}"
    by (rule abs_ccache_union)
  also
  have "\<dots> \<sqsubseteq>
        (\<Union>cnt\<in>cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [{}], ve_a, contour_class.nb b_a lab)))
        \<union> {((lab, [lab \<mapsto> b_a]), cont) |cont. cont \<in> cnt_a}"
    by (rule Un_mono_sq[OF old_elems new_elem])
  finally
  show "abs_ccache (insert ((lab, [lab \<mapsto> b]), cnt)
                   (evalF\<cdot>(Discr (cnt, [DI (a1 + a2)], ve, HOLCFExCF.nb b lab))))
        \<sqsubseteq> HOLCFAbsCF.evalF\<cdot>(Discr (PP (prim.Plus lab), ds_a, ve_a, b_a))"
    using ds_a by (subst HOLCFAbsCF.evalF.simps)(auto simp del:HOLCFAbsCF.evalF.simps)
  next

  fix ct cf v cntt cntf
  assume "isProc cntt" 
  assume "isProc cntf"
  assume abs_ds': "[{}, abs_d cntt, abs_d cntf] \<sqsubseteq> ds_a"
  then obtain v_a cntt_a cntf_a where ds_a: "ds_a = [v_a, cntt_a, cntf_a]"
                              and abs_cntt: "abs_d cntt \<sqsubseteq> cntt_a"
                              and abs_cntf: "abs_d cntf \<sqsubseteq> cntf_a"
    using below_same_length[OF abs_ds']
    by (cases ds_a rule:list.exhaust[OF _ list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"],  of _ _ "\<lambda>_ x. x"])auto

  let ?c = "ct::label" and ?cnt = cntt and ?cnt_a = cntt_a
  
  have new_elem: "abs_ccache {((?c, [?c \<mapsto> b]), ?cnt)} \<sqsubseteq> {((?c, [?c \<mapsto> b_a]), cont) |cont. cont \<in> ?cnt_a}"
    using abs_cntt and abs_cntf and abs_b by (auto simp add:sqsubset_is_subset abs_benv_def)

  have prem: "abs_fstate (?cnt, [], ve, HOLCFExCF.nb b ?c) \<sqsubseteq>
              (contents (abs_d ?cnt), [], ve_a, contour_class.nb b_a ?c)"
    using abs_ve and abs_cnt_nb[OF abs_b]
    by (simp)
  have "abs_ccache (evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c)))
       \<sqsubseteq> HOLCFAbsCF.evalF\<cdot>(Discr (contents (abs_d ?cnt), [], ve_a, contour_class.nb b_a ?c))"
    by (rule Next.hyps(1)[OF prem])
  also have "\<dots> \<sqsubseteq> (\<Union>cnt\<in>?cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a ?c)))"
    using abs_cntt and abs_cntf
    by (auto intro: contents_is_Proc[OF `isProc ?cnt`] simp del: evalF.simps simp add:sqsubset_is_subset)

  finally
  have old_elems: "abs_ccache (evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c)))
       \<sqsubseteq> (\<Union>cnt\<in>?cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a ?c)))".

  have "abs_ccache ((evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c)))
          \<union> {((?c, [?c \<mapsto> b]), ?cnt)})
        \<sqsubseteq> abs_ccache ((evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c))))
          \<union> abs_ccache {((?c, [?c \<mapsto> b]), ?cnt)}"
    by (rule abs_ccache_union)
  also
  have "\<dots> \<sqsubseteq>
        (\<Union>cnt\<in>?cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a ?c)))
        \<union> {((?c, [?c \<mapsto> b_a]), cont) |cont. cont \<in> ?cnt_a}"
    by (rule Un_mono_sq[OF old_elems new_elem])
  also
  have "\<dots> \<sqsubseteq> 
        ((\<Union>cnt\<in>cntt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a ct)))
          \<union> {((ct, [ct \<mapsto> b_a]), cont) |cont. cont \<in> cntt_a})
      \<union> ((\<Union>cnt\<in>cntf_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a cf)))
          \<union> {((cf, [cf \<mapsto> b_a]), cont) |cont. cont \<in> cntf_a})"
    by (rule subst[OF sqsubset_is_subset[THEN sym],of "\<lambda>x. x",OF Un_upper1]
       |rule subst[OF sqsubset_is_subset[THEN sym],of "\<lambda>x. x",OF Un_upper2])
  finally
  show "abs_ccache (insert ((?c, [?c \<mapsto> b]), ?cnt)
             (evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c)))) \<sqsubseteq>
          HOLCFAbsCF.evalF\<cdot>(Discr (PP (prim.If ct cf), ds_a, ve_a, b_a))" 
    using ds_a by (subst HOLCFAbsCF.evalF.simps)(auto simp del:HOLCFAbsCF.evalF.simps)
  next
  fix ct cf cntt cntf
  assume "isProc cntt" 
  assume "isProc cntf"
  assume abs_ds': "[{}, abs_d cntt, abs_d cntf] \<sqsubseteq> ds_a"
  then obtain v_a cntt_a cntf_a where ds_a: "ds_a = [v_a, cntt_a, cntf_a]"
                              and abs_cntt: "abs_d cntt \<sqsubseteq> cntt_a"
                              and abs_cntf: "abs_d cntf \<sqsubseteq> cntf_a"
    using below_same_length[OF abs_ds']
    by (cases ds_a rule:list.exhaust[OF _ list.exhaust[OF _ list.exhaust, of _ _ "\<lambda>_ x. x"],  of _ _ "\<lambda>_ x. x"])auto

  let ?c = "cf::label" and ?cnt = cntf and ?cnt_a = cntf_a
  
  have new_elem: "abs_ccache {((?c, [?c \<mapsto> b]), ?cnt)} \<sqsubseteq> {((?c, [?c \<mapsto> b_a]), cont) |cont. cont \<in> ?cnt_a}"
    using abs_cntt and abs_cntf and abs_b by (auto simp add:sqsubset_is_subset abs_benv_def)

  have prem: "abs_fstate (?cnt, [], ve, HOLCFExCF.nb b ?c) \<sqsubseteq>
              (contents (abs_d ?cnt), [], ve_a, contour_class.nb b_a ?c)"
    using abs_ve and abs_cnt_nb[OF abs_b]
    by (simp)
  have "abs_ccache (evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c)))
       \<sqsubseteq> HOLCFAbsCF.evalF\<cdot>(Discr (contents (abs_d ?cnt), [], ve_a, contour_class.nb b_a ?c))"
    by (rule Next.hyps(1)[OF prem])
  also have "\<dots> \<sqsubseteq> (\<Union>cnt\<in>?cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a ?c)))"
    using abs_cntt and abs_cntf
    by (auto intro: contents_is_Proc[OF `isProc ?cnt`] simp del: evalF.simps simp add:sqsubset_is_subset)

  finally
  have old_elems: "abs_ccache (evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c)))
       \<sqsubseteq> (\<Union>cnt\<in>?cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a ?c)))".

  have "abs_ccache ((evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c)))
          \<union> {((?c, [?c \<mapsto> b]), ?cnt)})
        \<sqsubseteq> abs_ccache ((evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c))))
          \<union> abs_ccache {((?c, [?c \<mapsto> b]), ?cnt)}"
    by (rule abs_ccache_union)
  also
  have "\<dots> \<sqsubseteq>
        (\<Union>cnt\<in>?cnt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a ?c)))
        \<union> {((?c, [?c \<mapsto> b_a]), cont) |cont. cont \<in> ?cnt_a}"
    by (rule Un_mono_sq[OF old_elems new_elem])
  also
  have "\<dots> \<sqsubseteq> 
        ((\<Union>cnt\<in>cntt_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a ct)))
          \<union> {((ct, [ct \<mapsto> b_a]), cont) |cont. cont \<in> cntt_a})
      \<union> ((\<Union>cnt\<in>cntf_a. HOLCFAbsCF.evalF\<cdot>(Discr (cnt, [], ve_a, contour_class.nb b_a cf)))
          \<union> {((cf, [cf \<mapsto> b_a]), cont) |cont. cont \<in> cntf_a})"
    by (rule subst[OF sqsubset_is_subset[THEN sym],of "\<lambda>x. x",OF Un_upper1]
       |rule subst[OF sqsubset_is_subset[THEN sym],of "\<lambda>x. x",OF Un_upper2])
  finally
  show "abs_ccache (insert ((?c, [?c \<mapsto> b]), ?cnt)
             (evalF\<cdot>(Discr (?cnt, [], ve, HOLCFExCF.nb b ?c)))) \<sqsubseteq>
          HOLCFAbsCF.evalF\<cdot>(Discr (PP (prim.If ct cf), ds_a, ve_a, b_a))" 
    using ds_a by (subst HOLCFAbsCF.evalF.simps)(auto simp del:HOLCFAbsCF.evalF.simps)
 qed
next
case 2
  obtain c \<beta> ve b where cstate: "cstate = (c,\<beta>,ve,b)" 
    by (cases cstate, auto)
  moreover
  obtain c_a \<beta>_a ds_a ve_a b_a where cstate_a: "cstate_a = (c_a,\<beta>_a,ve_a,b_a)" 
    by (cases cstate_a, auto)
  ultimately
  have abs_c: "c = c_a"
   and abs_\<beta>: "abs_benv \<beta> \<sqsubseteq> \<beta>_a"
   and abs_ve: "abs_venv ve \<sqsubseteq> ve_a"
   and abs_b: "abs_cnt b \<sqsubseteq> b_a"
  using 2 by auto

  from cstate cstate_a abs_c abs_\<beta> abs_b
  show ?case
  proof(cases c, auto simp add:HOL.Let_def simp del:evalF.simps evalC.simps set_map HOLCFExCF.evalV.simps)

  fix lab f vs
  
  have old_elems: "abs_ccache
     (evalF\<cdot>(Discr (HOLCFExCF.evalV f \<beta> ve, map (\<lambda>v. HOLCFExCF.evalV v \<beta> ve) vs, ve, HOLCFExCF.nb b lab)))
     \<sqsubseteq> (\<Union>f'\<in>HOLCFAbsCF.evalV f \<beta>_a ve_a.
              HOLCFAbsCF.evalF\<cdot>(Discr(f', map (\<lambda>v. HOLCFAbsCF.evalV v \<beta>_a ve_a) vs, ve_a, contour_class.nb (abs_cnt b) lab)))"
     sorry

  have new_elem: "abs_ccache {((lab, \<beta>), HOLCFExCF.evalV f \<beta> ve)}
                  \<sqsubseteq> {((lab, \<beta>_a), f') |f'. f' \<in> HOLCFAbsCF.evalV f \<beta>_a ve_a}"
    using abs_\<beta> and abs_d_evalV[OF abs_ve]
    by (auto simp add:sqsubset_is_subset)
    
  have "abs_ccache (evalF\<cdot>(Discr (HOLCFExCF.evalV f \<beta> ve, map (\<lambda>v. HOLCFExCF.evalV v \<beta> ve) vs, ve, HOLCFExCF.nb b lab))
        \<union> {((lab, \<beta>), HOLCFExCF.evalV f \<beta> ve)})
        \<sqsubseteq> abs_ccache (evalF\<cdot>(Discr (HOLCFExCF.evalV f \<beta> ve, map (\<lambda>v. HOLCFExCF.evalV v \<beta> ve) vs, ve, HOLCFExCF.nb b lab)))
        \<union> abs_ccache {((lab, \<beta>), HOLCFExCF.evalV f \<beta> ve)}"
    by (rule abs_ccache_union)
  also have "\<dots>
        \<sqsubseteq> (\<Union>f'\<in>HOLCFAbsCF.evalV f \<beta>_a ve_a.
              HOLCFAbsCF.evalF\<cdot>(Discr(f', map (\<lambda>v. HOLCFAbsCF.evalV v \<beta>_a ve_a) vs, ve_a, contour_class.nb (abs_cnt b) lab)))
        \<union> {((lab, \<beta>_a), f') |f'. f' \<in> HOLCFAbsCF.evalV f \<beta>_a ve_a}"
    by (rule Un_mono_sq[OF old_elems new_elem])
  finally
  show "abs_ccache (insert ((lab, \<beta>), HOLCFExCF.evalV f \<beta> ve)
                   (evalF\<cdot>(Discr (HOLCFExCF.evalV f \<beta> ve, map (\<lambda>v. HOLCFExCF.evalV v \<beta> ve) vs, ve, HOLCFExCF.nb b lab))))
        \<sqsubseteq> HOLCFAbsCF.evalC\<cdot>(Discr (App lab f vs, abs_benv \<beta>, ve_a, abs_cnt b))"
    using abs_\<beta>
    by (subst HOLCFAbsCF.evalC.simps)(auto simp add: HOL.Let_def simp del:HOLCFAbsCF.evalF.simps)
  next
  fix lab binds c'
  show "abs_ccache (evalC\<cdot>(Discr (c', \<beta>(lab \<mapsto> HOLCFExCF.nb b lab),
                                 ve ++ map_of (map (\<lambda>(v, l).((v, HOLCFExCF.nb b lab),HOLCFExCF.evalV (L l) (\<beta>(lab \<mapsto> HOLCFExCF.nb b lab)) ve)) binds),
                                 HOLCFExCF.nb b lab))) \<sqsubseteq>
          HOLCFAbsCF.evalC\<cdot>(Discr (call.Let lab binds c', \<beta>_a, ve_a, abs_cnt b))" sorry
  qed
}
qed

definition evalCPS :: "prog \<Rightarrow> ('c::contour) ans"
  where "evalCPS l = (let ve = smap_empty;
                          \<beta> = empty;
                          f = evalV (L l) \<beta> ve
                      in  evalF\<cdot>(Discr (contents f,[{Stop}],ve,initial_contour)))"


end