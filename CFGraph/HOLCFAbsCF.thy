theory HOLCFAbsCF
  imports CPSUtils HOLCF HOLCFUtils HOLCFList HOLCFOption CPSScheme Utils HOLCFExCF
begin

class contour =
  fixes nb :: "'a \<Rightarrow> label \<Rightarrow> 'a"
    and initial_contour :: 'a
    and abs_cnt :: "HOLCFExCF.contour \<Rightarrow> 'a"

types 'c benv = "label \<rightharpoonup> 'c"
      'c closure = "lambda \<times> 'c benv"

datatype 'c proc = PC "'c closure"
                 | PP prim
                 | Stop

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

definition abs_venv :: "HOLCFExCF.venv \<Rightarrow> 'c::contour venv"
  where "abs_venv ve = (\<lambda>(v,b_a). \<Union>{(case ve (v,b) of Some d \<Rightarrow> abs_d d | None \<Rightarrow> {})| b . abs_cnt b = b_a})"

fun evalV :: "val \<Rightarrow> 'c benv \<Rightarrow> 'c venv \<Rightarrow> 'c d"
  where "evalV (C _ i) \<beta> ve = {}"
  |     "evalV (P prim) \<beta> ve = {PP prim}"
  |     "evalV (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> ve (var,l))"
  |     "evalV (L lam) \<beta> ve = {PC (lam, \<beta>)}"

types 'c ccache = "((label \<times> 'c benv) \<times> 'c proc) set"
      'c ans = "'c ccache"

definition abs_ccache :: "HOLCFExCF.ccache \<Rightarrow> 'c::contour ccache"
  where "abs_ccache cc = (\<Union>((c,\<beta>),d) \<in> cc . {((c,abs_benv \<beta>), p) | p . p\<in>abs_d d})"

types 'c fstate = "('c proc \<times> 'c d list \<times> 'c venv \<times> 'c)"
      'c cstate = "(call \<times> 'c benv \<times> 'c venv \<times> 'c)"

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

definition smap_empty
 where "smap_empty k = {}"

definition smap_Union :: "('a::type \<Rightarrow> 'b::type set) set \<Rightarrow> 'a \<Rightarrow> 'b set"
 where "smap_Union smaps k = (\<Union>map \<in> smaps . map k)"

definition smap_union :: "('a::type \<Rightarrow> 'b::type set)  \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b set)"
 where "smap_union smap1 smap2 k =  smap1 k \<union> smap2 k"

definition smap_singleton :: "'a::type \<Rightarrow> 'b::type set \<Rightarrow> 'a \<Rightarrow> 'b set"
  where "smap_singleton k vs k' = (if k = k' then vs else {})"


fixrec  evalF :: "'c::contour fstate discr \<rightarrow> 'c ans"
     and evalC :: "'c cstate discr \<rightarrow> 'c ans"
  where "evalF\<cdot>fstate = (case undiscr fstate of
             (PC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = smap_union ve (smap_Union (set (map (\<lambda>(v,a). smap_singleton (v,b) a) (zip vs as))))
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
                     ve' = smap_union ve (smap_Union (set (map (\<lambda>(v,l). smap_singleton (v,b') (evalV (L l) \<beta>' ve)) ls)))
                 in evalC\<cdot>(Discr (c',\<beta>',ve',b'))
        )"

print_theorems
lemmas evalF_evalC_induct = evalF_evalC.induct[case_names Admissibility Bottom Next]

fun evalF_cases
 where "evalF_cases (PC (Lambda lab vs c, \<beta>)) as ve b = undefined"
     | "evalF_cases (PP (Plus cp)) [a1, a2, cnt] ve b = undefined"
     | "evalF_cases (PP (prim.If cp1 cp2)) [v,cntt,cntf] ve b = undefined"
     | "evalF_cases  Stop [v] ve b = undefined"

lemmas fstate_case =  evalF_cases.cases[
  OF case_split, of _ "\<lambda>_ vs _ _ as _ _ . length vs = length as",
  case_names "Closure" "Closure_inv" "Plus" "If" "Stop"]


definition evalCPS :: "prog \<Rightarrow> ('c::contour) ans"
  where "evalCPS l = (let ve = smap_empty;
                          \<beta> = empty;
                          f = evalV (L l) \<beta> ve
                      in  evalF\<cdot>(Discr (contents f,[{Stop}],ve,initial_contour)))"


end