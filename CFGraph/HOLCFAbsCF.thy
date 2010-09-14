theory HOLCFAbsCF
  imports CPSUtils HOLCF HOLCFUtils HOLCFList HOLCFOption CPSScheme Utils
begin

class contour =
  fixes nb :: "'a \<Rightarrow> label \<Rightarrow> 'a"
    and initial_contour :: 'a

types 'c benv = "label \<rightharpoonup> 'c"
      'c closure = "lambda \<times> 'c benv"

datatype 'c proc = PC "'c closure"
                 | PP prim
                 | Stop

types 'c d = "'c proc set"

types 'c venv = "var \<times> 'c \<rightharpoonup> 'c d"

fun evalV :: "val \<Rightarrow> 'c benv \<Rightarrow> 'c venv \<Rightarrow> 'c d"
  where "evalV (C _ i) \<beta> ve = {}"
  |     "evalV (P prim) \<beta> ve = {PP prim}"
  |     "evalV (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> (case ve (var,l) of Some d \<Rightarrow> d))"
  |     "evalV (L lam) \<beta> ve = {PC (lam, \<beta>)}"

types 'c ccache = "((label \<times> 'c benv) \<times> 'c proc) set"
      'c ans = "'c ccache"

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


fixrec  evalF :: "'c::contour fstate discr \<rightarrow> 'c ans"
     and evalC :: "'c cstate discr \<rightarrow> 'c ans"
  where "evalF\<cdot>fstate = (case undiscr fstate of
             (PC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
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
                    ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), evalV (L l) \<beta>' ve)) ls)
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
  where "evalCPS l = (let ve = empty;
                          \<beta> = empty;
                          f = evalV (L l) \<beta> ve
                      in  evalF\<cdot>(Discr (contents f,[{Stop}],ve,initial_contour)))"


end