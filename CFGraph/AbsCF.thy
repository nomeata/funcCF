theory AbsCF
  imports CPSUtils HOLCF HOLCFUtils CPSScheme Utils SetMap
begin

default_sort type

class contour = discrete_cpo +
  fixes nb_a :: "'a \<Rightarrow> label \<Rightarrow> 'a" ("\<anb>")
    and a_initial_contour :: 'a ("\<abinit>")

instantiation unit :: contour
begin
definition "\<anb> _ _ = ()"
definition "\<abinit> = ()"
instance by default auto
end

types 'c a_benv = "label \<rightharpoonup> 'c" ("_ \<abenv>" [1000])
      'c a_closure = "lambda \<times> 'c \<abenv>" ("_ \<aclosure>" [1000])

datatype 'c proc ("_ \<aproc>" [1000])
  = PC "'c \<aclosure>"
  | PP prim
  | AStop

types 'c a_d = "'c \<aproc> set" ("_ \<ad>" [1000])

types 'c a_venv = "var \<times> 'c \<Rightarrow> 'c \<ad>" ("_ \<avenv>" [1000])

fun evalV_a :: "val \<Rightarrow> 'c \<abenv> \<Rightarrow> 'c \<avenv> \<Rightarrow> 'c \<ad>" ("\<aA>")
  where "\<aA> (C _ i) \<beta> ve = {}"
  |     "\<aA> (P prim) \<beta> ve = {PP prim}"
  |     "\<aA> (R _ var) \<beta> ve =
           (case \<beta> (binder var) of
              Some l \<Rightarrow> ve (var,l)
            | None \<Rightarrow> {})"
  |     "\<aA> (L lam) \<beta> ve = {PC (lam, \<beta>)}"

types 'c a_ccache = "((label \<times> 'c \<abenv>) \<times> 'c \<aproc>) set" ("_ \<accache>" [1000])
      'c a_ans = "'c \<accache>" ("_ \<aans>" [1000])

types 'c a_fstate = "('c \<aproc> \<times> 'c \<ad> list \<times> 'c \<avenv> \<times> 'c)" ("_ \<afstate>" [1000])
      'c a_cstate = "(call \<times> 'c \<abenv> \<times> 'c \<avenv> \<times> 'c)" ("_ \<acstate>" [1000])

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

fixrec   a_evalF :: "'c::contour \<afstate> discr \<rightarrow> 'c \<aans>" ("\<aF>")
     and a_evalC :: "'c::contour \<acstate> discr \<rightarrow> 'c \<aans>" ("\<aC>")
  where "\<aF>\<cdot>fstate = (case undiscr fstate of
             (PC (Lambda lab vs c, \<beta>), as, ve, b) \<Rightarrow>
               (if length vs = length as
                then let \<beta>' = \<beta> (lab \<mapsto> b);
                         ve' = ve \<union>. (\<Union>. (map (\<lambda>(v,a). {(v,b) := a}.) (zip vs as)))
                     in \<aC>\<cdot>(Discr (c,\<beta>',ve',b))
                else \<bottom>)
            | (PP (Plus c),[_,_,cnts],ve,b) \<Rightarrow>
                     let b' = \<anb> b c;
                         \<beta>  = [c \<mapsto> b]
                     in (\<Union>cnt\<in>cnts. \<aF>\<cdot>(Discr (cnt,[{}],ve,b')))
                        \<union>
                        {((c, \<beta>), cont) | cont . cont \<in> cnts}
            | (PP (prim.If ct cf),[_, cntts, cntfs],ve,b) \<Rightarrow>
                  ((   let b' = \<anb> b ct;
                            \<beta> = [ct \<mapsto> b]
                        in (\<Union>cnt\<in>cntts . \<aF>\<cdot>(Discr (cnt,[],ve,b')))
                           \<union>{((ct, \<beta>), cnt) | cnt . cnt \<in> cntts}
                   )\<union>(
                       let b' = \<anb> b cf;
                            \<beta> = [cf \<mapsto> b]
                        in (\<Union>cnt\<in>cntfs . \<aF>\<cdot>(Discr (cnt,[],ve,b')))
                           \<union>{((cf, \<beta>), cnt) | cnt . cnt \<in> cntfs}
                   ))
            | (AStop,[_],_,_) \<Rightarrow> {}
            | _ \<Rightarrow> \<bottom>
        )"
      | "\<aC>\<cdot>cstate = (case undiscr cstate of
             (App lab f vs,\<beta>,ve,b) \<Rightarrow>
                 let fs = \<aA> f \<beta> ve;
                     as = map (\<lambda>v. \<aA> v \<beta> ve) vs;
                     b' = \<anb> b lab
                  in (\<Union>f' \<in> fs. \<aF>\<cdot>(Discr (f',as,ve,b')))
                     \<union>{((lab, \<beta>),f') | f' . f'\<in> fs}
            | (Let lab ls c',\<beta>,ve,b) \<Rightarrow>
                 let b' = \<anb> b lab;
                     \<beta>' = \<beta> (lab \<mapsto> b');
                     ve' = ve \<union>. (\<Union>. (map (\<lambda>(v,l). {(v,b') := (\<aA> (L l) \<beta>' ve)}.) ls))
                 in \<aC>\<cdot>(Discr (c',\<beta>',ve',b'))
        )"

lemmas a_evalF_evalC_induct = a_evalF_a_evalC.induct[case_names Admissibility Bottom Next]

fun a_evalF_cases
 where "a_evalF_cases (PC (Lambda lab vs c, \<beta>)) as ve b = undefined"
     | "a_evalF_cases (PP (Plus cp)) [a1, a2, cnt] ve b = undefined"
     | "a_evalF_cases (PP (prim.If cp1 cp2)) [v,cntt,cntf] ve b = undefined"
     | "a_evalF_cases AStop [v] ve b = undefined"

lemmas a_fstate_case = a_evalF_cases.cases[
  OF case_split, of _ "\<lambda>_ vs _ _ as _ _ . length vs = length as",
  case_names "Closure" "Closure_inv" "Plus" "If" "Stop"]

end
