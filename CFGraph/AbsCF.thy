theory ExCF
  imports CPSScheme
begin

class contour =
  fixes nb :: "'a \<Rightarrow> label \<Rightarrow> 'a"

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

types 'c ccache = "label \<times> 'c benv \<rightharpoonup> 'c d"
      'c ans = "'c ccache"

(* Do we need this or can we argue via ccpos somehow? *)
types args = nat
(*types args = "((proc \<times> d list \<times> venv \<times> contour) + (call \<times> benv \<times> venv \<times> contour)) set" *)

definition mapUnion :: "('a \<rightharpoonup> 'b) set \<Rightarrow> ('a \<rightharpoonup> 'b)"
  where "mapUnion maps = fold map_add empty maps"

function (sequential,domintros)
         evalF :: "'c::contour proc \<Rightarrow> 'c d list \<Rightarrow> 'c venv \<Rightarrow> 'c \<Rightarrow> args \<Rightarrow> 'c ans"
     and evalC :: "call \<Rightarrow> 'c benv \<Rightarrow> 'c venv \<Rightarrow> 'c \<Rightarrow> args \<Rightarrow> 'c ans"
  where "evalF (PC (Lambda lab vs c, \<beta>)) as ve b seen
          = (case length vs = length as of
              True \<Rightarrow> let \<beta>' = \<beta> (lab \<mapsto> b);
                          ve' = map_upds ve (map (\<lambda>v.(v,b)) vs) as
                      in evalC c \<beta>' ve' b seen
            )"
  |     "evalF (PP (Plus c)) as ve b seen
          = (case as of  [_, _, conts] \<Rightarrow>
                   let b' = nb b c;
                       \<beta>  = [c \<mapsto> b]
                   in mapUnion {evalF cont [{}] ve b' seen | cont . cont \<in> conts}
                      ((c, \<beta>) \<mapsto> conts))"
  |     "evalF (PP (If ct cf)) [_, contts, contfs] ve b seen
          = (      (let b' = nb b ct;
                        \<beta> = [ct \<mapsto> b]
                   in mapUnion {evalF cont [] ve b' seen | cont . cont \<in> contts}
                      ((ct, \<beta>) \<mapsto> contts)) ++
                   (let b' = nb b cf;
                        \<beta> = [cf \<mapsto> b]
                   in mapUnion {evalF cont [] ve b' seen | cont . cont \<in> contfs}
                      ((cf, \<beta>) \<mapsto> contfs)))"
  |     "evalF Stop as _ _ seen
          = (case as of [_] \<Rightarrow> empty)"

  |     "evalC (App lab f vs) \<beta> ve b seen
          = (let F = evalV f \<beta> ve;
                 as = map (\<lambda>v. evalV v \<beta> ve) vs;
                 b' = nb b lab
             in mapUnion {evalF f' as ve b' seen ((lab,\<beta>) \<mapsto> F)
                | f' . f' \<in> F})"
  |     "evalC (Let lab ls c') \<beta> ve b seen
          = (let b' = nb b lab;
                 \<beta>' = \<beta> (lab \<mapsto> b');
                 ve' = ve ++ map_of (map (\<lambda>(v,l). ((v,b'), evalV (L l) \<beta>' ve)) ls)
            in evalC c' \<beta>' ve' b' seen)"
  apply pat_completeness
  apply auto
done

print_theorems


end
