theory CPSSmallStep
imports CPSScheme CPSUtils Eval
begin

types state = "venv \<times> d list \<times> benv \<times> contour"

datatype node
  = StartNode lambda
  | StopNode
  | LambdaNode lambda
  | PrimNode prim
  | CallNode call

fun callD :: "d \<Rightarrow> venv \<Rightarrow> d list \<Rightarrow> benv \<Rightarrow> contour \<Rightarrow> (node \<times> state) option"
 where "callD (DC (l,\<beta>)) ve ds _ b = Some (LambdaNode l,  (ve, ds, \<beta>, b))"
     | "callD (DP prim)  ve ds \<beta> b = Some (PrimNode prim, (ve, ds, \<beta>, b))"
     | "callD Stop       ve ds \<beta> b = Some (StopNode,      (ve, ds, \<beta>, b))"
     | "callD (DI _)     ve ds \<beta> b = None"

fun CPSStep :: "node \<Rightarrow> state \<Rightarrow> (node \<times> state) option" ("\<langle>_:_\<rangle>") where
  "\<langle>StartNode prog : _\<rangle> = Some (LambdaNode prog, (empty , [ Stop ], empty, 0 ))"
 |"\<langle>LambdaNode (Lambda lab vs c) : (ve, ds, \<beta>, b)\<rangle> =
       (if length vs = length ds then Some (CallNode c , (map_upds ve (map (\<lambda>v. (v,b)) vs) ds, ds, (\<beta>(lab \<mapsto> b)), b)) else None)"
 |"\<langle>PrimNode (Plus lab) : (ve, [DI a1, DI a2, cnt], \<beta>, b)\<rangle> = callD cnt ve [DI (a1+a2)] \<beta> (Suc b)"
 |"\<langle>PrimNode (prim.If labt labf) : (ve, [DI v, cntt, cntf], \<beta>, b)\<rangle> = callD (if v\<noteq>0 then cntt else cntf) ve [] \<beta> (Suc b)"
 |"\<langle>CallNode (App lab f vs) : (ve, ds, \<beta>, b)\<rangle> = callD (\<A> f \<beta> ve) ve (map (\<lambda>v . \<A> v \<beta> ve) vs) \<beta> (Suc b) "
 |"\<langle>CallNode (Let lab binds c) : (ve, ds, \<beta>, b)\<rangle> =
     (let b' = Suc b;  \<beta>' = \<beta>(lab \<mapsto> b')
      in Some (CallNode c, (ve ++ map_of (map (\<lambda>(v,l). ((v,b'), DC (l,\<beta>'))) binds), ds, \<beta>', b')))"
 |"\<langle>_ : _\<rangle> = None"

end