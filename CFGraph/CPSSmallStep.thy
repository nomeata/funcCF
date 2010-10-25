theory CPSSmallStep
imports CPSScheme CPSUtils Eval
begin

types state = "venv \<times> d list option \<times> benv option \<times> contour"

datatype node
  = StartNode lambda
  | StopNode
  | LambdaNode lambda
  | PrimNode prim
  | CallNode call

fun callD :: "d \<Rightarrow> venv \<Rightarrow> d list \<Rightarrow> contour \<Rightarrow> (node \<times> state)"
 where "callD (DC (l,\<beta>)) ve ds b = (LambdaNode l,  (ve, Some ds, Some \<beta>, b))"
     | "callD (DP prim)  ve ds b = (PrimNode prim, (ve, Some ds, None, b))"
     | "callD Stop       ve ds b = (StopNode, (ve, Some ds, None, b))"

inductive CPSStep :: "node \<Rightarrow> state \<Rightarrow> node \<Rightarrow> state \<Rightarrow> bool" ("_:_ \<Rightarrow> _:_") where
  "StartNode prog :   state \<Rightarrow> LambdaNode prog : (empty , Some [ Stop ] , Some empty, 0 )"
  | "\<lbrakk> length vs = length as \<rbrakk>
     \<Longrightarrow> LambdaNode (Lambda lab vs c) : (ve, Some ds, Some \<beta>, b) \<Rightarrow> CallNode c : (map_upds ve (map (\<lambda>v. (v,b)) vs) as, None, Some (\<beta>(lab \<mapsto> b)), b)"
  | "\<lbrakk> (n', s') = callD cnt ve [DI (a1+a2)] (Suc b) \<rbrakk> 
     \<Longrightarrow> PrimNode (Plus lab) : (ve, Some [DI a1, DI a2, cnt], None, b) \<Rightarrow> n' : s'"
  | "\<lbrakk> v \<noteq> 0 ; (n', s') = callD cntt ve [] (Suc b) \<rbrakk> 
     \<Longrightarrow> PrimNode (prim.If labt labf) : (ve, Some [DI v, cntt, cntf], None, b) \<Rightarrow> n' : s'"
  | "\<lbrakk> v = 0 ; (n', s') = callD cntf ve [] (Suc b) \<rbrakk> 
     \<Longrightarrow> PrimNode (prim.If labt labf) : (ve, Some [DI v, cntt, cntf], None, b) \<Rightarrow> n' : s'"
  | "\<lbrakk> (n', s') = callD (\<A> f \<beta> ve) ve (map (\<lambda>v . \<A> v \<beta> ve) vs) (Suc b) \<rbrakk> 
     \<Longrightarrow> CallNode (App lab f vs) : (ve, None, Some \<beta>, b) \<Rightarrow> n' : s'"
  | "\<lbrakk> (n', s') = callD (\<A> f \<beta> ve) ve (map (\<lambda>v . \<A> v \<beta> ve) vs) (Suc b); b' = Suc b ; \<beta>' = \<beta>(lab \<mapsto> b') \<rbrakk> 
     \<Longrightarrow> CallNode (Let lab binds c) : (ve, None, Some \<beta>, b) \<Rightarrow> CallNode c : (ve ++ map_of (map (\<lambda>(v,l). ((v,b'), DC (l,\<beta>'))) binds), None, Some \<beta>', b')"


end