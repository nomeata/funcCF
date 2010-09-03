theory CPSUtils
imports CPSScheme
begin

fun subterms :: "lambda + call \<Rightarrow> (lambda + call) set"
and subtermsV :: "val \<Rightarrow> (lambda + call) set"
where "subterms (Inl l) = (case l of Lambda _ _ c \<Rightarrow> {Inl l} \<union> subterms (Inr c))"
    | "subterms (Inr c) = (case c of App _ _ _ \<Rightarrow> {Inr c}
                                   | Let _ binds c' \<Rightarrow> {Inr c}
                                                    \<union> UNION (set binds) (\<lambda>(_,l). subterms (Inl l))
                                                    \<union> subterms (Inr c'))"
    | "subtermsV (L l) = subterms (Inl l)"
    | "subtermsV _     = {}"

fun vars :: "lambda \<Rightarrow> var set"
and varsC :: "call \<Rightarrow> var set"
and varsV :: "val \<Rightarrow> var set"
where "vars (Lambda _ vs c) = set vs \<union> varsC c"
    | "varsC (App _ a as) = varsV a \<union> UNION (set as) varsV"
    | "varsC (Let _ binds c') = UNION (set binds) (\<lambda>(v,l). {v} \<union> vars l) \<union> varsC c'"
    | "varsV (L l) = vars l"
    | "varsV (R _ v) = {v}"
    | "varsV _  = {}"

fun label :: "lambda + call \<Rightarrow> label"
where "label (Inl (Lambda l _ _)) = l"
    | "label (Inr (App l _ _)) = l"
    | "label (Inr (Let l _ _)) = l"


end