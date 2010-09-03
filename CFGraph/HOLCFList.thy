theory HOLCFList imports HOLCF
begin

instantiation list :: (po) po
begin

fun below_list 
 where "[] \<sqsubseteq> [] = True"
     | "[] \<sqsubseteq> (_#_) = False"
     | "(_#_) \<sqsubseteq> [] = False"
     | "(a#as) \<sqsubseteq> (b#bs) = (a \<sqsubseteq> b \<and> as \<sqsubseteq> bs)"
print_theorems

lemma [simp]:"[] \<sqsubseteq> x \<Longrightarrow> x = []"
by (cases rule:below_list.cases) auto

lemma [simp]:"x \<sqsubseteq> [] \<Longrightarrow> x = []"
by (cases rule:below_list.cases) auto

lemma list_below_cons:
  assumes "a#as \<sqsubseteq> x"
  obtains b and bs where "a \<sqsubseteq> b" and "as \<sqsubseteq> bs" and "x=b#bs"
using assms by (cases "(a#as,x)" rule:below_list.cases) auto

instance 
apply default
proof-
  fix  x :: "'a list"
  show "x \<sqsubseteq> x" by (induct x) auto

  next
  fix  x y z :: "'a list"
  show "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  proof (induct x z arbitrary:y rule:list_induct2')
  print_cases
  case (2 x xs y)
    hence "y=[]" by simp
    with `x # xs \<sqsubseteq> y` have "x # xs = []" by simp
    thus ?case by simp
  next
  case (3 z zs y)
    hence "y=[]" by simp
    with `y \<sqsubseteq> z # zs` have "z # zs = []" by simp
    thus ?case by simp
  next
  case (4 x xs z zs y)
    from `x # xs \<sqsubseteq> y` obtain y' and ys
      where "x \<sqsubseteq> y'" and "xs \<sqsubseteq> ys" and "y = y'#ys" by (rule list_below_cons)
    hence "y'#ys \<sqsubseteq> z # zs" using 4 by simp
    hence "y' \<sqsubseteq> z \<and> ys \<sqsubseteq> zs"
      by  (cases "(y'#ys,z # zs)" rule:below_list.cases) auto
    hence "y' \<sqsubseteq> z" and "ys \<sqsubseteq> zs" by auto
    from `x \<sqsubseteq> y'` and `y' \<sqsubseteq> z` have "x \<sqsubseteq> z " by (rule below_trans)
    moreover
    from `xs \<sqsubseteq> ys` and `ys \<sqsubseteq> zs` and "4.hyps" have "xs \<sqsubseteq> zs" by simp
    ultimately show ?case by simp 
  qed simp 
  next
  fix  x y :: "'a list"
  show "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
    by (induct x y rule:list_induct2') (auto simp add:below_antisym)
qed
end

instance list :: (cpo) cpo 
apply default
proof-
  fix S :: "nat => 'a list"
  assume "chain S"
  thus "\<exists>x. range S <<| x"
  apply -
  proof (induct "S 0" arbitrary:S)
  case Nil
    { fix n
    from Nil and `chain S` have "S n = []"
    proof (induct n)
      case 0 show ?case using Nil.hyps by simp
      next
      case (Suc n)
      hence "S n = []" by simp
      from `chain S` have "S n \<sqsubseteq> S (Suc n)" by (auto dest: chainE)
      with `S n = []` have "[] \<sqsubseteq> S (Suc n)" by simp
      hence "S (Suc n) = []" by simp
      thus ?case by simp
    qed
    } hence "range S = {[]}" by auto
    hence "range S <<| []" by (auto simp add:is_lub_singleton)
    thus ?case by auto
  next
  case (Cons x xs)
    { fix i have "S i \<noteq> []" using Cons(2)
      proof (induct i)
      case 0 thus ?case by auto
      case (Suc i) hence "S i \<noteq> []" by simp
        from `chain S` have "S i \<sqsubseteq> S (Suc i)" by (auto dest: chainE)
        with `S i \<noteq> []` show "S (Suc i) \<noteq> []" by -(rule ccontr,simp)
      qed
    } hence "\<forall> i. S i \<noteq> []" by simp

    def S' == "\<lambda>n. tl (S n)"
    have "xs = S' 0" unfolding S'_def using Cons(2) by (cases "S 0") auto
    moreover
    have "chain S'"
    proof(rule chainI)
      fix i
      from `chain S` have "S i \<sqsubseteq> S (Suc i)" by (rule chainE)
      thus "S' i \<sqsubseteq> S' (Suc i)"
      unfolding S'_def
      by (cases "(S i,S (Suc i))" rule:below_list.cases) auto
    qed
    ultimately
    obtain X' where "range S' <<| X'" using Cons(1) by auto
    
    def s \<equiv> "\<lambda>n. hd (S n)"
    have "x = s 0" unfolding s_def using Cons(2) by (cases "S 0") auto
    
    have "chain s"
    proof(rule chainI)
      fix i
      from `chain S` have "S i \<sqsubseteq> S (Suc i)" by (rule chainE)
      thus "s i \<sqsubseteq> s (Suc i)"
      unfolding s_def
      by (cases "(S i,S (Suc i))" rule:below_list.cases) auto
    qed
    then  obtain x' where "range s <<| x'" by (auto dest:cpo)

    have "range S <<| x' # X'"
    proof(rule is_lubI)
      show "range S <| x' # X'"
      proof (rule is_ubI)
        fix x
        assume "x\<in>range S"
        then obtain i where "x = S i" by blast
        from `\<forall>i. S i \<noteq> []` have "S i \<noteq> []" by simp
        from `range s <<| x'` have "s i \<sqsubseteq> x'"
          by (auto dest:is_lubD1 ub_rangeD)
        moreover
        from `range S' <<| X'` have "S' i \<sqsubseteq> X'"
          by (auto dest:is_lubD1 ub_rangeD)
        ultimately
        have "s i # S' i \<sqsubseteq> x'#X'" by simp
        hence "hd (S i) # tl (S i) \<sqsubseteq> x'#X'"
          unfolding S'_def and s_def by simp
        hence "S i \<sqsubseteq> x'#X'" using `S i \<noteq> []` by auto
        with `x = S i` show "x \<sqsubseteq> x' # X'" by simp
     qed
     next
     fix u
     assume "range S <| u"
     from `range S <| u` have "S 0 \<sqsubseteq> u" by (rule ub_rangeD)
     with `S 0 \<noteq> []` have "u \<noteq> []" by auto
     then obtain u' and us where "u = u'#us" by (cases u) auto
      
     have "range s <| u'"
     proof(rule ub_rangeI)
       fix i
       from `range S <| u` and `u = u'#us`
       have "S i \<sqsubseteq> u'#us" by (auto dest: ub_rangeD)
       hence "hd (S i) \<sqsubseteq> u'" by (cases "(S i,u'#us)" rule:below_list.cases) auto
       thus "s i \<sqsubseteq> u'" unfolding s_def by simp
     qed
     hence "x' \<sqsubseteq>  u'" using `range s <<| x'` by -(rule is_lub_lub) 
     moreover
     have "range S' <| us" 
     proof(rule ub_rangeI)
       fix i
       from `range S <| u` and `u = u'#us`
       have "S i \<sqsubseteq> u'#us" by (auto dest: ub_rangeD)
       hence "tl (S i) \<sqsubseteq> us" by (cases "(S i,u'#us)" rule:below_list.cases) auto
       thus "S' i \<sqsubseteq> us" unfolding S'_def by simp
     qed
     hence "X' \<sqsubseteq>  us" using `range S' <<| X'` by -(rule is_lub_lub) 
     ultimately
     show "x' # X' \<sqsubseteq> u" using `u = u'#us` by simp
   qed
   thus ?case by blast
  qed
qed
end
