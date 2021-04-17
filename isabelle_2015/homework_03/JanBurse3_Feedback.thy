header "IN2055, Homework 3, Jan Burse
        03.11.14, jburse@hispeed.ch"

(** Score: 11/10

  3.1: -4 for not proving the required theorem!
  3.2: 5/5
**)

theory JanBurse

imports "~~/src/HOL/IMP/AExp"

begin

section "Homework 3.1: Register Machine from Hell"

datatype instr = LDI int | LD nat | ST nat | ADD nat

type_synonym state = "nat \<Rightarrow> int"

fun exec :: "instr \<Rightarrow> state \<Rightarrow> state" where
   "exec (LDI i) s = s(0 := i)" |
   "exec (LD n) s = (let h = s(Suc n) in s(0 := h))" |
   "exec (ST n) s = (let h = s(0) in s((Suc n) := h))" |
   "exec (ADD n) s = (let h = s(Suc n)+ s(0) in s(0 := h))"

fun execs :: "instr list \<Rightarrow> state \<Rightarrow> state" where
   "execs [] s = s" |
   "execs (i # is) s = execs is (exec i s)"

lemma execs_append[simp]: "\<forall>s. execs (xs @ ys) s = execs ys (execs xs s)"
apply (induction xs)
apply (auto)
done

datatype expr = C int | V nat | A expr expr

fun val::"expr \<Rightarrow> state \<Rightarrow> int" where
   "val (C i) s = i" |
   "val (V n) s = s(Suc n)" |
   "val (A a b) s = (val a s) + (val b s)"

fun vars::"expr \<Rightarrow> nat set" where
   "vars (C i) = {}" |
   "vars (V n) = {n}" |
   "vars (A a b) = (vars a) \<union> (vars b)"

fun cmp::"expr \<Rightarrow> nat \<Rightarrow> instr list" where
   "cmp (C i) k = [LDI i]" |
   "cmp (V n) k = [LD n]" |
   "cmp (A a b) k = (cmp a k) @ [ST k] @ (cmp b (Suc k)) @ [ADD k]"

fun above::"nat \<Rightarrow> nat set \<Rightarrow> bool" where
   "above k s = (\<forall>n. (n \<in> s \<longrightarrow> n < k))"

lemma above_more[simp]: "above k s \<and> l > k \<longrightarrow> above l s"
apply (auto)
done

lemma cmp_more[simp]: "\<forall>s k l. above k (vars e) \<and> l > k \<longrightarrow> 
                       execs (cmp e l) s (Suc k) = s (Suc k)"
apply (induction e)
apply (auto)
done

lemma less_succ[simp]: "l < k \<longrightarrow> l < (Suc k)"
apply (auto)
done

lemma cmp_less[simp]: "\<forall>s k l. above k (vars e) \<and> l < k \<longrightarrow> 
                       execs (cmp e k) s (Suc l) = s (Suc l)"
apply (induction e)
apply (auto)
done

lemma val_exec[simp]: "\<forall>s k. above k (vars e1) \<and> above k (vars e2) \<longrightarrow> 
                       val e2 (execs (cmp e1 k) s) = val e2 s"
apply (induction e2)
apply (auto)
done

lemma val_subst[simp]: "\<forall>s k h. above k (vars e) \<longrightarrow> 
                 val e (\<lambda>a. if a=(Suc k) then h else s a) = val e s"
apply (induction e)
apply (auto)
done

theorem hell_yeah: "\<forall>s k. above k (vars e) \<longrightarrow> execs (cmp e k) s 0 = val e s"
apply (induction e)
apply (auto)
done

(** Your compiler is not complete, it lacks the computation of 
  maxvars. Note that your above function does not define an algorithm!
  In essence, you proved a different theorem than was explicitly required!
**)


section "Homework 3.2: a*b* Language Checker"

datatype ab = A | B

fun is_b :: "ab list \<Rightarrow> bool" where
   "is_b (A # _) = False" |
   "is_b (B # xs) = is_b xs" |
   "is_b [] = True"

lemma isb_appb[simp]: "is_b (w @ [B]) = is_b w"
apply (induction w rule:is_b.induct)
apply (auto)
done

fun is_ab :: "ab list \<Rightarrow> bool" where
   "is_ab [] = True" |
   "is_ab (B # xs) = is_b xs" |
   "is_ab (A # xs) = is_ab xs"

lemma isab_appb[simp]: "is_ab (w @ [B]) = is_ab w"
apply (induction w rule: is_ab.induct)
apply (auto)
done

inductive_set S :: "ab list set" where
  SA: "w \<in> S \<Longrightarrow> [A] @ w \<in> S" |
  SB: "w \<in> S \<Longrightarrow> w @ [B] \<in> S" |
  SNil: "[] \<in> S"

theorem "w \<in> S \<Longrightarrow> is_ab w"
apply (induction w rule: S.induct)
apply (auto)
done

end
