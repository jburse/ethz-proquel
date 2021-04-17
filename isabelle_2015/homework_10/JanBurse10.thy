header "IN2055, Homework 10, Jan Burse
        12.01.15, jburse@hispeed.ch"

theory JanBurse10

imports Main

begin

section "Homework 10: Be Original!"

(**************************************************************)
(*                                                            *)
(* We show that some code implements a lastIndexOf function.  *)
(* We only show being a function and termination. Because of  *)
(* lack of time, we don't show correctness. The code reads:   *)
(*                                                            *)
(*      lastIndexOf = WHILE (0<i & a[i-1]!=b) DO i=i-1;       *)
(*                                                            *)
(* The underlying while language has been extended by arrays  *)
(* so as to be able to formulate the lastIndexOf code. The    *)
(* big step semantic of the language is defined in sub        *)
(* section 1.                                                 *)
(*                                                            *)
(* The termination proof is not based on some annotation, but *)
(* on some syntactic criteria. The criteria is basically a    *)
(* bounded loop with an exit condition. The syntactic notions *)
(* are verified for the big step semantic in sub section 2.   *)
(*                                                            *)
(* To be a function the code should not modify a and b, this  *)
(* can be formally verified. That the while is a bounded loop *)
(* with exit can also be formally verified. The proofs are    *)
(* found in sub section 3.                                    *)
(*                                                            *)
(**************************************************************)

(**************************************************************)
(* Section 1 was done before new year. Section 2 was done     *)
(* shortly after new year. Sadly we heard only today about    *)
(* total correctness and verification code generation.        *)
(*                                                            *)
(* But on the other hand our annotation less termination is   *)
(* also appealing. Maybe the methods could be combined, by    *)
(* an annotation that hints the syntactic criteria that       *)
(* should be checked.                                         *)
(**************************************************************)

subsection "Section 1: While with Arrays"

(**************************************************************)
(* We define here a while programming language with arrays.   *)
(* The introduction of arrays has impacted the state, the     *)
(* arithmetic expressions and the commands.                   *)
(* As a small enhancement we also introduced arithmetic       *)
(* subtraction and Boolean equality.                          *)
(**************************************************************)

(**************************************************************)
(* Arithmetic Expressions                                     *)
(* - The data type is not mutually recursive, since the list  *)
(*   type expressions in the variable constructor is allowed. *)
(* - The evaluation function is also not mutually recursive,  *)
(*   the trick is to use the map operator for the list type.  *)
(**************************************************************)

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<times> val list \<Rightarrow> int"

datatype aexp = N int
              | V vname "aexp list"
              | Plus aexp aexp
              | Minus aexp aexp
         
fun aval::"aexp \<Rightarrow> state \<Rightarrow> val" where
   "aval (N n) _ = n" |
   "aval (V x i) s = (s (x,(map (\<lambda>e.(aval e s)) i)))" |
   "aval (Plus a b) s = aval a s + aval b s" |
   "aval (Minus a b) s = aval a s - aval b s"

value "aval (Plus (V ''x'' []) (N 5)) (\<lambda>x. if x = (''x'',[]) then 7 else 0)"

value "aval (Plus (V ''x'' []) (N 5)) ((\<lambda>x. 0) ((''x'',[]) := 7)) "

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

value "aval (Plus (V ''x'' []) (N 5)) <(''x'',[]) := 7>"

(**************************************************************)
(* Boolean Expressions                                        *)
(**************************************************************)

datatype bexp = Bc bool
              | Not bexp
              | And bexp bexp
              | Less aexp aexp
              | Eq aexp aexp

fun bval::"bexp \<Rightarrow> state \<Rightarrow> bool" where
   "bval (Bc v) _ = v" |
   "bval (Not b) s = (\<not> bval b s)" |
   "bval (And a b) s = (bval a s \<and> bval b s)" |
   "bval (Less a b) s = (aval a s < aval b s)" |
   "bval (Eq a b) s = (aval a s = aval b s)"

value "bval (Less (V ''x'' []) (Plus (N 3) (V ''y'' [])))
            <(''x'',[]) := 3, (''y'',[]) := 1>"

(**************************************************************)
(* Commands and Big Step                                      *)
(* - We use the list type expression in the data type.        *)
(* - We use the map operator in the assignment statement.     *)
(**************************************************************)

datatype com = SKIP
             | Assign vname "aexp list" aexp  ("_ _ ::= _" [1000, 61, 61] 61)
             | Seq com com                    ("_;;/ _"  [60, 61] 60)
             | If bexp com com                ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
             | While bexp com                 ("(WHILE _/ DO _)" [0,61] 61)

value "''x'' [] ::= (V ''y'' [])"

inductive big_step::"com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
     "big_step SKIP s s" |
     "big_step (x i ::= a) s (s((x,(map (\<lambda>e.(aval e s)) i)) := aval a s))" |
     "big_step c1 s1 s2 \<Longrightarrow> big_step c2 s2 s3 \<Longrightarrow> big_step (c1;;c2) s1 s3" |
     "bval b s \<Longrightarrow> big_step c1 s t 
               \<Longrightarrow> big_step (IF b THEN c1 ELSE c2) s t" |
     "\<not>bval b s \<Longrightarrow> big_step c2 s t 
                \<Longrightarrow> big_step (IF b THEN c1 ELSE c2) s t" |
     "bval b s1 \<Longrightarrow> big_step c s1 s2 \<Longrightarrow> big_step (WHILE b DO c) s2 s3 
               \<Longrightarrow> big_step (WHILE b DO c) s1 s3" |
     "\<not>bval b s \<Longrightarrow> big_step (WHILE b DO c) s s"

subsection "Section 2: Loops with Exit"

(**************************************************************)
(* We define here an extension of the always terminating loop *)
(* subset of while programs. Our loops have an additional     *)
(* exit condition and also work for arrays.                   *)
(**************************************************************)

(**************************************************************)
(* Big Step with Counter                                      *)
(* - We show equivalence to big step. We did this already in  *)
(*   our homework 6.1. We needed to adapt the assignment.     *)
(**************************************************************)

(* we inductively define a big step semantic with counting.
   the counter is carried along the exec calls, and a guard
   f2 < f1 assures that isabelle/hol thinks exec terminates. *)
inductive exec::"nat \<Rightarrow> com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" where
   "exec (Suc f) SKIP s f s" |
   "exec (Suc f) (x i ::= e) s f (s((x,(map (\<lambda>e.(aval e s)) i)) := aval e s))" |
   "exec f1 c1 s1 f2 s2 \<Longrightarrow> f2 < f1 \<Longrightarrow> 
    exec f2 c2 s2 f3 s3 \<Longrightarrow> 
       exec (Suc f1) (c1 ;; c2) s1 f3 s3 " |
   "bval b s1 \<Longrightarrow> exec f1 c1 s1 f2 s2 \<Longrightarrow> 
       exec (Suc f1) (IF b THEN c1 ELSE c2) s1 f2 s2" |
   "\<not>bval b s1 \<Longrightarrow> exec f1 c2 s1 f2 s2 \<Longrightarrow>
       exec (Suc f1) (IF b THEN c1 ELSE c2) s1 f2 s2" |
   "bval b s1 \<Longrightarrow> exec f1 c s1 f2 s2 \<Longrightarrow> f2 < f1 \<Longrightarrow>
       exec f2 (WHILE b DO c) s2 f3 s3 \<Longrightarrow> 
       exec (Suc f1) (WHILE b DO c) s1 f3 s3" |
   "\<not>bval b s1 \<Longrightarrow> exec (Suc f1) (WHILE b DO c) s1 f1 s1"

(* we show that the guard in the definition of exec
   really holds. *)
lemma less_exec[simp]:"exec m c s n t \<Longrightarrow> m>n"
apply (induction rule:exec.induct)
apply (auto)
done

(* we show that the input and output counters can
   be shifted on the right side, so basically their 
   difference says how many steps have been executed. *)
lemma shift_exec1:"exec m c s n t \<Longrightarrow> exec (m+k) c s (n+k) t"
apply (induction arbitrary: k rule:exec.induct)
apply (auto intro:exec.intros)
apply (intro exec.intros)
apply (auto)
apply (intro exec.intros)
apply (auto)
done

(* we show that the input and output counters can
   be shifted on the left side, so basically their 
   difference says how many steps have been executed. *)
lemma shift_exec2:"exec m c s n t \<Longrightarrow> exec (k+m) c s (k+n) t"
apply (induction arbitrary: k rule:exec.induct)
apply (auto intro:exec.intros)
apply (intro exec.intros)
apply (auto)
apply (intro exec.intros)
apply (auto)
done

(* we show that the counting is additive among
   the sequential construct *)
lemma seq_exec:"exec m1 c1 s1 n1 s2 \<Longrightarrow>
                exec m2 c2 s2 n2 s3 \<Longrightarrow>
                exec (Suc (m1+m2)) (c1;; c2) s1 (n1+n2) s3"
proof (intro exec.intros)
   assume "exec m1 c1 s1 n1 s2"
   thus "exec (m1 + m2) c1 s1 (n1 + m2) s2"
   by (auto simp:shift_exec1)
next
   assume "exec m2 c2 s2 n2 s3"
   thus "exec (n1 + m2) c2 s2 (n1 + n2) s3"
   by (auto simp:shift_exec2)
qed (auto)

(* we show that the counting is additive among
   the while construct *)
lemma while_exec:"bval b s1 \<Longrightarrow>
                exec m1 c s1 n1 s2 \<Longrightarrow>
                exec m2 (WHILE b DO c) s2 n2 s3 \<Longrightarrow>
                exec (Suc (m1+m2)) (WHILE b DO c) s1 (n1+n2) s3"
proof (intro exec.intros)
   assume "exec m1 c s1 n1 s2"
   thus "exec (m1 + m2) c s1 (n1 + m2) s2"
   by (auto simp:shift_exec1)
next
   assume "exec m2 (WHILE b DO c) s2 n2 s3"
   thus "exec (n1 + m2) (WHILE b DO c) s2 (n1 + n2) s3"
   by (auto simp:shift_exec2)
qed (auto)

(* we show that big step implies big step with counting *)
lemma big_step_to_exec:"big_step c s t \<Longrightarrow> \<exists>m n. exec (Suc m) c s n t"
proof (induction c s t rule:big_step.induct)
  fix x e s i
  show "\<exists>m n.  exec (Suc m) (x i ::= e) s n (s((x,(map (\<lambda>e.(aval e s)) i)) := aval e s))"
  by (auto intro:exec.intros)
next
  fix c1 s1 s2 c2 s3
  assume "\<exists>m n. exec (Suc m) c1 s1 n s2"
  and "\<exists>m n. exec (Suc m) c2 s2 n s3"
  thus "\<exists>m n. exec (Suc m) (c1;; c2) s1 n s3"
  by (auto intro:seq_exec)
next
  fix b s1 c s2 s3
  assume "bval b s1"
  and "\<exists>m n. exec (Suc m) c s1 n s2"
  and "\<exists>m n. exec (Suc m) (WHILE b DO c) s2 n s3"
  thus "\<exists>m n. exec (Suc m) (WHILE b DO c) s1 n s3"
  by (auto intro:while_exec)
qed (auto intro:exec.intros)

(* we show that big step with counting implies big step *)
lemma exec_to_big_step:"exec (Suc m) c s n t \<Longrightarrow> big_step c s t"
proof (induction rule:exec.induct) 
  fix f x e s i
  show "big_step (x i ::= e) s (s((x,(map (\<lambda>e.(aval e s)) i)) := aval e s))"
  by (auto intro:big_step.intros)
qed (auto intro:big_step.intros)

(* we show that big step and big step with counting are the same *)
theorem exec_eq_big_step:"(big_step c s t) = (\<exists>m n. exec (Suc m) c s n t)"
proof (rule iffI) 
  fix c s t
  assume "big_step c s t"
  thus "\<exists>m n. exec (Suc m) c s n t"
  using big_step_to_exec by (auto)
next
  fix c s t
  assume "\<exists>m n. exec (Suc m) c s n t"
  thus "big_step c s t"
  using exec_to_big_step by (auto)
qed

(**************************************************************)
(* Loop with Exit Condition                                   *)
(* - We show termination of for loops. We did this already in *)
(*   our homework 8.2. We needed to adapt the assignment.     *)
(* - The loop condition has been relaxed so that an exit      *)
(*   can be formulated before the counter reaches zero.       *)
(**************************************************************)

(* var_no_assign syntactically checks whether in a given
   command a given variable does not receive any assignment.
   Here the variable can also be an array. *)
inductive var_no_assign::"com \<Rightarrow> vname \<Rightarrow> bool" where
   "var_no_assign SKIP _" |
   "x \<noteq> y \<Longrightarrow> var_no_assign (x _ ::= e) y" |
   "var_no_assign c1 x \<Longrightarrow> var_no_assign c2 x
      \<Longrightarrow> var_no_assign (c1;; c2) x" |
   "var_no_assign c1 x \<Longrightarrow> var_no_assign c2 x
      \<Longrightarrow> var_no_assign (IF b THEN c1 ELSE c2) x" |
   "var_no_assign c x
      \<Longrightarrow> var_no_assign (WHILE b DO c) x"

inductive_cases var_no_assign_elim:"var_no_assign c x"

(* we show that the syntactical var_no_assign implies that
   semantically the state isn't changed for the given variable.
   Here the variable can also be an array. *)
lemma var_no_assign_no_change_state:"exec m c s n t \<Longrightarrow> var_no_assign c x \<Longrightarrow> \<forall>l.(s (x,l) = t (x,l))"
proof (induction arbitrary: x rule:exec.induct)
   fix c s1 b s3 x and s2::state
   assume "\<And>x. var_no_assign c x \<Longrightarrow> \<forall>l.(s1 (x,l) = s2 (x,l))"
   and "\<And>x. var_no_assign (WHILE b DO c) x \<Longrightarrow> \<forall>l.(s2 (x,l) = s3 (x,l))"
   and "var_no_assign (WHILE b DO c) x" 
   thus "\<forall>l.(s1 (x,l) = s3 (x,l))"
   by (fastforce elim:var_no_assign_elim)
qed (auto elim:var_no_assign_elim)

(* var_decrements syntactically checks whether in a given
   command a given variable is decremented by a positive 
   non-zero not necessarily unique value. While loops in
   the command are covered by var_non_assign. Here the 
   variable isn't an array. *)
inductive var_decrements::"com \<Rightarrow> vname \<Rightarrow> bool" where
   "n < 0 \<Longrightarrow> var_decrements (x [] ::= (Plus (V x []) (N n))) x" |
   "n > 0 \<Longrightarrow> var_decrements (x [] ::= (Minus (V x []) (N n))) x" |
   "var_no_assign c1 x \<Longrightarrow> var_decrements c2 x
      \<Longrightarrow> var_decrements (c1;; c2) x" |
   "var_decrements c1 x \<Longrightarrow> var_no_assign c2 x
      \<Longrightarrow> var_decrements (c1;; c2) x" |
   "var_decrements c1 x \<Longrightarrow> var_decrements c2 x
      \<Longrightarrow> var_decrements (c1;; c2) x" |
   "var_decrements c1 x \<Longrightarrow> var_decrements c2 x
      \<Longrightarrow> var_decrements (IF b THEN c1 ELSE c2) x"

inductive_cases var_decrements_elim:"var_decrements c x"

(* we show that the syntactical var_decrements implies that
   semantically the state is strictly monotone decreasing
   for the given variable. Here the variable isn't an array. *)
lemma var_decrements_strict_mono_state:"exec m c s n t \<Longrightarrow> var_decrements c x \<Longrightarrow> s (x,[]) > t (x,[])"
proof (induction arbitrary: x rule:exec.induct)
   fix f1 c1 s1 f2 s2 c2 f3 s3 x
   assume "var_decrements (c1;; c2) x"
   and "exec f1 c1 s1 f2 s2"
   and "\<And>x. var_decrements c1 x \<Longrightarrow> s1 (x,[]) > s2 (x,[])"
   and "exec f2 c2 s2 f3 s3"
   and "\<And>x. var_decrements c2 x \<Longrightarrow> s2 (x,[]) > s3 (x,[])"
   thus "s1 (x,[]) > s3 (x,[])"
   proof (cases)
      assume label1:"exec f1 c1 s1 f2 s2"
      and label2:"var_no_assign c1 x"
      and label3:"\<And>x. var_decrements c2 x \<Longrightarrow> s2 (x,[]) > s3 (x,[])"
      and label4:"var_decrements c2 x"
      have "s1 (x,[]) = s2 (x,[])"
      using var_no_assign_no_change_state label1 label2 by simp
      moreover have "s2 (x,[]) > s3 (x,[])"
      using label3 label4 by simp
      ultimately show "s1 (x,[]) > s3 (x,[])" by simp
   next
      assume label1:"\<And>x. var_decrements c1 x \<Longrightarrow> s1 (x,[]) > s2 (x,[])"
      and label2:"var_decrements c1 x"
      and label3:"exec f2 c2 s2 f3 s3"
      and label4:"var_no_assign c2 x"
      have "s1 (x,[]) > s2 (x,[])"
      using label1 label2 by simp
      moreover have "s2 (x,[]) = s3 (x,[])"
      using var_no_assign_no_change_state label3 label4 by simp
      ultimately show "s1 (x,[]) > s3 (x,[])" by simp
   qed (fastforce)
qed (auto elim:var_decrements_elim)

(* cond_loop syntactically checks whether a condition
   has the form 0 < x. Here the variable isn't an array
   and the condition can happen inside a conjunction. *)
inductive cond_loop::"bexp \<Rightarrow> vname \<Rightarrow> bool" where
    "cond_loop (Less (N 0) (V x [])) x" |
    "cond_loop a x \<Longrightarrow> cond_loop (And a b) x" |
    "cond_loop b x \<Longrightarrow> cond_loop (And a b) x" 

(* we show that syntactical cond_loop implies that
   semantically the condition fails when the state
   says so. Here the variable isn't an array. *)
lemma cond_s:"cond_loop b x \<Longrightarrow> n \<le> 0 \<Longrightarrow> n = nat (s (x,[])) \<Longrightarrow> \<not> bval b s"
proof (induction rule:cond_loop.induct)
qed (auto)

(* we show that when the body of a while always terminates, 
   then the while itself also terminates provided the while 
   condition is syntactically satisfied and variable 
   decrements condition is syntactically satisfied in 
   the body of the while. Here the variable isn't an array. *)
lemma term_w:"v = nat (s (x,[])) \<Longrightarrow> \<forall>s. \<exists>t p q. exec (Suc p) c s q t \<Longrightarrow> 
       var_decrements c x \<Longrightarrow> cond_loop b x \<Longrightarrow>
       \<exists>t p q. exec (Suc p) (WHILE b DO c) s q t"
proof (induction v arbitrary: s rule:nat_less_induct, cases)
   fix n and s::state
   assume "n \<le> 0"
   and "n = nat (s (x,[]))"
   and "cond_loop b x"
   thus "\<exists>t p q. exec (Suc p) (WHILE b DO c) s q t"
   using cond_s
   by (force intro:exec.intros)
next
   fix n::nat and s::state
   assume label0:"\<not> n \<le> 0"
   assume label1:"n = nat (s (x,[]))"
   assume label2:"\<forall>s. \<exists>t p q. exec (Suc p) c s q t"
   assume label3:"var_decrements c x"
   assume label12:"cond_loop b x"
   assume label4:"\<forall>m<n.
          \<forall>xa. m = nat (xa (x,[])) \<longrightarrow>
                (\<forall>s. \<exists>t p q. exec (Suc p) c s q t) \<longrightarrow>
                var_decrements c x \<longrightarrow>
                cond_loop b x \<longrightarrow>
                (\<exists>t p q.
                    exec (Suc p)
                     (WHILE b DO c)
                     xa q t)"
   have "0 < s (x,[])"
   using label0 label1 by simp
   moreover have "\<exists>t p q. exec (Suc p) c s q t"
   using label2 by simp
   moreover have "\<forall>t p q. exec (Suc p) c s q t \<longrightarrow> t (x,[]) < s (x,[])"
   using label3 var_decrements_strict_mono_state by simp
   moreover have "\<forall>t m. (m < n \<longrightarrow> m = nat(t (x,[])) \<longrightarrow>
                (\<exists>p2 q2 t2. exec (Suc p2) (WHILE b DO c) t q2 t2))"
   using label4 label2 label3 label12 by blast
   ultimately show "\<exists>t p q. exec (Suc p) (WHILE b DO c) s q t"
   using label1
   proof (auto)
       fix t p q
       assume label5:"\<forall>t. (\<exists>p q. exec (Suc p) c s q t) \<longrightarrow> t (x,[]) < s (x,[])"
       assume label6:"exec (Suc p) c s q t"
       assume label7:"\<forall>t. t (x,[]) < s (x,[]) \<longrightarrow>
            (\<exists>p2 q2 t2.
                exec (Suc p2)
                 (WHILE b DO c) t
                 q2 t2)"
       have "t (x,[]) < s (x,[])"
       using label5 label6 by auto
       moreover have "t (x,[]) < s (x,[]) \<longrightarrow>
            (\<exists>p2 q2 t2.
                exec (Suc p2)
                 (WHILE b DO c) t
                 q2 t2)"
       using label7 by simp
       moreover have "exec (Suc p) c s q t"
       using label6 by simp
       ultimately show "\<exists>t p q. exec (Suc p) (WHILE b DO c) s q t"
       proof (auto, cases)
          fix p2 q2 xa
          assume "bval b s"
          and "exec (Suc p) c s q t"
          and "exec (Suc p2) (WHILE b DO c) t q2 xa"
          thus "\<exists>t p q. exec (Suc p) (WHILE b DO c) s q t"
          by (auto intro:while_exec)
       next
          assume "\<not> bval b s"
          thus "\<exists>t p q. exec (Suc p) (WHILE b DO c) s q t"
          by (auto intro:exec.intros)
       qed
   qed
qed

(* while_loop syntactically checks whether a given 
   command only contains while loops where the while 
   condition is syntactically satisfied and the variable 
   decrements condition is syntactically satisfied in 
   the body of the while. *) 
inductive while_loop::"com \<Rightarrow> bool" where
   "while_loop SKIP" |
   "while_loop (_ _ ::= _)" |
   "while_loop c1 \<Longrightarrow> while_loop c2
       \<Longrightarrow> while_loop (c1;;c2)" |
   "while_loop c1 \<Longrightarrow> while_loop c2
       \<Longrightarrow> while_loop (IF _ THEN c1 ELSE c2)" |
   "while_loop c \<Longrightarrow> var_decrements c x \<Longrightarrow> cond_loop b x
       \<Longrightarrow> while_loop (WHILE b DO c)" 

(* we show that syntactical while_loop implies that
   semantically the big step with counting terminates. *)
lemma while_loop_to_exec:"while_loop c \<Longrightarrow> \<exists>t m n. exec (Suc m) c s n t"
proof (induction arbitrary: s rule:while_loop.induct)
   fix x e s i
   show "\<exists>t m n. exec (Suc m) (x i ::= e) s n t"
   by (auto intro:exec.intros)
next
   fix c1 c2 s
   assume "\<And>s. \<exists>t m n. exec (Suc m) c1 s n t"
   and "\<And>s. \<exists>t m n. exec (Suc m) c2 s n t"
   thus "\<exists>t m n. exec (Suc m) (c1;; c2) s n t"
   by (blast intro:seq_exec)
next
   fix c1 c2 s b
   assume "\<And>s. \<exists>t m n. exec (Suc m) c1 s n t"
   and "\<And>s. \<exists>t m n. exec (Suc m) c2 s n t"
   thus "\<exists>t m n. exec (Suc m) (IF b THEN c1 ELSE c2) s n t"
   by (blast intro:exec.intros)
next
   fix c b x s
   assume "\<And>s. \<exists>t m n. exec (Suc m) c s n t"
   and "var_decrements c x"
   and "cond_loop b x"
   thus "\<exists>t m n. exec (Suc m) (WHILE b DO c) s n t"
   using term_w by simp
qed (blast intro:exec.intros)

(* we show that syntactical while_loop implies that
   semantically the big step terminates. *)
theorem while_loop_to_big_step:"while_loop c \<Longrightarrow> \<exists>t. big_step c s t"
proof (rule exE)
   assume " while_loop c"
   thus "\<exists>t m n. exec (Suc m) c s n t"
   by (auto intro: while_loop_to_exec)
next
   fix x
   assume "\<exists>m n. exec (Suc m) c s n x"
   thus "\<exists>t. big_step c s t"
   by (auto intro:exec_to_big_step)
qed

subsection "Section 3: lastIndexOf Example"

(**************************************************************)
(* We show that some code implements a lastIndexOf function.  *)
(* We only show being a function and termination. Because of  *)
(* lack of time, we don't show correctness. The code reads:   *)
(*                                                            *)
(*      lastIndexOf = WHILE (0<i & a[i-1]!=b) DO i=i-1;       *)
(*                                                            *)
(* The code would then be started with i the length of the    *)
(* array a. The code would then return i-1, so to indicate    *)
(* by -1 that no element was found or else to return the last *)
(* index where an element matching b was found.               *)
(**************************************************************)

abbreviation (input) lastIndexOf::com where
  "lastIndexOf == WHILE (And (Less (N 0) (V ''i'' []))
        (Not (Eq (V ''a'' [(Minus (V ''i'' []) (N 1))]) (V ''b'' [])))) DO 
                  ''i'' [] ::= (Minus (V ''i'' []) (N 1))"

value lastIndexOf

(* Here we show that the lastIndexOf does not modify b *)
theorem "var_no_assign lastIndexOf ''b''"
apply (simp add:var_no_assign.intros)
done

(* Here we show that the lastIndexOf does not modify a *)
theorem "var_no_assign lastIndexOf ''a''"
apply (simp add:var_no_assign.intros)
done

(* Here we show that the lastIndexOf does terminate *)
theorem "while_loop lastIndexOf"
apply (rule while_loop.intros)
apply (rule while_loop.intros)
apply (rule var_decrements.intros)
apply (simp)
apply (rule cond_loop.intros)
apply (rule cond_loop.intros)
done

end
