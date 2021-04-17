header "IN2055, Homework 8, Jan Burse
        09.12.14, jburse@hispeed.ch"

theory JanBurse8

imports "~~/src/HOL/IMP/Com"
        "~~/src/HOL/IMP/AExp"
        "~~/src/HOL/IMP/BExp"

begin

section "Homework 8.2: Terminating While Loops,
         the code includes a copy of my homework 6.1
         solution which is the basis for this solution."

(****************************************************************)
(* Homework 6.1                                                 *)
(****************************************************************)

value "aval (Plus (V ''x'') (N 1)) <>"

inductive exec::"nat \<Rightarrow> com \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" where
   "exec (Suc f) SKIP s f s" |
   "exec (Suc f) (x ::= e) s f (s(x := aval e s))" |
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

code_pred exec .

values "{(f, s). exec 0 SKIP <> f s}"
values "{(f, s). exec 1 SKIP <> f s}"
values "{(f, s). exec 3 (WHILE (Less (V ''x'') (N 1)) 
            DO (''x'' ::= (Plus (V ''x'') (N 1)))) <> f s}"
values "{(f, s). exec 4 (WHILE (Less (V ''x'') (N 1)) 
            DO (''x'' ::= (Plus (V ''x'') (N 1)))) <> f s}"

thm exec.simps
thm exec.induct
thm exec.intros

lemma less_exec[simp]:"exec m c s n t \<Longrightarrow> m>n"
apply (induction rule:exec.induct)
apply (auto)
done

lemma shift_exec1[simp]:"exec m c s n t \<Longrightarrow> exec (m+k) c s (n+k) t"
apply (induction arbitrary: k rule:exec.induct)
apply (auto intro:exec.intros)
apply (intro exec.intros)
apply (auto)
apply (intro exec.intros)
apply (auto)
done

lemma shift_exec2[simp]:"exec m c s n t \<Longrightarrow> exec (k+m) c s (k+n) t"
apply (induction arbitrary: k rule:exec.induct)
apply (auto intro:exec.intros)
apply (intro exec.intros)
apply (auto)
apply (intro exec.intros)
apply (auto)
done

lemma seq_exec:"exec m1 c1 s1 n1 s2 \<Longrightarrow>
                exec m2 c2 s2 n2 s3 \<Longrightarrow>
                exec (Suc (m1+m2)) (c1;; c2) s1 (n1+n2) s3"
proof (intro exec.intros)
   assume "exec m1 c1 s1 n1 s2"
   thus "exec (m1 + m2) c1 s1 (n1 + m2) s2"
   by (auto)
next
   assume "exec m1 c1 s1 n1 s2"
   thus "n1 + m2 < m1 + m2"
   by (auto)
next
   assume "exec m2 c2 s2 n2 s3"
   thus "exec (n1 + m2) c2 s2 (n1 + n2) s3"
   by (auto)
qed

lemma while_exec:"bval b s1 \<Longrightarrow>
                exec m1 c s1 n1 s2 \<Longrightarrow>
                exec m2 (WHILE b DO c) s2 n2 s3 \<Longrightarrow>
                exec (Suc (m1+m2)) (WHILE b DO c) s1 (n1+n2) s3"
proof (intro exec.intros)
   assume "bval b s1"
   thus "bval b s1"
   by (auto)
next
   assume "exec m1 c s1 n1 s2"
   thus "exec (m1 + m2) c s1 (n1 + m2) s2"
   by (auto)
next
   assume "exec m1 c s1 n1 s2"
   thus "n1 + m2 < m1 + m2"
   by (auto)
next
   assume "exec m2 (WHILE b DO c) s2 n2 s3"
   thus "exec (n1 + m2) (WHILE b DO c) s2 (n1 + n2) s3"
   by (auto)
qed

inductive big_step::"com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
   "big_step SKIP s s" |
   "big_step (x ::= e) s (s(x := aval e s))" |
   "big_step c1 s1 s2 \<Longrightarrow> big_step c2 s2 s3 \<Longrightarrow> big_step (c1 ;; c2) s1 s3" |
   "bval b s \<Longrightarrow> big_step c1 s t \<Longrightarrow> big_step (IF b THEN c1 ELSE c2) s t" |
   "\<not>bval b s \<Longrightarrow> big_step c2 s t \<Longrightarrow> big_step (IF b THEN c1 ELSE c2) s t" |
   "bval b s1 \<Longrightarrow> big_step c s1 s2 \<Longrightarrow> big_step (WHILE b DO c) s2 s3 \<Longrightarrow> big_step (WHILE b DO c) s1 s3" |
   "\<not>bval b s \<Longrightarrow> big_step (WHILE b DO c) s s"

code_pred big_step .

values "{t. big_step SKIP <> t}"
values "{map t [''x'', ''y'']|t. big_step (WHILE (Less (V ''x'') (N 1)) 
             DO (''x'' ::= (Plus (V ''x'') (N 1)))) <> t}"

thm big_step.induct

lemma "big_step c s t \<Longrightarrow> \<exists>m n. exec (Suc m) c s n t"
proof (induction c s t rule:big_step.induct)
  fix x e s
  show "\<exists>m n.  exec (Suc m) (x ::= e) s n (s(x := aval e s))"
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

thm exec.induct
thm big_step.intros

lemma exec_to_big_step:"exec (Suc m) c s n t \<Longrightarrow> big_step c s t"
proof (induction rule:exec.induct) 
  fix f x e s
  show "big_step (x ::= e) s (s(x := aval e s))"
  by (auto intro:big_step.intros)
qed (auto intro:big_step.intros)

inductive while_free::"com \<Rightarrow> bool" where
     "while_free SKIP" |
     "while_free (x ::= e)" |
     "while_free c1 \<Longrightarrow> while_free c2 \<Longrightarrow> while_free (c1;; c2)" |
     "while_free c1 \<Longrightarrow> while_free c2 \<Longrightarrow> while_free (IF b THEN c1 ELSE c2)"

thm while_free.induct

lemma while_free_to_exec:"while_free c \<Longrightarrow> \<exists>t m n. exec (Suc m) c s n t"
proof (induction arbitrary: s rule:while_free.induct)
   fix s
   show "\<exists>t m n. exec (Suc m) SKIP s n t"
   by (auto intro:exec.intros)
next
   fix x e s
   show "\<exists>t m n. exec (Suc m) (x ::= e) s n t"
   by (auto intro:exec.intros)
next
   fix c1 c2 s
   assume "\<And>s. \<exists>t m n. exec (Suc m) c1 s n t"
   and "\<And>s. \<exists>t m n. exec (Suc m) c2 s n t"
   thus "\<exists>t m n. exec (Suc m) (c1;; c2) s n t"
   by (blast intro:seq_exec)
qed (blast intro:exec.intros)

thm while_free_to_exec

theorem while_free_to_big_step:"while_free c \<Longrightarrow> \<exists>t. big_step c s t"
proof (rule exE)
   assume "while_free c"
   thus "\<exists>t m n. exec (Suc m) c s n t"
   by (auto intro:while_free_to_exec)
next
   fix x
   assume "\<exists>m n. exec (Suc m) c s n x"
   thus "\<exists>t. big_step c s t"
   by (auto intro:exec_to_big_step)
qed

theorem no_big_step_to_no_while_free:"\<exists>s. \<forall>t. \<not> big_step c s t \<Longrightarrow> \<not> while_free c"
proof (rule contrapos_nn)
   assume "\<exists>s. \<forall>t. \<not> big_step c s t"
   thus "\<not> (\<forall>s. \<exists>t. big_step c s t)"
   by (auto)
next
   assume "while_free c"
   thus "\<forall>s. \<exists>t. big_step c s t"
   by (auto intro:while_free_to_big_step)
qed

(****************************************************************)
(* Homework 8.2                                                 *)
(****************************************************************)

(* Translation table:
       In homework            Here
       invar                  var_no_assign
       incr                   var_decrement
       term                   while_simple 
*)

(* I first tried to proof that while loops of the form

         WHILE (x < b) DO c

   where x is strictly increasing do terminate. But I run into 
   complexity troubles making the prove because of the additional
   parameter. So I choose the simpler but essentially equivalent
   problem of proving that while loops of the form 
    
         WHILE (0 < x ) DO c

   where x is strictly decreasing do terminate. Interestingly
   the proof went through with nat_less_induct already, there
   was no need for int_less_induct.  *)

(* var_no_assign syntactically checks whether in a given
   command a given variable does not receive any assignment *)
inductive var_no_assign::"com \<Rightarrow> vname \<Rightarrow> bool" where
   "var_no_assign SKIP _" |
   "x \<noteq> y \<Longrightarrow> var_no_assign (x ::= e) y" |
   "var_no_assign c1 x \<Longrightarrow> var_no_assign c2 x
      \<Longrightarrow> var_no_assign (c1;; c2) x" |
   "var_no_assign c1 x \<Longrightarrow> var_no_assign c2 x
      \<Longrightarrow> var_no_assign (IF b THEN c1 ELSE c2) x" |
   "var_no_assign c x
      \<Longrightarrow> var_no_assign (WHILE b DO c) x"

inductive_cases var_no_assign_elim:"var_no_assign c x"

thm var_no_assign_elim

lemma var_no_assign_no_change_state:"exec m c s n t \<Longrightarrow> var_no_assign c x \<Longrightarrow> s x = t x"
proof (induction arbitrary: x rule:exec.induct)
   fix c s1 b s3 x and s2::state
   assume "\<And>x. var_no_assign c x \<Longrightarrow> s1 x = s2 x"
   and "\<And>x. var_no_assign (WHILE b DO c) x \<Longrightarrow> s2 x = s3 x"
   and "var_no_assign (WHILE b DO c) x" 
   thus "s1 x = s3 x"
   by (fastforce elim:var_no_assign_elim)
qed (auto elim:var_no_assign_elim)

(* var_decrement syntactically checks whether in a given
   command a given variable is decremented by a positive 
   non-zero not necessarily unique value *)
inductive var_decrement::"com \<Rightarrow> vname \<Rightarrow> bool" where
   "n < 0 \<Longrightarrow> var_decrement (x ::= (Plus (V x) (N n))) x" |
   "var_no_assign c1 x \<Longrightarrow> var_decrement c2 x
      \<Longrightarrow> var_decrement (c1;; c2) x" |
   "var_decrement c1 x \<Longrightarrow> var_no_assign c2 x
      \<Longrightarrow> var_decrement (c1;; c2) x" |
   "var_decrement c1 x \<Longrightarrow> var_decrement c2 x
      \<Longrightarrow> var_decrement (c1;; c2) x" |
   "var_decrement c1 x \<Longrightarrow> var_decrement c2 x
      \<Longrightarrow> var_decrement (IF b THEN c1 ELSE c2) x"

inductive_cases var_decrement_elim:"var_decrement c x"

thm var_decrement_elim

lemma var_incrememt_strict_mono_state:"exec m c s n t \<Longrightarrow> var_decrement c x \<Longrightarrow> s x > t x"
proof (induction arbitrary: x rule:exec.induct)
   fix f1 c1 s1 f2 s2 c2 f3 s3 x
   assume "var_decrement (c1;; c2) x"
   and "exec f1 c1 s1 f2 s2"
   and "\<And>x. var_decrement c1 x \<Longrightarrow> s1 x > s2 x"
   and "exec f2 c2 s2 f3 s3"
   and "\<And>x. var_decrement c2 x \<Longrightarrow> s2 x > s3 x"
   thus "s1 x > s3 x"
   proof (cases)
      assume label1:"exec f1 c1 s1 f2 s2"
      and label2:"var_no_assign c1 x"
      and label3:"\<And>x. var_decrement c2 x \<Longrightarrow> s2 x > s3 x"
      and label4:"var_decrement c2 x"
      have "s1 x = s2 x"
      using var_no_assign_no_change_state label1 label2 by simp
      moreover have "s2 x > s3 x"
      using label3 label4 by simp
      ultimately show "s1 x > s3 x" by simp
   next
      assume label1:"\<And>x. var_decrement c1 x \<Longrightarrow> s1 x > s2 x"
      and label2:"var_decrement c1 x"
      and label3:"exec f2 c2 s2 f3 s3"
      and label4:"var_no_assign c2 x"
      have "s1 x > s2 x"
      using label1 label2 by simp
      moreover have "s2 x = s3 x"
      using var_no_assign_no_change_state label3 label4 by simp
      ultimately show "s1 x > s3 x" by simp
   qed (fastforce)
qed (auto elim:var_decrement_elim)

(* The crucial lemma about termination.
   Much work, quantifiers everywhere, such pain. *)
lemma term_w:"v = nat (s x) \<Longrightarrow> \<forall>s. \<exists>t p q. exec (Suc p) c s q t \<Longrightarrow> 
       var_decrement c x \<Longrightarrow>
       \<exists>t p q. exec (Suc p) (WHILE (Less (N 0) (V x)) DO c) s q t"
proof (induction v arbitrary: s rule:nat_less_induct, cases)
   fix n and s::state
   assume "n \<le> 0"
   and "n = nat (s x)"
   thus "\<exists>t p q. exec (Suc p) (WHILE (Less (N 0) (V x)) DO c) s q t"
   by (force intro:exec.intros)
next
   fix n::nat and s::state
   assume label0:"\<not> n \<le> 0"
   assume label1:"n = nat (s x)"
   assume label2:"\<forall>s. \<exists>t p q. exec (Suc p) c s q t"
   assume label3:"var_decrement c x"
   assume label4:"\<forall>m<n.
          \<forall>xa. m = nat (xa x) \<longrightarrow>
                (\<forall>s. \<exists>t p q. exec (Suc p) c s q t) \<longrightarrow>
                var_decrement c x \<longrightarrow>
                (\<exists>t p q.
                    exec (Suc p)
                     (WHILE (Less (N 0) (V x)) DO c)
                     xa q t)"
   have "0 < s x"
   using label0 label1 by simp
   moreover have "\<exists>t p q. exec (Suc p) c s q t"
   using label2 by simp
   moreover have "\<forall>t p q. exec (Suc p) c s q t \<longrightarrow> t x < s x"
   using label3 var_incrememt_strict_mono_state by simp
   moreover have "\<forall>t m. (m < n \<longrightarrow> m = nat(t x) \<longrightarrow>
                (\<exists>p2 q2 t2. exec (Suc p2) (WHILE (Less (N 0) (V x)) DO c) t q2 t2))"
   using label4 label2 label3 by blast
   ultimately show "\<exists>t p q. exec (Suc p) (WHILE (Less (N 0) (V x)) DO c) s q t"
   using label1
   proof (auto)
       fix t p q
       assume label8:"0 < s x"
       assume label5:"\<forall>t. (\<exists>p q. exec (Suc p) c s q t) \<longrightarrow> t x < s x"
       assume label6:"exec (Suc p) c s q t"
       assume label7:"\<forall>t. t x < s x \<longrightarrow>
            (\<exists>p2 q2 t2.
                exec (Suc p2)
                 (WHILE Less (N 0) (V x) DO c) t
                 q2 t2)"
       have "t x < s x"
       using label5 label6 by auto
       moreover have "t x < s x \<longrightarrow>
            (\<exists>p2 q2 t2.
                exec (Suc p2)
                 (WHILE Less (N 0) (V x) DO c) t
                 q2 t2)"
       using label7 by simp
       moreover have "exec (Suc p) c s q t"
       using label6 by simp
       ultimately show "\<exists>t p q. exec (Suc p) (WHILE (Less (N 0) (V x)) DO c) s q t"
       using label8 
       proof (auto)
          fix p2 q2 xa
          assume label9:"0 < s x"
          assume label10:"exec (Suc p) c s q t"
          assume label11:"exec (Suc p2) (WHILE Less (N 0) (V x) DO c) t q2 xa"
          have "bval (Less (N 0) (V x)) s" 
          using label9 by simp
          thus "\<exists>t p q. exec (Suc p) (WHILE (Less (N 0) (V x)) DO c) s q t"
          using label10 label11 by (force intro:while_exec)
       qed
   qed
qed

(* while_simple syntactically checks whether
   a given command only contains while loops that are
   zero lower bounded and decrement their variable *) 
inductive while_simple::"com \<Rightarrow> bool" where
   "while_simple SKIP" |
   "while_simple (_ ::= _)" |
   "while_simple c1 \<Longrightarrow> while_simple c2
       \<Longrightarrow> while_simple (c1;;c2)" |
   "while_simple c1 \<Longrightarrow> while_simple c2
       \<Longrightarrow> while_simple (IF _ THEN c1 ELSE c2)" |
   "while_simple c \<Longrightarrow> var_decrement c x
       \<Longrightarrow> while_simple (WHILE (Less (N 0) (V x)) DO c)" 

thm while_simple.induct

lemma while_simple_to_exec:"while_simple c \<Longrightarrow> \<exists>t m n. exec (Suc m) c s n t"
proof (induction arbitrary: s rule:while_simple.induct)
   fix x e s
   show "\<exists>t m n. exec (Suc m) (x ::= e) s n t"
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
   fix c x s
   assume "\<And>s. \<exists>t m n. exec (Suc m) c s n t"
   and "var_decrement c x"
   thus "\<exists>t m n. exec (Suc m) (WHILE Less (N 0) (V x) DO c) s n t"
   using term_w by simp
qed (blast intro:exec.intros)

theorem while_simple_to_big_step:"while_simple c \<Longrightarrow> \<exists>t. big_step c s t"
proof (rule exE)
   assume " while_simple c"
   thus "\<exists>t m n. exec (Suc m) c s n t"
   by (auto intro: while_simple_to_exec)
next
   fix x
   assume "\<exists>m n. exec (Suc m) c s n x"
   thus "\<exists>t. big_step c s t"
   by (auto intro:exec_to_big_step)
qed

end
