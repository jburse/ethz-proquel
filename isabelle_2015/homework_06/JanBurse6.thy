header "IN2055, Homework 6, Jan Burse
        24.11.14, jburse@hispeed.ch"

theory JanBurse6

imports "~~/src/HOL/IMP/Com"
        "~~/src/HOL/IMP/AExp"
        "~~/src/HOL/IMP/BExp"

begin

section "Homework 6.1: While Free Programs
         Again more progress in applying Isar, proof done by 
         detour over the counting exec from my Homework 5.1, 
         but whereas I tried a fun exec last time, I was now 
         trying an inductive exec, which was easier to use"

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

lemma seq_exec[simp]:"exec m1 c1 s1 n1 s2 \<Longrightarrow>
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

lemma while_exec[simp]:"bval b s1 \<Longrightarrow>
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

(* lemma is not used, left over from homework 5.1 *)
lemma big_step_to_exec:"big_step c s t \<Longrightarrow> \<exists>m n. exec (Suc m) c s n t"
proof (induction c s t rule:big_step.induct)
  fix s 
  show "\<exists>m n. exec (Suc m) SKIP s n s" 
  by (auto intro:exec.intros)
next
  fix x e s
  show "\<exists>m n.  exec (Suc m) (x ::= e) s n (s(x := aval e s))"
  by (auto intro:exec.intros)
next
  fix c1 s1 s2 c2 s3
  assume "\<exists>m n. exec (Suc m) c1 s1 n s2"
  and "\<exists>m n. exec (Suc m) c2 s2 n s3"
  thus "\<exists>m n. exec (Suc m) (c1;; c2) s1 n s3"
  by (auto intro: seq_exec)
next
  fix b s c1 t c2
  assume "bval b s"
  and "\<exists>m n. exec (Suc m) c1 s n t"
  thus "\<exists>m n. exec (Suc m) (IF b THEN c1 ELSE c2) s n t"
  by (auto intro:exec.intros)
next
  fix b s c1 t c2
  assume "\<not> bval b s"
  and "\<exists>m n. exec (Suc m) c2 s n t"
  thus "\<exists>m n. exec (Suc m) (IF b THEN c1 ELSE c2) s n t"
  by (auto intro:exec.intros)
next
  fix b s1 c s2 s3
  assume "bval b s1"
  and "\<exists>m n. exec (Suc m) c s1 n s2"
  and "\<exists>m n. exec (Suc m) (WHILE b DO c) s2 n s3"
  thus "\<exists>m n. exec (Suc m) (WHILE b DO c) s1 n s3"
  by (auto intro: while_exec)
next
  fix b s c
  assume "\<not> bval b s"
  thus "\<exists>m n. exec (Suc m) (WHILE b DO c) s n s"
  by (auto intro:exec.intros)
qed

thm exec.induct
thm big_step.intros

lemma exec_to_big_step:"exec (Suc m) c s n t \<Longrightarrow> big_step c s t"
proof (induction rule:exec.induct) 
  fix f s
  show "big_step SKIP s s"
  by (auto intro:big_step.intros)
next
  fix f x e s
  show "big_step (x ::= e) s (s(x := aval e s))"
  by (auto intro:big_step.intros)
next
  fix c1 s1 s2 c2 s3
  assume "big_step c1 s1 s2"
  and "big_step c2 s2 s3"
  thus "big_step (c1;; c2) s1 s3"
  by (auto intro:big_step.intros)
next
  fix b s1 c1 s2 c2
  assume "bval b s1"
  and "big_step c1 s1 s2"
  thus "big_step (IF b THEN c1 ELSE c2) s1 s2"
  by (auto intro:big_step.intros)
next
  fix b s1 c1 s2 c2
  assume "\<not>bval b s1"
  and "big_step c2 s1 s2"
  thus "big_step (IF b THEN c1 ELSE c2) s1 s2"
  by (auto intro:big_step.intros)
next
  fix b s1 c s2 s3
  assume "bval b s1"
  and "big_step c s1 s2"
  and "big_step (WHILE b DO c) s2 s3"
  thus "big_step (WHILE b DO c) s1 s3"
  by (auto intro:big_step.intros)
next
  fix b s1 c
  assume "\<not>bval b s1"
  thus "big_step (WHILE b DO c) s1 s1"
  by (auto intro:big_step.intros)
qed

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
   by (blast intro: seq_exec)
next
   fix c1 c2 b s
   assume "\<And>s. \<exists>t m n. exec (Suc m) c1 s n t"
   and "\<And>s. \<exists>t m n. exec (Suc m) c2 s n t"
   thus "\<exists>t m n. exec (Suc m) (IF b THEN c1 ELSE c2) s n t"
   by (blast intro:exec.intros)
qed

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

end
