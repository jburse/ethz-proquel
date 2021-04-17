header "IN2055, Homework 5, Jan Burse
        17.11.14, jburse@hispeed.ch"

(** Score: 2/10
  Unfortunately, only the exec_mono-lemma, with some 
  altered specification.
  See comments below about altering homework specifications!
**)

theory JanBurse

imports "~~/src/HOL/IMP/Com"
        "~~/src/HOL/IMP/AExp"
        "~~/src/HOL/IMP/BExp"

begin

section "Homework 5.1: Fuel your executions
         More progress in applying Isar but had 
         to give up with the last induction"

(* was first trying the following definition,
   because I literally interpreted fuel as
   the number of steps taken and not as the depth *)

(** Yes, Isabelle is very good at finding termination orders.
**)

(* interestingly Isabelle/HOL found a termination
   order, I guess it took into account the guard
   f2 < f1 in the rule for (c1 ;; c2) *)

(* also interestingly when importing Big_Step as
   well Isabelle/HOL had problem with the syntax,
   especially the Some (f2, s2) \<Rightarrow> ... in the case
   statement, since it collides with the operator 
   for big step. *)

(** But you only get warnings, as the ambiguities  can be resolved
  by type-checking. So no need to worry ;)
**)

fun exec'::"nat \<Rightarrow> com \<Rightarrow> state \<Rightarrow> (nat \<times> state) option" where
   "exec' 0 _ _ = None" |
   "exec' (Suc f) SKIP s = Some (f, s)" |
   "exec' (Suc f) (x ::= e) s = Some (f, (s(x := aval e s)))" |
   "exec' (Suc f1) (c1 ;; c2) s1 = (case exec' f1 c1 s1 of
         Some (f2, s2) \<Rightarrow> (if f2<f1 then exec' f2 c2 s2 else None) |
         None \<Rightarrow> None)" |
   "exec' (Suc f) (IF b THEN c1 ELSE c2) s = (if bval b s
        then exec' f c1 s
        else exec' f c2 s)" |
   "exec' (Suc f) (WHILE b DO c) s = (if bval b s
        then exec' f (c;; (WHILE b DO c)) s
        else exec' f SKIP s)"

value "aval (Plus (V ''x'') (N 1)) <>"

(** Why did you change the argument order? 
  Always be careful if you modify functions whose definitions
  where given as part of the homework specification.
  Specifications are not meant to be modified without any comment!
  You may either argue why your specification is better than the one
  in the homework (and be lucky that we accept your argumentation ;) ),
  or, better, prove yours equivalent to the one in the homework.

  So, in your case, you might get better automation with 
  your specification, but you should have called it my_exec,
  proven a lemma "exec=my_exec", and then you could have (safely) used it.

**)
fun exec::"nat \<Rightarrow> com \<Rightarrow> state \<Rightarrow> state option" where
   "exec 0 _ _ = None" |
   "exec (Suc f) SKIP s = Some s" |
   "exec (Suc f) (x ::= e) s = Some (s(x := aval e s))" |
   "exec (Suc f) (c1 ;; c2) s1 = (case exec f c1 s1 of
         Some s2 \<Rightarrow> exec f c2 s2 |
         None \<Rightarrow> None)" |
   "exec (Suc f) (IF b THEN c1 ELSE c2) s = (if bval b s
        then exec f c1 s
        else exec f c2 s)" |
   "exec (Suc f) (WHILE b DO c) s = (if bval b s
        then exec f (c;; (WHILE b DO c)) s
        else exec f SKIP s)"

thm exec.induct
thm exec.simps

(** Why did you rename this lemma?*)
lemma exec_mono1[simp]:"exec m c s = Some t \<Longrightarrow> exec (m+k) c s = Some t"
apply (induction arbitrary: t k rule:exec.induct)
apply (auto intro:exec.simps)
apply (auto split:option.splits)
done

thm max_def

lemma exec_max1[simp]:"exec m c s = Some t \<Longrightarrow> exec (max m k) c s = Some t"
unfolding max_def
apply (auto split:if_splits)
proof -
   assume "exec m c s = Some t"
          "m\<le>k"
   then have "exec m c s = Some t"
             "\<exists>j.(m + (j::nat) = k)"
   by (auto,presburger)
   then show "exec k c s = Some t"
   by (auto)
qed

lemma exec_max2[simp]:"exec m c s = Some t \<Longrightarrow> exec (max k m) c s = Some t"
unfolding max_def
apply (auto split:if_splits)
proof -
   assume "exec m c s = Some t"
          "\<not> k \<le> m"
   then have "exec m c s = Some t"
             "\<exists>j.(m + (j::nat) = k)"
   by (auto,presburger)
   then show "exec k c s = Some t"
   by (auto)
qed

lemma exec_semi[simp]:"exec m1 c1 s1 = Some s2 \<and>
                 exec m2 c2 s2 = Some s3 \<Longrightarrow>
                 exec (Suc (max m1 m2)) (c1;;c2) s1 = Some s3"
apply (auto)
done

value "exec 0 SKIP <>"
value "exec 1 SKIP <>"
value "exec 3 (WHILE (Less (V ''x'') (N 1)) 
            DO (''x'' ::= (Plus (V ''x'') (N 1)))) <>"
value "exec 4 (WHILE (Less (V ''x'') (N 1)) 
            DO (''x'' ::= (Plus (V ''x'') (N 1)))) <>"

inductive big_step::"com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
   Skip: "big_step SKIP s s" |
   Assign: "big_step (x ::= e) s (s(x := aval e s))" |
   Seq: "big_step c1 s1 s2 \<Longrightarrow> big_step c2 s2 s3 \<Longrightarrow> big_step (c1 ;; c2) s1 s3" |
   IfTrue: "bval b s \<Longrightarrow> big_step c1 s t \<Longrightarrow> big_step (IF b THEN c1 ELSE c2) s t" |
   IfFalse: "\<not>bval b s \<Longrightarrow> big_step c2 s t \<Longrightarrow> big_step (IF b THEN c1 ELSE c2) s t" |
   WhileTrue: "bval b s \<Longrightarrow> big_step (c ;; (WHILE b DO c)) s t \<Longrightarrow> big_step (WHILE b DO c) s t" |
   WhileFalse: "\<not>bval b s \<Longrightarrow> big_step (WHILE b DO c) s s"

code_pred big_step .

values "{t. big_step SKIP <> t}"
values "{map t [''x'', ''y'']|t. big_step (WHILE (Less (V ''x'') (N 1)) 
             DO (''x'' ::= (Plus (V ''x'') (N 1)))) <> t}"

thm big_step.induct

(** You should have used big_step_induct.
  If you would have imported big_step, or copied over all of it, 
  including the section "proof automation", this would have made 
  life easier ...
**)

lemma "big_step c s t \<Longrightarrow> \<exists>m.(exec (Suc m) c s = Some t)"
apply (induction rule:big_step.induct)
sorry

end
