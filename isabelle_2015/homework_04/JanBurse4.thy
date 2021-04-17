header "IN2055, Homework 4, Jan Burse
        11.11.14, jburse@hispeed.ch"

theory JanBurse4

imports "~~/src/HOL/IMP/AExp"

begin

section "Homework 4.1: (Deterministic) Labeled Transition Systems
         Unfortunately only apply Solution and no Isar Solution"

type_synonym ('q, 'l) lts = "'q \<Rightarrow> 'l \<Rightarrow> 'q \<Rightarrow> bool"

inductive word::"('q, 'l) lts \<Rightarrow> 'q \<Rightarrow> 'l list \<Rightarrow> 'q \<Rightarrow> bool" where
   "word g x [] x" |
   "g x c y \<Longrightarrow> word g y cs z \<Longrightarrow> word g x (c # cs) z"

thm word.induct

inductive_cases wordNilE[elim]:  "word g x [] y"
inductive_cases wordConsE[elim!]:  "word g x (c # cs) y"

thm wordNilE
thm wordConsE

fun det::"('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool" where
     "det g = (\<forall>x y z c. g x c y \<longrightarrow> g x c z \<longrightarrow> y = z)"

theorem "word g x w y \<Longrightarrow> word g x w z \<Longrightarrow> det g \<Longrightarrow> y = z"
apply (induction rule:word.induct)
apply (auto)
done

section "Homework 4.2: Dyck Grammars
         Tried first showing T and S equivalent R = e | A R B | R R
         then horizon(x)=0 & forall y (y prefix x --> horizon(y)>=0)
         but both didn't work out, got stuck in splitting X @ Y = Z @ T"

datatype ab = A | B

fun horizon::"ab list \<Rightarrow> int" where
   "horizon [] = 0" |
   "horizon (x # xs) = horizon xs + (case x of A \<Rightarrow> 1 | B \<Rightarrow> -1)"

lemma distr[simp]: "horizon (xs @ ys) = horizon xs + horizon ys"
apply (induction xs arbitrary: ys)
apply (auto)
done

inductive S::"ab list \<Rightarrow> bool" where
   "S []" |
   "S xs \<Longrightarrow> S ys \<Longrightarrow> S (A # xs @ B # ys)" 

inductive S'::"ab list \<Rightarrow> bool" where
   "S' []" |
   "S xs \<Longrightarrow> S' ys \<Longrightarrow> S' (A # xs @ B # ys)" |
   "S' xs \<Longrightarrow> S' (A # xs)" 

lemma zero[simp]: "S xs \<Longrightarrow> (horizon xs) = 0"
apply (induction rule:S.induct)
apply (auto)
done

lemma positive[simp]: "S' xs \<Longrightarrow> (horizon xs) \<ge> 0"
apply (induction rule:S'.induct)
apply (auto)
done

lemma "S zs \<Longrightarrow> zs = xs @ ys \<Longrightarrow> S' xs"
apply (induction arbitrary: xs ys rule:S.induct)
apply (auto intro:S'.intros)
sorry

end
