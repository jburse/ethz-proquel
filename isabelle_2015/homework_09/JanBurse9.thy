header "IN2055, Homework 9, Jan Burse
        15.12.14, jburse@hispeed.ch"

theory JanBurse9

imports Main

begin

section "Homework 9.2: Knaster-Tarski Fixed Point Theorem"

(* Conducted an experiment in proving Knaster-Tarski for 
   sets from thin air. Means I wasn't using the lattice 
   framework but instead bootstrapped the usual lattice 
   operators on sets from the basic logical operators. 

   Then was proving the lfp and gfp theorem in parallel.
   Wanted to see whether both theorems use the same
   proof methods. But sometimes lfp goes through with 
   simp whereas gfp requires auto. *)

(* Translation table:
    Lattice:            Here:
    \<Inter>                   inf
    \<Union>                   sup
    \<subseteq>                   les *)

(* Definition of the set lattice *)

fun inf::"'a set set \<Rightarrow> 'a set" where
   "inf A = {x. \<forall>a. (a \<in> A \<longrightarrow> x \<in> a)}"

fun sup::"'a set set \<Rightarrow> 'a set" where
   "sup A = {x. \<exists>a. (a \<in> A \<and> x \<in> a)}"

fun les::"'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
   "les A B = (\<forall>x. (x \<in> A \<longrightarrow> x \<in> B))"

(* Show some properties of the set lattice *)

lemma lemma_1_1:"\<forall>x. (x \<in> A \<longrightarrow> les b x) \<Longrightarrow> les b (inf A)"
by (simp)

lemma lemma_1_2:"\<forall>x. (x \<in> A \<longrightarrow> les x b) \<Longrightarrow> les (sup A) b"
by (auto)

lemma lemma_2:"les a b \<Longrightarrow> les b c \<Longrightarrow> les a c"
by (auto)

lemma lemma_3:"les a b \<Longrightarrow> les b a \<Longrightarrow> a = b"
by (auto)

lemma lemma_4_1:"a = b \<Longrightarrow> les a b"
by (simp)

lemma lemma_4_2:"a = b \<Longrightarrow> les b a"
by (simp)

(* Show that the Knaster-Tarski constructions are minimal resp. maximal. *)

fun lfp::"('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
   "lfp f = inf {a. les (f a) a}"

fun gfp::"('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
   "gfp f = sup {a. les a (f a)}"

lemma lemma_5_1:"les (f a) a \<longrightarrow> les (lfp f) a"
by (simp)

lemma lemma_5_2:"les a (f a) \<longrightarrow> les a (gfp f)"
by (auto)

theorem "f a = a \<Longrightarrow> les (lfp f) a"
using lemma_5_1 lemma_4_1 by (blast)

theorem "f a = a \<Longrightarrow> les a (gfp f)"
using lemma_5_2 lemma_4_2 by (blast)

(* Show that the Knaster-Tarski constructions for sets are fix-points. *)

fun mono::"('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
   "mono f = (\<forall>x y. (les x y) \<longrightarrow> (les (f x) (f y)))"

lemma lemma_6_1:"mono f \<Longrightarrow> les (f (lfp f)) (lfp f)"
proof -
    assume label1:"mono f"
    have label3:"\<forall>a. (les (lfp f) a \<longrightarrow> les (f (lfp f)) (f a))"
    using label1 by (simp del:les.simps)
    have label4:"\<forall>a. (les (f a) a \<longrightarrow> les (f (lfp f)) a)"
    using lemma_5_1 label3 lemma_2 by (blast)
    show "les (f (lfp f)) (lfp f)"
    using label4 lemma_1_1[of "{a. les (f a) a}"] by (simp del:les.simps)
qed

lemma lemma_6_2:"mono f \<Longrightarrow> les (gfp f) (f (gfp f))"
proof -
    assume label1:"mono f"
    have label3:"\<forall>a. (les a (gfp f) \<longrightarrow> les (f a) (f (gfp f)))"
    using label1 by (simp del:les.simps)
    have label4:"\<forall>a. (les a (f a) \<longrightarrow> les a (f (gfp f)))"
    using lemma_5_2 label3 lemma_2 by (blast)
    show "les (gfp f) (f (gfp f))"
    using label4 lemma_1_2[of " {a. les a (f a)}"] by (simp del:les.simps)
qed

lemma lemma_7_1:"mono f \<Longrightarrow> les (lfp f) (f (lfp f))"
proof -
    assume label1:"mono f"
    have label2:"les (f (lfp f)) (lfp f) \<Longrightarrow> les (f (f (lfp f))) (f (lfp f))"
    using label1 by (simp del:les.simps)
    have label3:"les (f (f (lfp f))) (f (lfp f)) \<Longrightarrow> les (lfp f) (f (lfp f))"
    by (simp)
    show "les (lfp f) (f (lfp f))"
    using label1 label2 label3 lemma_6_1 by (blast)
qed

lemma lemma_7_2:"mono f \<Longrightarrow> les (f (gfp f)) (gfp f)"
proof -
    assume label1:"mono f"
    have label2:"les (gfp f) (f (gfp f)) \<Longrightarrow> les (f (gfp f)) (f (f (gfp f)))"
    using label1 by (simp del:les.simps)
    have label3:"les (f (gfp f)) (f (f (gfp f))) \<Longrightarrow>  les (f (gfp f)) (gfp f)"
    by (auto)
    show "les (f (gfp f)) (gfp f)"
    using label1 label2 label3 lemma_6_2 by (blast)
qed

theorem "mono f \<Longrightarrow> f (lfp f) = lfp f"
using lemma_6_1 lemma_7_1 lemma_3 by (blast)

theorem "mono f \<Longrightarrow> f (gfp f) = gfp f"
using lemma_6_2 lemma_7_2 lemma_3 by (blast)

end
