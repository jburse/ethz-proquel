header "IN2055, Homework 2, Jan Burse
        27.10.14, jburse@hispeed.ch"

theory JanBurse
(** Score: 10/10 *)
imports "~~/src/HOL/IMP/AExp"

begin

section "Homework 2.1: Binary Search Tree"

datatype bst = Leaf | Node bst int bst

fun alfa :: "bst \<Rightarrow> int set" where (* alpha ;) Or, better use the greek letter \<alpha> !*)
   "alfa Leaf = {}" |
   "alfa (Node a i b) = (alfa a) \<union> {i} \<union> (alfa b)" 

value "alfa (Node Leaf 5 Leaf)"
value "alfa (Node (Node Leaf 2 Leaf) 5 (Node Leaf 9 Leaf))"

fun invar_left_right :: "int \<Rightarrow> bst \<Rightarrow> int \<Rightarrow> bool" where
  "invar_left_right _ Leaf _ = True" |
  "invar_left_right i (Node a j b) k = ((i<j) \<and> (j<k) \<and>
      (invar_left_right i a j) \<and> (invar_left_right j b k))"

fun invar_right :: "int \<Rightarrow> bst \<Rightarrow> bool" where
  "invar_right _ Leaf = True" |
  "invar_right j (Node a i b) = ((j<i) \<and> (invar_left_right j a i) \<and> (invar_right i b))"

fun invar_left :: "bst \<Rightarrow> int \<Rightarrow> bool" where
  "invar_left Leaf _ = True" |
  "invar_left (Node a i b) j = ((i<j) \<and> (invar_left a i) \<and> (invar_left_right i b j))"

fun invar :: "bst \<Rightarrow> bool" where
  "invar Leaf = True" |
  "invar (Node a i b) = ((invar_left a i) \<and> (invar_right i b))"

lemma helper: "((i::int)<k) \<Longrightarrow> (\<not>(k<i) \<and> (k\<noteq>i))"
apply (auto)
done

lemma bound1a: "\<lbrakk> k \<in> (alfa t); invar_left_right i t j \<rbrakk> \<Longrightarrow> k<j"
apply (induction t arbitrary: i j)
apply (auto)
apply (force)
done

lemma bound1c: "\<lbrakk> k \<in> (alfa t); invar_left_right i t j \<rbrakk> \<Longrightarrow> i<k"
apply (induction t arbitrary: i j)
apply (auto)
apply (force)
done

lemma bound1b: "\<lbrakk> k \<in> (alfa t); invar_left_right i t j \<rbrakk> \<Longrightarrow> (\<not>(k<i) \<and> (k\<noteq>i))"
apply (auto simp:bound1c helper)
done

lemma bound2a: "\<lbrakk> invar_right i t; k \<in> (alfa t) \<rbrakk> \<Longrightarrow> i<k"
apply (induction t arbitrary: i)
apply (auto simp:bound1c)
apply (force)
done

lemma bound2b: "\<lbrakk> invar_right i t; k \<in> (alfa t) \<rbrakk> \<Longrightarrow> (\<not>(k<i) \<and> (k\<noteq>i))"
apply (auto simp:bound2a helper)
done

lemma bound3a: "\<lbrakk> invar_left t j; k \<in> (alfa t) \<rbrakk> \<Longrightarrow> k<j"
apply (induction t arbitrary: j)
apply (auto simp:bound1a)
apply (force)
done

fun lookup :: "bst \<Rightarrow> int \<Rightarrow> bool" where
   "lookup Leaf _ = False" |
   "lookup (Node a i b) j = (if j=i then True
         else (if j<i then (lookup a j) else (lookup b j)))"

value "lookup (Node (Node Leaf 2 Leaf) 5 (Node Leaf 9 Leaf)) 3"
value "lookup (Node (Node Leaf 2 Leaf) 5 (Node Leaf 9 Leaf)) 5"
value "lookup (Node (Node Leaf 2 Leaf) 5 (Node Leaf 9 Leaf)) 9"
value "lookup (Node (Node Leaf 2 Leaf) 5 (Node Leaf 9 Leaf)) 2"

lemma lookup0: "lookup a i \<Longrightarrow> i \<in> (alfa a)"
apply (induction a)
apply (auto simp:if_splits)
done

lemma lookup1: "\<lbrakk> invar_left_right i t j; k \<in> (alfa t) \<rbrakk> \<Longrightarrow> lookup t k"
apply (induction t arbitrary: i j)
apply (auto simp:bound1a bound1b)
done

lemma lookup2: "\<lbrakk> invar_right i t; k \<in> (alfa t) \<rbrakk> \<Longrightarrow> lookup t k"
apply (induction t arbitrary: i)
apply (auto simp:lookup1)
apply (auto simp:bound1a)
apply (auto simp:bound2b)
done

lemma lookup3: "\<lbrakk> invar_left t i; k \<in> (alfa t) \<rbrakk> \<Longrightarrow> lookup t k"
apply (induction t arbitrary: i)
apply (auto simp:lookup1)
apply (auto simp:bound1b)
apply (auto simp:bound3a)
done

lemma lookup4: "\<lbrakk> invar t; k \<in> (alfa t) \<rbrakk> \<Longrightarrow> lookup t k"
apply (induction t)
apply (auto simp:bound2b)
apply (auto simp:bound3a)
apply (auto simp:lookup2)
apply (auto simp:lookup3)
done

theorem lookup: "invar t \<Longrightarrow> (k \<in> (alfa t) \<longleftrightarrow> (lookup t k))"
apply (auto simp:lookup4)
apply (auto simp:lookup0)
done

fun ins :: "bst \<Rightarrow> int \<Rightarrow> bst" where
  "ins Leaf i = (Node Leaf i Leaf)" |
  "ins (Node a i b) j = (if i=j then (Node a i b)
      else (if i<j then (Node a i (ins b j))
                   else (Node (ins a j) i b)))"

value "ins (ins Leaf 5) 2"
value "ins (ins Leaf 2) 5"

lemma ins0: "alfa (ins t x) = (alfa t) \<union> {x}"
apply (induction t)
apply (auto)
done

theorem ins_correct1: "invar t \<Longrightarrow> alfa (ins t k) = (alfa t) \<union> {k}"
apply (auto simp:ins0)
done

lemma ins1: "\<lbrakk> invar_left_right i t j; i<k; k<j \<rbrakk> \<Longrightarrow> invar_left_right i (ins t k) j"
apply (induction t arbitrary: i j)
apply (auto)
done

lemma ins2: "\<lbrakk> invar_left t i; k<i \<rbrakk> \<Longrightarrow> invar_left (ins t k) i"
apply (induction t arbitrary: i)
apply (auto simp:ins1)
done

lemma ins3: "\<lbrakk> invar_right i t; i<k \<rbrakk> \<Longrightarrow> invar_right i (ins t k)"
apply (induction t arbitrary: i)
apply (auto simp:ins1)
done

theorem ins_correct2: "invar t \<Longrightarrow> invar (ins t x)"
apply (induction t)
apply (auto simp:ins2)
apply (auto simp:ins3)
done

section "Homework 2.2: Normalizing Expressions"

datatype aexp' = N' val | V' vname | Plus' aexp' aexp' |
                 Mult val aexp'

fun aval' :: "aexp' \<Rightarrow> state \<Rightarrow> val" where
   "aval' (N' n) s = n" |
   "aval' (V' x) s = s(x)" |
   "aval' (Plus' a b) s = (aval' a s) + (aval' b s)" |
   "aval' (Mult i a) s = i * (aval' a s)"

value "aval' (Mult 3 (N' 2)) <>"
value "aval' (Mult 3 (V' ''x'')) < ''x'' := 2 >"

fun normal :: "aexp' \<Rightarrow> bool" where
   "normal (N' _) = True" |
   "normal (V' _) = True" |
   "normal (Plus' a b) = ((normal a) \<and> (normal b))" |
   "normal (Mult i (V' _)) = True" |
   "normal (Mult i _) = False"

value "normal (Mult 3 (N' 2))"
value "normal (Mult 3 (V' ''x''))"

thm normal.induct

fun mult :: "val \<Rightarrow> aexp' \<Rightarrow> aexp'" where
   "mult i (N' n) = (N' (i*n))" |
   "mult i (V' x) = (Mult i (V' x))" |
   "mult i (Plus' a b) = (Plus' (mult i a) (mult i b))" |
   "mult i (Mult j a) = (Mult (i*j) a)"

value "mult 3 (Plus' (V' x) (V' y))"
value "mult 3 (Mult 2 (V' x))"

lemma normal_mult[simp]: "normal a \<Longrightarrow> normal (mult i a)"
apply (induction a rule: normal.induct)
apply (auto)
done

thm algebra_simps

lemma move_mult[simp] : "aval' (mult i a) s = i * aval' a s"
apply (induction a)
apply (auto simp:algebra_simps)
done

fun normalize :: "aexp' \<Rightarrow> aexp'" where
   "normalize (N' n) = (N' n)" |
   "normalize (V' x) = (V' x)" |
   "normalize (Plus' a b) = (Plus' (normalize a) (normalize b))" |
   "normalize (Mult i a) = mult i (normalize a)"

thm normalize.induct

theorem normal_normalize: "normal (normalize a)"
apply (induct a rule:normalize.induct)
apply (auto)
done

theorem sound_normalize: "aval' (normalize a) s = aval' a s"
apply (induction a)
apply (auto)
done

end
