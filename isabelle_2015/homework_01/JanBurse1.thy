header "IN2055, Homework 1, Jan Burse
        20.10.14, jburse@hispeed.ch"

theory JanBurse1

imports Main

begin

section "Homework 1.1: Two to the power of n"

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
   "add 0 n = n" |
   "add (Suc n) m = Suc (add n m)"

value "add 2 3"

thm add.simps

fun mul :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
   "mul 0 n = 0" |
   "mul (Suc n) m = add (mul n m) m"

value "mul 2 3"

fun pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
   "pow n 0 = 1" |
   "pow n (Suc m) = mul (pow n m) n"

value "pow 2 3"

lemma add_assoc[simp]: "add (add a b) c = add a (add b c)"
apply (induction a)
apply (auto)
done

lemma add_zero[simp]: "add a 0 = a"
apply (induction a)
apply (auto)
done

lemma add_succ[simp]: "add a (Suc b) = Suc (add a b)"
apply (induction a)
apply (auto)
done

lemma mul_zero[simp]: "mul a 0 = 0"
apply (induction a)
apply (auto)
done

lemma mul_succ[simp]: "mul a (Suc b) = add a (mul a b)"
apply (induction a)
apply (auto)
done

lemma mul_dist[simp]: "mul (add a b) c = add (mul a c) (mul b c)"
apply (induction b)
apply (auto)
done
 
lemma mul_assoc[simp]: "mul (mul a b) c = mul (mul a c) b"
apply (induction c)
apply (auto)
done

lemma pow_dist[simp]: "pow n (add m q) = mul (pow n m) (pow n q)"
apply (induction m)
apply (auto)
done

fun pow2 :: "nat \<Rightarrow> nat" where
   "pow2 n = pow 2 n"

value "pow2 3"

theorem "pow2 (add n m) = mul (pow2 n) (pow2 m)"
apply (auto)
done

section "Homework 1.2: Doubling a List"

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil a = (a # Nil)" |
  "snoc (x # xs) a = x # (snoc xs a)"

value "snoc [a,b,c] d"

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil" |
  "rev (x # xs) = snoc (rev xs) x"

value "rev [a,b,c]"

fun double :: "'a list \<Rightarrow> 'a list" where
  "double [] = []" |
  "double (x # xs) = x # (x # (double xs))"

value "double [a, b, c]"

lemma double_snoc[simp]: "double (snoc xs x) = (snoc (snoc (double xs) x) x)"
apply (induction xs)
apply (auto)
done

theorem rev_double: "rev (double xs) = double (rev xs)"
apply (induction xs)
apply (auto)
done

end
