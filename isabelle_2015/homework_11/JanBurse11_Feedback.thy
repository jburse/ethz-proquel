(** Score: 10/10 *)

header "IN2055, Homework 11, Jan Burse
        19.01.15, jburse@hispeed.ch"

theory JanBurse

imports "~~/src/HOL/IMP/VCG"

begin

section "Homework 11.1: Program Verification"

(****************************************************************)
(* First define the program (minus), the invariant (iminus) and *)
(* and the annotated version of the program (aminus). Then also *)
(* verify that the program (minus) is the stripped version of   *)
(* the annotated version (aminus).                              *)
(****************************************************************)

abbreviation (input) minus::com where
   "minus == WHILE (Less (N 0) (V ''x'')) DO
               (''x'' ::= (Plus (V ''x'') (N (-1)));;
                ''y'' ::= (Plus (V ''y'') (N (-1))))"

value minus

abbreviation (input) iminus::"int \<Rightarrow> int \<Rightarrow> assn" where
   "iminus x y == \<lambda>s. s ''y'' - s ''x'' = y - x \<and> 0 \<le> s ''x''"

value "iminus x y"

abbreviation (input) aminus::"int \<Rightarrow> int \<Rightarrow> acom" where
   "aminus x y == {iminus x y} 
             WHILE (Less (N 0) (V ''x'')) DO
               (''x'' ::= (Plus (V ''x'') (N (-1)));;
                ''y'' ::= (Plus (V ''y'') (N (-1))))"

value "aminus x y"

lemma "strip (aminus x y) = minus"
apply (simp)
done

(****************************************************************)
(* Now define the post-condition (qminus) and the pre-condition *)
(* (pminus). Then verify the lemmas (lemma1, lemma2 and         *)
(* lemma3) for soundness and finally the soundness itself.      *)
(****************************************************************)

abbreviation (input) qminus::"int \<Rightarrow> int \<Rightarrow> assn" where
   "qminus x y == \<lambda>s. s ''y'' = y - x"

value "qminus x y"

lemma lemma1:"pre (aminus x y) (qminus x y) = (iminus x y)"
apply (simp)
done

lemma lemma2:"vc (aminus x y) (qminus x y)"
apply (simp)
done

abbreviation (input) pminus::"int \<Rightarrow> int \<Rightarrow> assn" where
   "pminus x y == \<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> x"

value "pminus x y"

lemma lemma3:"(pminus x y) s \<Longrightarrow> (iminus x y) s"
apply (simp)
done

theorem "\<turnstile> {pminus x y} strip (aminus x y) {qminus x y}"
proof (rule vc_sound')
  show "vc (aminus x y) (qminus x y)"
  using lemma2 by (simp)
next
  show "\<forall>s. ((pminus x y) s \<longrightarrow> pre (aminus x y) (qminus x y) s)"
  using lemma1 lemma3 by (simp)
qed

end
