header "IN2055, Homework 7, Jan Burse
        01.12.14, jburse@hispeed.ch"

theory JanBurse7

imports "~~/src/HOL/IMP/AExp"
        "~~/src/HOL/IMP/BExp"
        "~~/src/HOL/IMP/Star"

begin

section "Homework 7.2: Compiling REPEAT
         Could solve this homework in about 1 hour, but before that spent 
         two days trying to do a custom big step framework and
         corresponding proof from scratch independent from the given
         template as an exercise for myself. Now have already a little 
         better understanding of Isar from, for example can explain the
         following example in terms of sequent calculus:

             lemma (\<And>x y. p x y) \<Longrightarrow> p z z
             proof -
                assume label:\<And>x y. p x y
                from label[where x=z and y=z] show p z z
             by (simp)
             qed

         But still have problems fully understanding Isar moreover(*),
         so did this homework, the RepeatFalse case, more or less by 
         copy paste analogy from the WhileTrue case despite its use of
         Isar moreover. For the RepeatTrue case there is no case needed 
         since it is automatically done by the last fastforce.

         (*) Found this link, when already two days had passed:
         http://www21.in.tum.de/~ballarin/belgrade08-tut/session05/session05.pdf"

datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 61] 61)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 61] 61)
(* begin mod *)
      | Repeat com bexp         ("(REPEAT _/ UNTIL _)"  [0, 61] 61)
(* end mod *)

subsection "Big-Step Semantics of Commands"

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"
(* begin mod *) |
RepeatTrue: "\<lbrakk> (c,s\<^sub>1) \<Rightarrow> s\<^sub>2; bval b s\<^sub>2 \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b,s\<^sub>1) \<Rightarrow> s\<^sub>2" |
RepeatFalse:
"\<lbrakk> (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  \<not> bval b s\<^sub>2;  (REPEAT c UNTIL b, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (REPEAT c UNTIL b, s\<^sub>1) \<Rightarrow> s\<^sub>3"
(* end mod *)

text{* Proof automation: *}

declare big_step.intros [intro]

lemmas big_step_induct = big_step.induct[split_format(complete)]


subsection "Rule inversion"

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

(* begin mod *)
inductive_cases RepeatE[elim]: "(REPEAT c UNTIL b,s) \<Rightarrow> t"
thm RepeatE
(* end mod *)

abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
by blast

subsection "Execution is deterministic"

theorem big_step_determ: "\<lbrakk> (c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induction arbitrary: u rule: big_step.induct) blast+

text {* 
  In the following, we use the length of lists as integers 
  instead of natural numbers. Instead of converting @{typ nat}
  to @{typ int} explicitly, we tell Isabelle to coerce @{typ nat}
  automatically when necessary.
*}
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

text {* 
  Similarly, we will want to access the ith element of a list, 
  where @{term i} is an @{typ int}.
*}
fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl "!!" 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

text {*
  The only additional lemma we need about this function 
  is indexing over append:
*}
lemma inth_append [simp]:
  "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i) (auto simp: algebra_simps)

text{* We hide coercion @{const int} applied to @{const length}: *}

abbreviation (output)
  "isize xs == int (length xs)"

notation isize ("size")


subsection "Instructions and Stack Machine"

text_raw{*\snip{instrdef}{0}{1}{% *}
datatype instr = 
  LOADI int | LOAD vname | ADD | STORE vname |
  JMP int | JMPLESS int | JMPGE int
text_raw{*}%endsnip*}

type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
"iexec instr (i,s,stk) = (case instr of
  LOADI n \<Rightarrow> (i+1,s, n#stk) |
  LOAD x \<Rightarrow> (i+1,s, s x # stk) |
  ADD \<Rightarrow> (i+1,s, (hd2 stk + hd stk) # tl2 stk) |
  STORE x \<Rightarrow> (i+1,s(x := hd stk),tl stk) |
  JMP n \<Rightarrow>  (i+1+n,s,stk) |
  JMPLESS n \<Rightarrow> (if hd2 stk < hd stk then i+1+n else i+1,s,tl2 stk) |
  JMPGE n \<Rightarrow> (if hd2 stk >= hd stk then i+1+n else i+1,s,tl2 stk))"

definition
  exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
     ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [59,0,59] 60) 
where
  "P \<turnstile> c \<rightarrow> c' = 
  (\<exists>i s stk. c = (i,s,stk) \<and> c' = iexec(P!!i) (i,s,stk) \<and> 0 \<le> i \<and> i < size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i,s,stk) \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size P
  \<Longrightarrow> P \<turnstile> (i,s,stk) \<rightarrow> c'"
by (simp add: exec1_def)

abbreviation 
  exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("(_/ \<turnstile> (_ \<rightarrow>*/ _))" 50)
where
  "exec P \<equiv> star (exec1 P)"

declare star.step[intro]

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

code_pred exec1 by (metis exec1_def)

values
  "{(i,map t [''x'',''y''],stk) | i t stk.
    [LOAD ''y'', STORE ''x''] \<turnstile>
    (0, <''x'' := 3, ''y'' := 4>, []) \<rightarrow>* (i,t,stk)}"


subsection{* Verification infrastructure *}

text{* Below we need to argue about the execution of code that is embedded in
larger programs. For this purpose we show that execution is preserved by
appending code to the left or right of a program. *}

lemma iexec_shift [simp]: 
  "((n+i',s',stk') = iexec x (n+i,s,stk)) = ((i',s',stk') = iexec x (i,s,stk))"
by(auto split:instr.split)

lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow> c'"
by (auto simp: exec1_def)

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
by (induction rule: star.induct) (fastforce intro: exec1_appendR)+

lemma exec1_appendL:
  fixes i i' :: int 
  shows
  "P \<turnstile> (i,s,stk) \<rightarrow> (i',s',stk') \<Longrightarrow>
   P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow> (size(P')+i',s',stk')"
  unfolding exec1_def
  by (auto simp del: iexec.simps)

lemma exec_appendL:
  fixes i i' :: int 
  shows
 "P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')  \<Longrightarrow>
  P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow>* (size(P')+i',s',stk')"
  by (induction rule: exec_induct) (blast intro!: exec1_appendL)+

text{* Now we specialise the above lemmas to enable automatic proofs of
@{prop "P \<turnstile> c \<rightarrow>* c'"} where @{text P} is a mixture of concrete instructions and
pieces of code that we already know how they execute (by induction), combined
by @{text "@"} and @{text "#"}. Backward jumps are not supported.
The details should be skipped on a first reading.

If we have just executed the first instruction of the program, drop it: *}

lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0,s,stk) \<rightarrow>* (j,t,stk') \<Longrightarrow>
  instr#P \<turnstile> (1,s,stk) \<rightarrow>* (1+j,t,stk')"
by (drule exec_appendL[where P'="[instr]"]) simp

lemma exec_appendL_if[intro]:
  fixes i i' j :: int
  shows
  "size P' <= i
   \<Longrightarrow> P \<turnstile> (i - size P',s,stk) \<rightarrow>* (j,s',stk')
   \<Longrightarrow> i' = size P' + j
   \<Longrightarrow> P' @ P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')"
by (drule exec_appendL[where P'=P']) simp

text{* Split the execution of a compound program up into the excution of its
parts: *}

lemma exec_append_trans[intro]:
  fixes i' i'' j'' :: int
  shows
"P \<turnstile> (0,s,stk) \<rightarrow>* (i',s',stk') \<Longrightarrow>
 size P \<le> i' \<Longrightarrow>
 P' \<turnstile>  (i' - size P,s',stk') \<rightarrow>* (i'',s'',stk'') \<Longrightarrow>
 j'' = size P + i''
 \<Longrightarrow>
 P @ P' \<turnstile> (0,s,stk) \<rightarrow>* (j'',s'',stk'')"
by(metis star_trans[OF exec_appendR exec_appendL_if])


declare Let_def[simp]


subsection "Compilation"

fun acomp :: "aexp \<Rightarrow> instr list" where
"acomp (N n) = [LOADI n]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>* (size(acomp a),s,aval a s#stk)"
by (induction a arbitrary: stk) fastforce+

fun bcomp :: "bexp \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> instr list" where
"bcomp (Bc v) f n = (if v=f then [JMP n] else [])" |
"bcomp (Not b) f n = bcomp b (\<not>f) n" |
"bcomp (And b1 b2) f n =
 (let cb2 = bcomp b2 f n;
        m = (if f then size cb2 else (size cb2::int)+n);
      cb1 = bcomp b1 False m
  in cb1 @ cb2)" |
"bcomp (Less a1 a2) f n =
 acomp a1 @ acomp a2 @ (if f then [JMPLESS n] else [JMPGE n])"

value
  "bcomp (And (Less (V ''x'') (V ''y'')) (Not(Less (V ''u'') (V ''v''))))
     False 3"

lemma bcomp_correct[intro]:
  fixes n :: int
  shows
  "0 \<le> n \<Longrightarrow>
  bcomp b f n \<turnstile>
 (0,s,stk)  \<rightarrow>*  (size(bcomp b f n) + (if f = bval b s then n else 0),s,stk)"
proof(induction b arbitrary: f n)
  case Not
  from Not(1)[where f="~f"] Not(2) show ?case by fastforce
next
  case (And b1 b2)
  from And(1)[of "if f then size(bcomp b2 f n) else size(bcomp b2 f n) + n" 
                 "False"] 
       And(2)[of n f] And(3) 
  show ?case by fastforce
qed fastforce+

fun ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^sub>1;;c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp c\<^sub>1; cc\<^sub>2 = ccomp c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp (WHILE b DO c) =
 (let cc = ccomp c; cb = bcomp b False (size cc + 1)
  in cb @ cc @ [JMP (-(size cb + size cc + 1))])" |
(* begin mod *)
"ccomp (REPEAT c UNTIL b) = 
     (let cc = ccomp c; cb = bcomp b True 1
      in cc @ cb @ [JMP (-(size cc + size cb + 1))])"
(* end mod *)

value "ccomp (REPEAT ''u'' ::= Plus (V ''u'') (N 1) UNTIL Less (N 0) (V ''u''))"


subsection "Preservation of semantics"

lemma ccomp_bigstep:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)"
proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1"  let ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc1,s2,stk)"
    using Seq.IH(1) by fastforce
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1,s2,stk) \<rightarrow>* (size(?cc1 @ ?cc2),s3,stk)"
    using Seq.IH(2) by fastforce
  ultimately show ?case by simp (blast intro: star_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  let ?cw = "ccomp(WHILE b DO c)"
  have "?cw \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cb,s1,stk)"
    using `bval b s1` by fastforce
  moreover
  have "?cw \<turnstile> (size ?cb,s1,stk) \<rightarrow>* (size ?cb + size ?cc,s2,stk)"
    using WhileTrue.IH(1) by fastforce
  moreover
  have "?cw \<turnstile> (size ?cb + size ?cc,s2,stk) \<rightarrow>* (0,s2,stk)"
    by fastforce
  moreover
  have "?cw \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cw,s3,stk)" by(rule WhileTrue.IH(2))
  ultimately show ?case by(blast intro: star_trans)
(* begin mod *)
next
  case (RepeatFalse c s1 s2 b s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b True 1"
  let ?cr = "ccomp(REPEAT c UNTIL b)"
  have "?cr \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc,s2,stk)"
     using RepeatFalse.IH(1) by fastforce
  moreover
  have "?cr \<turnstile> (size ?cc,s2,stk) \<rightarrow>* (size ?cc+size ?cb,s2,stk)"
     using `\<not> bval b s2` by fastforce
  moreover
  have "?cr \<turnstile> (size ?cc+size ?cb,s2,stk) \<rightarrow>* (0,s2,stk)"
    by fastforce
  moreover
  have "?cr \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cr,s3,stk)" by (rule RepeatFalse.IH(2))
  ultimately show ?case by(blast intro: star_trans)
(* end mod *)
qed fastforce+

end
