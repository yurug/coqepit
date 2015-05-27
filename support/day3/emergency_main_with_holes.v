(* Loading libraries and the ssreflect plugin. *)
(* In particular, we are importing formalized material about
   elementary arithmetic *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path div.
Require Import fintype tuple finfun bigop prime finset binomial.

(** BEGIN HIDE **)

Lemma double_sub n : n.*2 - n = n.
Proof. by rewrite -addnn addKn. Qed.

Lemma iota_Sr k : iota 1 k.+1 = iota 1 k ++ [:: k.+1].
Proof. by rewrite -[in LHS](addn1 k) iota_add add1n. Qed.

(** END HIDE **)

(* BEGIN HIDE *)
Section CoprimeProd.

Variables (I : eqType).

Lemma coprime_prodr (r : seq I) (P : pred I) (F : I -> nat) n :
  (forall x, x \in r -> P x -> coprime n (F x)) ->
  coprime n (\prod_(i <- r | P i) F i).
Proof.
elim: r => [|x r ihr] hc; first by rewrite big_nil coprimen1.
have {ihr} ihr : coprime n (\prod_(j <- r | P j) F j).
  by apply: ihr => y ry Py; rewrite hc // in_cons ry orbT.
by rewrite big_cons; case: ifP => Px //; rewrite coprime_mulr hc // in_cons eqxx.
Qed.

Lemma coprime_prodl (r : seq I) (P : pred I) (F : I -> nat) n :
  (forall x, x \in r -> P x -> coprime (F x) n) ->
  coprime (\prod_(i <- r | P i) F i) n.
Proof.
move=> h; rewrite coprime_sym; apply: coprime_prodr=> i; rewrite coprime_sym.
exact: h.
Qed.

End CoprimeProd.

(* END HIDE *)


(*** We first prove elementary lemmas about doubling and halving. ***)

(* (n.*2) denotes (double n), (n./2) denotes (half n), the
   integral half of a natutal number. *)
(* The following command list the lemmas that feature double
   in their conclusion. *)
Search (_.*2).

(* The following command list the lemmas that feature double
   in their statement (but in this case it makes no diff...) *)
Search _ (_.*2).

(* The About command should be used to inspect the statement of
   a theorem. It provides the useful informations about, not only
   the statement, but also for instance the status of the
   (implicit) arguments. *)

About muln2.
About leq_pmul2r.

(* Note that Check also work in this case, but gives much less
  information. *)

(* Prove the following lemma using muln2 and leq_pmul2r. *)
Lemma leq_ndouble n : n <= n.*2.
Proof. admit . Qed.

(* The command Hint Resolve <my_lemma> adds <my_lemma> to the
   set of things tried by the easy/trivial/done tactics. This
   is very useful be can be dangerous! An unconditional lemma
   like leq_ndouble is a good candidate though. *)
Hint Resolve leq_ndouble.

(* Prove the following lemma, using odd_double_half. *)
Lemma leq_double_half n : (n./2).*2 <= n.
Proof.
admit.
Qed.

Hint Resolve leq_double_half.

(* Observe the result of the following: *)
About leq_trans.
(* Pay attention to the order and status of Implicit Arguments. *)

(* Prove the following lemma using leq_trans and leq_ndouble. *)
Lemma leq_half n : n./2 <= n.
Proof.
admit.
Qed.

Hint Resolve leq_half.

(* The ssrnat library also implement an uphalf function. *)
(* Printing its body is not so informative: *)

Print uphalf.
(* Let us inspect its theory: *)
Search _ uphalf.

(* Let us comment this statement:
  uphalf_half  forall n : nat, uphalf n = odd n + n./2 *)
(* What is odd? *)
About odd.
Search _ odd.
(* It is a boolean predicate testing whether a natural numbers
is odd... But how can a boolean be added to a natural number?
Because the boolean is embedded in natural numbers, via a coercion. *)
Set Printing Coercions.

About uphalf_half.
Print nat_of_bool.

Unset Printing Coercions.
About uphalf_half.

(* Now we know that uphalf_half is n./2 if n is even and 1 + n./2 if
   n is odd. *)

(* Before starting the next exercise, inspect the statement of
    leq_add2l. What does this equality stand for ? *)

(* Using the lemmas uphalf_half, odd_double_half, leq_add2l and
   leq_add2l, le_double prove the following lemma: *)

Lemma leq_uphalfn n : uphalf n <= n.
Proof.
admit.
Qed.

(* Again, we add this as a hint. *)
Hint Resolve leq_uphalfn.

(* Binomial coefficients are denotes 'C(n, m).
   The factorial of n is denoted n`!.
Find in the  library a lemma relating 'C(n, m) and n`!, m`! *)

(*** Now Lemma0 of our proof. Complete the proof it using
subSn, double_sub, doubleS, mul2n, mulnA
mulnCA expnS.
 **)
Lemma lebinpow2 n : 'C(n.*2, n) <= 2 ^ (n.*2).
Proof.
elim: n => [|n ihn] //=. (* induction on the natural number *)
 (* we pre-multiply by the denominator *)
rewrite -(@leq_pmul2l n.+1) //.
have -> : n.+1 * 'C((n.+1).*2, n.+1) = 2 * (n.*2).+1 * 'C(n.*2, n).
  rewrite -[(n.+1).*2]/(((n.+1).*2).-1.+1) -[LHS]mul_Sm_binm.
  rewrite -[(n.+1).*2.-1]/(n.*2.+1) -[in LHS]bin_sub ?leqW //.
  admit.
have h : 2 * n.*2.+1 * 'C(n.*2, n) <= 2 * n.*2.+1 * 2 ^ n.*2.
  admit.
apply: (leq_trans h); rewrite -[2 * _ * _]mulnA [X in X <= _]mulnCA.
rewrite -expnS.
have -> : n.+1 * 2 ^ (n.+1).*2 = n.+1 * 2 * 2 ^ (n.*2.+1).
  admit.
by rewrite leq_pmul2r ?expn_gt0 // muln2 ltn_double.
Qed.

(*** Now some less elementary lemmas about primes and divisibility. ***)

(* The libraries we loaded define the boolean predicates:
   - prime *)
About prime.
Search _ prime.
(* and (_ %| _), such that (n %| m) means 'n divides m': *)
Search _ (_ %| _).

(* They also define (factorial n), denoted `!n *)
Search _ (_ `!).

(* We first prove that a prime number that divides n! must be
   smaller than n. *)

(* Remember that:
   - (n == m) denotes (n == m) = true, the boolean equality
   test on natural numbers.
   - move/eqP: h => h := transforms a hypothesis h : n == m in the context
    into h : n = m
   - apply/eqP := transforms a goal n == m into n = m.
   - case/orP: h => h := when h : p || q, a boolean disjunction, performs
     a case analysis, in one branch we have h : p and in the other
     branch, we have h : q.
    - case/andP: h => h1 h2 := when h : p && q, introduces two
    hypotheses h1 : p and h2 : q.
    - rewrite (negPf h := when h : ~~ p, rewrites occurrences of p
      to false in the goal. *)



(* Proove the following lemma, by recurrence on n.
   Use Search commands, like *)
Search _ (0 `!).

(* Remember that having h  : false = true in the context closes the
   (sub)proof. *)
Lemma prime_dvd_fact_le p n : prime p -> p %| n`! -> p <= n.
Proof.
admit.
Qed.

(* Now a converse, which does not require p to be prime, only
   to be strictly positive. *)
(* Again, prove this lemma, by recurrence on n. *)
Lemma le_dvd_fact p n :  0 < p -> p <= n -> p %| n`!.
Proof.
admit.
Qed.

(* When statements are formalized as booleans, they are amenable
   to classical reasoning like contraposition. This is formalized
   by the 'contra*' lemmas, like contraL: *)
About contraL.

(* Like on paper, when proofs get slightly longer, it is a good
   practice to:
  - use forward reasoning tactics (assert, have, suff)
  - mark the end of a script paragraph by a 'closing tactic', one
    which fails if it does not close the current goal. *)
(* Complete the following proof: *)
Lemma lemma1 p n : n.+1 <= p <= n.*2 -> prime p -> p %| 'C(n.*2, n).
Proof.
case/andP=> ltnp lep2n pn.
have h : 'C(n.*2, n) * (n`! ^ 2) = (n.*2)`!.
  have e : n`! ^ 2 = n`! * (n.*2 - n)`!.
    by rewrite -addnn addnK. (**)
  admit.
have hc : ~~ (p %| (n`! ^ 2)).
  admit.
have : p %| (n.*2)`! by admit.
admit.
Qed.

(* How to prove this? *)

Corollary corollary1 n :
  \prod_(n.+1 <= p < (n.*2).+1 | prime p) p <= 'C(n.*2, n).
Proof.
apply: dvdn_leq; first by rewrite bin_gt0.
rewrite big_nat_cond.
(* have : uniq (index_iota n.+1 (n.*2).+1) by rewrite iota_uniq. *)
(* move: (index_iota n.+1 (n.*2).+1) => l. *)
(* elim: l => /= [|m r ihr]; first by rewrite big_nil. *)
admit.
Qed.

(* Now we load some libraries about real numbers. *)
Require Import Reals Coquelicot.Rcomplements.

(* We open a scope notation for the interpretation of
  operations on real numbers. *)
Open Scope R_scope.

(* Observe that the default interpretation for notation has
  changed: *)
Check 0.
Check (9 + 0).

(* These operations do not evaluate: they are a symbolic,
   axiomatic signature: *)
Print Rplus.

Compute (0 + 1).

(* Beside the usual arithmetic notations, we also have an inverse
(total) function on real numbers, called Rinv and denoted / x : *)

Check (/ 1).

Check (/ 0).
(* It is total, but its theory require its arguments to be non zero *)


(* Similarily, comparison predicates are in Prop, not bool:*)
Check (0 < 1)%R.

(* We can recover the nat scope using an explicit label: *)
Check (0 < 1)%nat.

(* And we load some auxiliary material. *)


(** BEGIN HIDE **)
(*** Boilerplate code, to be able to use bigop style iterated
     sums and products on natural numbers. ***)

Hint Resolve Rle_refl.
Hint Resolve Rlt_0_1.
Hint Resolve Rle_0_1.
Hint Resolve Rlt_0_2.
Hint Resolve R1_neq_R0.

Lemma RplusA : associative Rplus.
Proof. now intros x y z; rewrite Rplus_assoc. Qed.

Lemma Rplus0r : left_id 0 Rplus.
Proof. exact Rplus_0_l. Qed.

Lemma Rplusr0 : right_id 0 Rplus.
Proof. exact Rplus_0_r. Qed.

Lemma RplusC : commutative Rplus.
Proof. exact Rplus_comm. Qed.

Canonical Rplus_monoid := Monoid.Law RplusA Rplus0r Rplusr0.
Canonical Rplus_comoid := Monoid.ComLaw RplusC.

Lemma RmultA : associative Rmult.
Proof. now intros x y z; rewrite Rmult_assoc. Qed.

Lemma Rmult1r : left_id 1 Rmult.

Proof. exact Rmult_1_l. Qed.

Lemma Rmultr1 : right_id 1 Rmult.
Proof. exact Rmult_1_r. Qed.

Lemma RmultC : commutative Rmult.

Proof. exact Rmult_comm. Qed.

Lemma Rmult0r : left_zero 0 Rmult.
Proof. exact Rmult_0_l. Qed.

Lemma Rmultr0 : right_zero 0 Rmult.
Proof. exact Rmult_0_r. Qed.

Lemma RmultDl : left_distributive Rmult Rplus.
Proof. exact Rmult_plus_distr_r. Qed.

Lemma RmultDr : right_distributive Rmult Rplus.
Proof. exact Rmult_plus_distr_l. Qed.

Canonical Rmult_monoid := Monoid.Law RmultA Rmult1r Rmultr1.
Canonical Rmult_comoid := Monoid.ComLaw RmultC.
Canonical Rmult_muloid := Monoid.MulLaw Rmult0r Rmultr0.
Canonical Rplus_addoid := Monoid.AddLaw RmultDl RmultDr.

(* Some convention LaTeX style notations for the common
  iterated operations on real numbers. *)
Local Notation "+%R" := Rplus (at level 0, only parsing).
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P%B) F%R) : R_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F%R) : R_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P%B) F%R) : R_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F%R) : R_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P%B) F%R) : R_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : R_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P%B) F%R) (only parsing) : R_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : R_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P%B) F%R) : R_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : R_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%R/0%R]_(i in A | P%B) F%R) : R_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%R/0%R]_(i in A) F%R) : R_scope.

Local Notation "*%R" := Rmult (at level 0, only parsing).
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%R/1%R]_(i <- r | P%B) F%R) : R_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%R/1%R]_(i <- r) F%R) : R_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n | P%B) F%R) : R_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%R/1%R]_(m <= i < n) F%R) : R_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%R/1%R]_(i | P%B) F%R) : R_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : R_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%R/1%R]_(i : t | P%B) F%R) (only parsing) : R_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%R/1%R]_(i : t) F%R) (only parsing) : R_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%R/1%R]_(i < n | P%B) F%R) : R_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%R/1%R]_(i < n) F%R) : R_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%R/1%R]_(i in A | P%B) F%R) : R_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%R/1%R]_(i in A) F%R) : R_scope.


(* A couple of few missing things in the libraries we loaded... *)

Lemma INRpow n m : INR (n ^ m) = INR n ^ m.
Proof.
elim: m => [|m ihm]; first by rewrite expn0 pow_O.
by rewrite expnS mult_INR ihm.
Qed.

Lemma Rdiv_ge_1 r1 r2 : 0 < r1 -> (r1 <= r2 <-> 1 <= r2 / r1).
Proof.
intros H.
pattern r1 at 1.
rewrite <- (Rmult_1_l r1).
split ; apply Rle_div_r ; apply H.
Qed.

(*** A version of  INR that allows for easier proofs of 2 < 8, making
    (INR n) and ('n' : R) convertible for every numeral 'n'. ***)

(* Three base cases are needed in order to avoid spurious
    multiplications by one at the tail. *)

Fixpoint pos2R (p : positive) : R :=
  match p with
    |xH => 1
    |xO xH => 2
    |xI xH => 3
    |xO p => 2 * (pos2R p)
    |xI p => 1 + 2 * (pos2R p)
  end.

Arguments pos2R : simpl never.
Arguments IZR : simpl never.

Lemma pos2RE p : pos2R p = IZR (Zpos p).
Proof.
elim: p=> [p ihp | p ihp |] //.
- case: p ihp => [p | p |] ihp.
  + rewrite -[LHS]/(1 + 2 * pos2R p~1) ihp -[RHS]/(INR (Pos.to_nat p~1~1)).
    by rewrite Pos2Nat.inj_xI S_INR mult_INR Rplus_comm.
  + rewrite -[LHS]/(1 + 2 * pos2R p~0) ihp -[RHS]/(INR (Pos.to_nat p~0~1)).
    by rewrite Pos2Nat.inj_xI S_INR mult_INR Rplus_comm.
  + by rewrite -[RHS]/(INR (Pos.to_nat 3)) Pos2Nat.inj_xI S_INR Rplus_comm.
- case: p ihp => [p | p |] ihp.
  + rewrite -[LHS]/(2 * pos2R p~1) ihp -[RHS]/(INR (Pos.to_nat p~1~0)).
    by rewrite Pos2Nat.inj_xO mult_INR.
  + rewrite -[LHS]/(2 * pos2R p~0) ihp -[RHS]/(INR (Pos.to_nat p~0~0)).
    by rewrite Pos2Nat.inj_xO mult_INR.
  + by rewrite -[RHS]/(INR (Pos.to_nat 2)) Pos2Nat.inj_xO.
Qed.

Definition Z2R (z : Z) :=
  match z with
    |Z0 => R0
    |Zpos p => pos2R p
    |Zneg p => - pos2R p
  end.

Lemma Z2RE z : Z2R z = IZR z.
Proof. by case: z => // p /=; rewrite pos2RE. Qed.

Definition nat2R (n : nat) := Z2R (Z_of_nat n).

Lemma nat2RE n : nat2R n = INR n.
Proof. by rewrite INR_IZR_INZ -Z2RE. Qed.


Lemma S_nat2R n : nat2R n.+1 = INR n + 1.
Proof. rewrite nat2RE; exact: S_INR. Qed.

Lemma lt_0_nat2R n : (0 < n)%nat -> 0 < nat2R n.
Proof.
move/ltP=> lt0n; rewrite nat2RE. exact: lt_0_INR.
Qed.

Lemma le_0_nat2R n : (0 <= n)%nat -> 0 <= nat2R n.
Proof.
move/leP=> lt0n; rewrite nat2RE -[0]/(INR 0); exact: le_INR.
Qed.

Lemma le_nat2R n m : (n <= m)%nat -> nat2R n <= nat2R m.
Proof. move/leP=>h; rewrite !nat2RE; exact: le_INR. Qed.

Lemma lt_nat2R n m : (n < m)%nat -> nat2R n < nat2R m.
Proof. move/ltP=>h; rewrite !nat2RE; exact: lt_INR. Qed.

Lemma nat2R_le n m : nat2R n <= nat2R m -> (n <= m)%nat.
Proof. rewrite !nat2RE => lenm; apply/leP; exact: INR_le. Qed.

Lemma nat2R_lt n m : nat2R n < nat2R m -> (n < m)%nat.
Proof. rewrite !nat2RE => lenm; apply/leP; exact: INR_lt. Qed.

Lemma mult_nat2R n m : nat2R (n * m)%nat = nat2R n * nat2R m.
Proof. by rewrite !nat2RE mult_INR. Qed.

Lemma plus_nat2R n m : nat2R (n + m)%nat = nat2R n + nat2R m.
Proof. by rewrite !nat2RE plus_INR. Qed.

Lemma nat2Rpow n m : nat2R (n ^ m) = nat2R n ^ m.
Proof. by rewrite !nat2RE INRpow. Qed.

Lemma nat2R_inj : injective nat2R.
Proof. by move=> i j; rewrite !nat2RE; apply: INR_eq. Qed.

Lemma not_0_nat2R n : n != 0%nat -> nat2R n <> 0.
Proof. move/eqP; rewrite nat2RE. exact: not_0_INR. Qed.

Lemma Rinv_nat2R_gt0 n : (n > 0)%nat -> 0 < / nat2R n.
Proof.
by move=> lt0n; apply: Rinv_0_lt_compat; apply: lt_0_nat2R.
Qed.

Lemma Rinv_nat2R_ge0 n : (n > 0)%nat -> 0 <= / nat2R n.
Proof.
by move=> lt0n; apply: Rlt_le; apply: Rinv_nat2R_gt0.
Qed.

(*** Definition of log, the logarithm in basis 2, and elementary properties
   thereof. We prove here only what is needed in the proof, but basically
   we should be able to prove everything that is available on ln, mutatis
   mutandis. ***)

Definition log (x : R) := ln x / ln 2.

Arguments log : simpl never.

Lemma Rlt_0_ln2 : 0 < ln 2.
Proof. now rewrite <- ln_1; apply ln_increasing; prove_sup. Qed.

Hint Resolve Rlt_0_ln2.

(* For the purpose of Hint Resolve... *)
Lemma Rgt_ln2_0 : ln 2 > 0.
Proof. exact Rlt_0_ln2. Qed.

Hint Resolve Rgt_ln2_0.

Lemma ln2_neq_0 : ln 2 <> 0.
Proof. apply Rgt_not_eq; exact Rlt_0_ln2. Qed.

Hint Resolve ln2_neq_0.

Lemma ln_gt_0 x : x > 1 -> ln x > 0.
Proof. intros lt0x; rewrite -ln_1; exact: ln_increasing. Qed.

Lemma Rmult_log_ln2 x : log x * ln 2 = ln x.
Proof.
now unfold log, Rdiv; rewrite Rmult_assoc Rinv_l ?Rmult_1_r.
Qed.

Lemma log_pow (n : nat) : log (2 ^ n) = nat2R n.
Proof.
unfold log. rewrite ln_pow;last by prove_sup.
by rewrite /Rdiv Rmult_assoc Rinv_r // Rmult_1_r nat2RE.
Qed.

Lemma log_le  (x y : R) : 0 < x -> x <= y -> log x <= log y.
Proof.
intros lt0x lexy. apply Rle_div_l; trivial. rewrite Rmult_log_ln2.
now apply ln_le.
Qed.

Lemma log_div (x y : R) : 0 < x -> 0 < y -> log (x / y) = log x - log y.
Proof.
intros lt0x lt0y. unfold log, Rdiv.
now rewrite -Rmult_minus_distr_r ln_div.
Qed.

Lemma log_increasing (x y : R) : 0 < x -> x < y -> log x < log y.
Proof.
intros lt0x lt0y.  apply Rlt_div_l; trivial. rewrite Rmult_log_ln2.
now apply ln_increasing.
Qed.

Lemma log_increasingW (x y : R) : 0 < x -> x <= y -> log x <= log y.
Proof.
move=> lt_0_x /Rle_lt_or_eq_dec [|->] //.
by move/(log_increasing _ _ lt_0_x)/Rlt_le.
Qed.

Lemma log_1 : log 1 = 0.
Proof. now unfold log; rewrite ln_1; unfold Rdiv; rewrite Rmult_0_l. Qed.

Lemma log_2 : log 2 = 1.
Proof. by unfold log; apply Rinv_r. Qed.

Lemma log_gt_0 x : x > 1 -> log x > 0.
Proof. intros lt0x; rewrite -log_1; exact: log_increasing. Qed.

Lemma log_ge_0 x : 1 <= x -> 0 <= log x.
Proof. by rewrite -log_1; apply: log_increasingW. Qed.

Lemma log_gt_1 x : x > 2 -> log x > 1.
Proof.
rewrite -[X in log x > X]log_2; apply: log_increasing.
by apply: (lt_0_INR 2%nat); apply/ltP.
Qed.

Lemma log_ge_1 x : 2 <= x -> 1 <= log x.
Proof.
rewrite -[X in X <= log x]log_2; apply: log_increasingW.
by apply: (lt_0_INR 2%nat); apply/ltP.
Qed.

Lemma log_lt_inv  (x y : R) : 0 < x -> 0 < y -> log x < log y -> x < y.
Proof.
move=> lt0x lt0y.
have /Rmult_lt_reg_r h: 0 < / ln 2 by apply: Rinv_0_lt_compat.
by move/h; move/ln_lt_inv; apply.
Qed.


Lemma log_inv (x y : R) : 0 < x -> 0 < y -> log x = log y -> x = y.
Proof.
move=> lt_0_x lt_0_y elog.
have /Rmult_eq_reg_r h: / ln 2 <> 0 by apply: Rinv_neq_0_compat.
move/h: elog; exact: ln_inv.
Qed.

Lemma log_le_inv  (x y : R) : 0 < x -> 0 < y -> log x <= log y -> x <= y.
Proof.
move=> lt0x lt0y; case/Rle_lt_or_eq_dec; last by move/(log_inv _ _ lt0x lt0y)->.
by move/(log_lt_inv _ _ lt0x lt0y); apply: Rlt_le.
Qed.

Lemma log_mult (x y : R) : 0 < x -> 0 < y -> log (x * y) = log x + log y.
Proof. by move=> lt0x lt0y; rewrite /log -Rmult_plus_distr_r -ln_mult. Qed.

Lemma log_Rinv (x : R) : 0 < x -> log (/ x) = - log x.
Proof.
by move=> lt0x; rewrite /log ln_Rinv // -Ropp_mult_distr_l_reverse.
Qed.


(*** Some auxiliary lemmas about iterated products and sume of reals.
     we cannot use the MC theory of ordered structures because R cannot
     be equipped as such with this structure (we miss the choice axiom.
     We just prove what is needed below... to be hidden or to be used as
     exercises in order to use the bigop library. ***)

Arguments INR : simpl never.

Lemma prodR_gt0 (I : eqType) r (P : pred I) (E : I -> R) :
  (forall i, i \in r -> P i -> 0 < E i) -> 0 < \prod_(i <- r | P i) E i.
Proof.
elim: r => [|x r ihr] lt0E; first by rewrite big_nil; exact: Rlt_0_1.
have {ihr} ihr : 0 < \prod_(i <- r | P i) E i.
  by apply: ihr=> i ri; apply: lt0E; rewrite in_cons ri orbT.
rewrite big_cons; case: ifP=> // Px; apply: Rmult_lt_0_compat => //.
by apply: lt0E; rewrite // in_cons eqxx.
Qed.

Lemma leR_sum (I : eqType) (r : seq I) (P : pred I) (F G : I -> R) :
    (forall i, i \in r -> P i -> F i <= G i) ->
  \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
Proof.
elim: r => [|x r ihr] hle; first by rewrite !big_nil.
have {ihr} ihr : \sum_(i <- r | P i) F i <= \sum_(i <- r | P i) G i.
  by apply: ihr => i ri; apply: hle; rewrite in_cons ri orbT.
rewrite !big_cons; case: ifP=> Px //; apply: Rplus_le_compat => //.
by apply: hle; rewrite // in_cons eqxx.
Qed.

Lemma sumR_ge0 (I : eqType) (r : seq I) (P : pred I) (G : I -> R) :
    (forall i, i \in r -> P i -> 0 <= G i) ->
    0 <= \sum_(i <- r | P i) G i.
Proof. by move/leR_sum; rewrite big1_eq. Qed.

Lemma sumRln (I : eqType) (r : seq I) P (F : I -> R) :
  (forall i, i \in r -> F i > 0) ->
  \sum_(i <- r | P i) ln (F i) = ln (\prod_(i <- r | P i) F i).
Proof.
elim: r=> [|x r ihr] hpos; first by rewrite !big_nil ln_1.
have {ihr} ihr : \sum_(i <- r | P i) ln (F i) = ln (\prod_(i <- r | P i) F i).
  by rewrite ihr // => i ri; apply: hpos; rewrite in_cons ri orbT.
rewrite !big_cons; case: ifP=> Px //.
rewrite ln_mult ?ihr //; first by apply: hpos; rewrite in_cons eqxx.
by apply: prodR_gt0=> i ri _; apply: hpos; rewrite in_cons ri orbT.
Qed.

Lemma sumRlog (I : eqType) (r : seq I) P (F : I -> R) :
  (forall i, i \in r -> F i > 0) ->
  \sum_(i <- r | P i) log (F i) = log (\prod_(i <- r | P i) F i).
Proof. by move=> hp; rewrite [RHS]/log -sumRln // [RHS]big_distrl. Qed.

(*** Second part of the proof, i.e. lemma 2:
     we majorize sums of logs of consecutive primes
     between n.+1 and 2n ***)

Lemma le_sum_log_ps n :
  \sum_(n.+1 <= p < (n.*2).+1 | prime p) log (nat2R p) <= 2 * nat2R n.
Proof.
case: (posnP n)=> [-> | lt0n].
  by rewrite double0 big_nil Rmult_0_r.
have /sumRlog -> i : i \in index_iota n.+1 (n.*2).+1 -> nat2R i > 0.
  rewrite mem_iota; case/andP=> ltin _; apply: lt_0_nat2R; exact: ltn_trans ltin.
have -> : 2 * nat2R n = log (nat2R (2 ^ (n.*2))).
  by rewrite nat2Rpow log_pow -mul2n mult_nat2R.
rewrite -(big_morph _ mult_nat2R (refl_equal (nat2R 1%N))) => /=.
apply: log_increasingW.
  by apply: lt_0_nat2R; apply: prodn_cond_gt0=> i /prime_gt0.
apply: le_nat2R; apply: leq_trans (corollary1 n) _.
exact: lebinpow2.
Qed.

(*** Third part of the proof, i.e. lemma 3:
     we majorize sums of logs of consecutive inverses primes
     between n.+1 and 2n, with a factor of log n. ***)

Lemma le_sum_inv n : (1 < n)%nat ->
  \sum_(n.+1 <= p < (n.*2).+1 | prime p) / (nat2R p) <= 2 / log (nat2R n).
Proof.
move=> lt1n. set dom := index_iota n.+1 (n.*2).+1.
have domP i : i \in dom -> ((n.+1 <= i) && (i <= n.*2))%nat.
  by rewrite /dom mem_iota subnKC // ltnS.
have nat2Rn_gt0 : nat2R n > 0.
  by apply: lt_0_nat2R; apply: ltn_trans lt1n.
have nat2Rn_neq0 : nat2R n <> 0 by apply: Rgt_not_eq.
have logn_gt0 : log (nat2R n) > 0.
  by apply: log_gt_0; apply: (lt_nat2R 1).
have logn_neq0 : log (nat2R n) <> 0 by apply: Rgt_not_eq.
have /leR_sum t1 : forall i,  i \in dom -> prime i ->
                  / (nat2R i) <= log (nat2R i) * / ((nat2R n) * (log (nat2R n))).
  move=> i /domP /andP [ltni ltiS2n] pi.
  have nat2Ri_neq0 : nat2R i > 0 by apply: lt_0_nat2R; apply: prime_gt0.
  rewrite [X in _ <= _ * X]Rinv_mult_distr // [/ nat2R n * _]Rmult_comm.
  rewrite -Rmult_assoc -[X in X <= _]Rmult_1_l; apply: Rmult_le_compat => //.
  - by apply: Rlt_le; apply: Rinv_0_lt_compat.
  - apply -> Rdiv_ge_1 => //; apply: log_increasingW => //; apply: Rlt_le.
    by apply: lt_nat2R.
  - apply: Rle_Rinv => //; apply: Rlt_le; exact: lt_nat2R.
apply: Rle_trans t1 _; rewrite -big_distrl /=; apply <- Rle_div_l; last first.
  by apply: Rmult_gt_0_compat.
set RHS := (X in _ <= X); suff -> : RHS = 2 * nat2R n by apply: le_sum_log_ps.
rewrite {}/RHS [nat2R n * _]Rmult_comm Rmult_assoc; congr (2 * _).
by rewrite -Rmult_assoc Rinv_l // Rmult_1_l.
Qed.

(* END HIDE *)

(*** Third part: an elementary proof that H n, the term of the harmonic
     series, is a big O of log n. ***)

(* We start be proving that the sum of the inverse of consecutive even
   numbers up to n is equal to the sum of the inverses of the consecutive
   numbers up to n, divided by 2. *)
Lemma sum_even_Rinv n :
  \sum_(1 <= i < n.+1 | ~~ odd i) / nat2R i =
  / nat2R 2 * \sum_(1 <= i < n./2.+1) / nat2R i.
Proof.
set R := RHS.
have {R} -> : R = \sum_(1 <= i < n./2.+1) /nat2R i.*2.
  rewrite {}/R big_distrr /=.
  rewrite !big_add1.
  apply: eq_bigr => i _.
  rewrite -Rinv_mult_distr; [|by apply: not_0_nat2R..].
  by rewrite -mult_nat2R mul2n.
rewrite -[in LHS]big_filter.
(* Observe the conflict between two libraries we loaded: *)
About double.
About ssrnat.double.
suff -> : [seq i <- index_iota 1 n.+1 | ~~ odd i] =
          map ssrnat.double (index_iota 1 n./2.+1) by rewrite big_map.
rewrite /index_iota !subn1 /=.
(* Finish the proof by induction on n *)
admit.
Qed.

(* And the final inequality on the harmonic sum: *)
Lemma Rle_harmonic_log n : (0 < n)%nat ->
    \sum_(1 <= i < n.+1) / nat2R i <= 1 + log (nat2R n).
Proof.
(* This idiom performs a recurrence with a strong hypothesis. *)
elim: n {-2}n (leqnn n)=> [|n ihn] m.
  by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt; case/orP; last exact: ihn.
move/eqP=> -> {m} _.
rewrite (bigID odd) /=.
have -> : \sum_(1 <= i < n.+2 | odd i) / nat2R i =
          1 + \sum_(1 <= i < n.+1 | ~~ odd i) / nat2R i.+1.
  have arg1 : (1 <= 2)%nat. by [].
  rewrite [LHS](big_cat_nat _ _ _ arg1 _) //=.
  rewrite big_mkcond [X in X + _ = _]big_nat1 /= Rinv_1.
  rewrite big_add1. done.
rewrite Rplus_assoc.
apply: Rplus_le_compat; trivial.
have majS k : \sum_(1 <= i < k | ~~ odd i) / nat2R i.+1 <=
              \sum_(1 <= i < k | ~~ odd i) / nat2R i.
  apply: leR_sum => i ii oi.
  apply: Rinv_le_contravar; last by apply: le_nat2R.
  (* This should be a lemma in our case... *)
  by apply: lt_0_nat2R; move: ii; rewrite mem_index_iota; case/andP.
set lhs := (X in X <= _).
have t1 : lhs <= 2 * \sum_(1 <= i < n.+2 | ~~ odd i) / nat2R i.
  rewrite RIneq.double /lhs.
  apply: Rplus_le_compat => //.
  apply: Rle_trans (majS _) _ => {majS}.
  have arg1 : (1 <= n.+1)%nat. by [].
  rewrite [X in _ <= X](big_cat_nat _ _ _ arg1 _) //=.
  rewrite -[X in X <= _]Rplus_0_r. apply: Rplus_le_compat=> //.
  rewrite big_mkcond /= big_nat1 //.
  by case: ifP => // _; apply: Rinv_nat2R_ge0.
apply: Rle_trans t1 _ => {lhs majS}.
rewrite Rmult_comm.
rewrite Rle_div_r; last by apply: (lt_0_nat2R 2).
rewrite /Rdiv Rmult_comm.
rewrite sum_even_Rinv.
apply: Rmult_le_compat=> //; first by apply: Rinv_nat2R_ge0.
  apply: sumR_ge0=> i hi _.
  apply: Rinv_nat2R_ge0.
  by move: hi; rewrite mem_iota; case/andP.
case: n ihn => // [|n ihn] /=.
  by rewrite big_nil ?log_1 //.
apply: Rle_trans (ihn _ _ _) _; rewrite ?ltnS //.
have -> : 1 + log (nat2R n./2.+1) = log (nat2R (n./2.+1).*2).
  rewrite -log_2 -log_mult //; last exact: lt_0_nat2R.
  rewrite -mul2n mult_nat2R log_mult //; exact: lt_0_nat2R.
apply: log_increasingW; first exact: lt_0_nat2R.
by apply: le_nat2R; rewrite doubleS !ltnS.
Qed.


(*** BEGIN HIDE **)

(* And now the final result: warning, the proof script still needs a
   serious clean up... *)
Section ForArthur.

(* We instanciate manually the various bigO constants and bounds. *)
Let M := nat2R 6.
Let M' := nat2R 2.
Let N2 := 2%nat.
Let N1 := 5%nat.

Lemma harm: forall j : nat, (N2 <= j)%nat ->
  (\sum_(1 <= i < j.+1) / nat2R i) <= M' * ((log \o nat2R) j).
Proof.
move=> j le2j.
apply: Rle_trans (Rle_harmonic_log j _) _; first by apply: leq_trans le2j.
rewrite RIneq.double; apply: Rplus_le_compat => //=; rewrite -log_2 -[2]/(nat2R 2).
apply: log_increasingW; first by apply: lt_0_nat2R.
by apply: le_nat2R.
Qed.

Let le2N : (2 <= N1)%nat.
Proof. by []. Qed.

Let le3M'M: nat2R 3 * M' <= M.
Proof. by rewrite /M' -mult_nat2R. Qed.

Let le0M' : 0 <= M'.
  by rewrite -[0]/(nat2R 0); apply: le_nat2R.
Qed.

Let le0M : 0 <= M.
by apply: le_0_nat2R.
Qed.

Let ltN2ltN1 : nat2R N2 < log (nat2R N1).
Proof.
rewrite -[nat2R N2]log_pow.
have -> : 2 ^ N2 = nat2R 4 by rewrite -[4%nat]/(2 ^ 2)%nat nat2Rpow.
apply: log_increasing; last by apply: lt_nat2R.
by apply: lt_0_nat2R.
Qed.

Lemma log_log_ge0 n : (N1 <= n)%nat -> 0 <= log (log (nat2R n)).
Proof.
move=> leN1n; apply: log_ge_0; apply: log_ge_1; apply: (le_nat2R 2).
by apply: leq_trans leN1n.
Qed.

Theorem bigO_sum_primeV n : (N1 <= n)%nat ->
 \sum_(1 <= p < n.+1 | prime p) / (nat2R p) <= M * (log (log (nat2R n))).
Proof.
move=> leNn; set S := (X in X <= _).
(* We introduce the least m such that n <= 2 ^ m, and its properties *)
(* may be better with up? *)
have /nfloor_ex [m [lemlogn lelogmSm]]: 0 <= log (nat2R n).
  apply: Rlt_le; apply: log_gt_0; apply: (lt_nat2R 1).
  by apply: leq_trans leNn.
rewrite -nat2RE in lemlogn.
have {lelogmSm} lelogmSm: log (nat2R n) < nat2R m.+1 by rewrite S_nat2R.
have lt0n : (0 < n)%nat by apply: leq_trans leNn; apply: ltn_trans le2N.
have lt0N : 0 < nat2R n by apply: (lt_nat2R 0).
have le1logn : 1 <= log (nat2R n).
  rewrite -log_2. apply: log_increasingW; auto; apply: (le_nat2R 2).
  by apply: leq_trans leNn.
have lt0m : (0 < m)%nat.
  by case: (posnP m)=> // em0; move/Rgt_not_le: lelogmSm; rewrite em0.
have lenm : (n.+1 <= (2 ^ m.+1).+1)%nat.
  rewrite ltnS; apply: nat2R_le.
  apply: log_le_inv => //; first by apply: lt_0_nat2R; rewrite expn_gt0.
  by rewrite nat2Rpow log_pow; apply: Rlt_le.
have leNm : (N2 <= m)%nat.
 rewrite -ltnS; apply: nat2R_lt. apply: Rlt_trans lelogmSm.
 apply: Rlt_le_trans ltN2ltN1 _; apply: log_increasingW.
   by apply: lt_0_nat2R; apply: ltn_trans le2N.
 by apply: le_nat2R.
(* We majorize S by the same sum up to 2^m.+1 *)
have t1 : S <= \sum_(1 <= p < (2 ^ m.+1).+1 | prime p) / nat2R p.
  rewrite (big_cat_nat _ _ _ _ lenm) //= -(Rplus_0_r S).
  apply: Rplus_le_compat_l; apply sumR_ge0=> i; rewrite mem_iota; case/andP=> ltin.
  move=> _ _. apply: Rlt_le; apply: Rinv_0_lt_compat; apply: (lt_nat2R 0).
  by apply: ltn_trans ltin.
apply: Rle_trans t1 _ => {S}; set S := (X in X <= _).
have t2 : M * (log (nat2R m)) <= M * log (log (nat2R n)).
  apply: Rmult_le_compat_l => //.
  apply: log_increasingW=> //; exact: lt_0_nat2R.
apply: Rle_trans t2=> {lt0n lelogmSm lt0N lenm leNn lemlogn le1logn n}.
(* We express S as a double sum. *)
have {S} -> : S = / nat2R 2 +
   \sum_(1 <= k < m.+1) \sum_((2 ^ k).+1 <= p <
      (2 ^ k.+1).+1 | prime p) / nat2R p.
  rewrite {}/S; elim: m lt0m {leNm} => [|m ihm] // _.
  rewrite [in RHS]big_nat_recr //=.
  have le2m: ((2 ^ m.+1).+1 <= (2 ^ m.+2).+1)%nat by rewrite ltnS leq_exp2l.
  rewrite [LHS](big_cat_nat _ _ _ _ le2m) ?expn_gt0 //= -[RHS]Rplus_assoc.
  congr (_ + _) => //; case: (posnP m) => [-> | lt0m]; last exact: ihm.
  rewrite expn1 [in RHS]big_nil big_mkcond /= 2?big_nat_recr //= big_nil.
  by rewrite !Rplus_0_l Rplus_0_r.
(* We introduce the harmonic sum S' and majorize S using S' *)
pose S' := \sum_(1 <= k < m.+1) / nat2R k. set S := (X in _ + X <= _).
have majSS' : S <= nat2R 2 * S'.
  rewrite /S' big_distrr /=; apply: leR_sum=> /= i; rewrite mem_iota subn1 /=.
  rewrite  add1n => /andP [lt0i ltiSm] _.
  have -> : (2 ^ i.+1 = (2 ^ i).*2)%nat by rewrite expnS mul2n.
  apply: Rle_trans (le_sum_inv (2 ^ i)%nat _) _.
    by rewrite -[1%nat]/(2 ^ 0)%nat ltn_exp2l.
  apply: Rmult_le_compat_l; first by apply: (le_nat2R 0 2).
  apply: Rinv_le_contravar; first by apply: lt_0_nat2R.
  by rewrite nat2Rpow log_pow.
have {majSS'} majSS' : / nat2R 2 +  S <= / nat2R 2 + nat2R 2 * S'.
   by apply: Rplus_le_compat_l.
apply: Rle_trans majSS' _.
have {S} majS' : / nat2R 2 + nat2R 2 * S' <= nat2R 3 * S'.
  have -> : nat2R 3 * S' = S' + nat2R 2 * S'.
    rewrite -[X in _ = X + _]Rmult_1_l -Rmult_plus_distr_r.
    by rewrite  -[nat2R 1 + _]plus_nat2R.
  apply: Rplus_le_compat_r. rewrite /S' big_nat_recl //.
  rewrite -[/ 2]Rplus_0_r; apply: Rplus_le_compat.
    apply:  Rinv_le_contravar => //.
    by apply: (le_nat2R 1 2).
  apply: sumR_ge0 => i; rewrite mem_iota; case/andP=> lt0i _ _.
  apply: Rlt_le; apply: Rinv_0_lt_compat.
  by apply: lt_0_nat2R.
apply: Rle_trans majS' _.
(* Std majorization of the harmonic series *)
have maj_harm : nat2R 3 * S' <= nat2R 3 * M' * (log (nat2R m)).
  rewrite Rmult_assoc; apply: Rmult_le_compat_l; last first.
    exact: Rle_trans (harm _ leNm) _.
  by rewrite -[0]Rplus_0_l; apply Rplus_le_compat.
apply: Rle_trans maj_harm _; apply: Rmult_le_compat_r=> //.
by apply: log_ge_0; apply: (le_nat2R 1).
Qed.

End ForArthur.


(** END HIDE **)


About bigO_sum_primeV.
