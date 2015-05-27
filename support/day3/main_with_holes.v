(* Loading libraries and the ssreflect plugin. *)
(* In particular, we are importing formalized material about
   elementary arithmetic *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path div.
Require Import fintype tuple finfun bigop prime finset binomial.

Load "extra_mc.v".

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

Load "extra_R".

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

Load "final.v".

About bigO_sum_primeV.
