
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
