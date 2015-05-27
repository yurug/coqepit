
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
