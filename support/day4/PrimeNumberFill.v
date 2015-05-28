Require Import ZArith.
Require Import Znumtheory.
Require Import Bool.
Require Import Psatz.

Fixpoint pforallb (P:Z->bool) (z:Z) (p:positive):= 
  match p with
  | xH => P z
  | xO p => pforallb P z p && pforallb P (z + Zpos p) p
  | xI p => pforallb P z p && pforallb P (z + Zpos p) p && P (z + (Zpos (xO p)))
  end.

Lemma pforallb_correct (P:Z->bool) (z:Z) (p:positive): 
   pforallb P z p = true -> forall x, z <= x < z + Zpos p -> P x = true.
Proof.
  generalize z;induction p;simpl;clear z;intros z;rewrite ?andb_true_iff.
  (* xI *)
  intros [[H1 H2] H3] x; rewrite Pos2Z.inj_xI;intros Hx. 
  cut ( z <= x < z + Zpos p \/ z + Zpos p <= x < z + 2* Zpos p \/ x = z + 2 * Z.pos p);
    [ | lia].
  intros [W | [W | W]]. 
  eauto.
  apply (IHp _ H2);lia.
  rewrite W;apply H3.
  (* xO *)
  intros [H1 H2] x; rewrite Pos2Z.inj_xO;intros Hx.
  cut (z <= x < z + Zpos p \/ z + Zpos p <= x < z + 2* Zpos p); [ | lia]. 
  intros [W | W]. 
  eauto.
  apply (IHp _ H2);lia.
  (* xH *)
  intros Hz x Hx; assert (H : z = x) by lia; rewrite <-H;trivial.
Qed.

Definition forallb (P : Z -> bool)  (n1 n2:Z) := 
  match n2 - n1 with
  | Zpos p => pforallb P n1 p
  | _      => true
  end.

Lemma forallb_correct (P:Z -> bool) z1 z2: 
  forallb P z1 z2 = true -> forall z, z1 <= z < z2 -> P z = true.
Proof.
  unfold forallb.
  case_eq (z2 - z1).
  (* 0 *)
  intros Hs _ z Hz;lia. 
  (* pos *)
  intros p Hs Hall z Hz. 
  apply (pforallb_correct P z1 p);trivial;lia.
  (* neg *)
  intros p Hs _ z Hz;lia.
Qed.

Definition is_prime (p:Z) := 
  (1 <? p) && forallb (fun z => negb (p mod z =? 0)) 2 p.

Lemma is_prime_correct p : is_prime p = true -> prime p.
Proof.
Admitted.

Lemma prime17 : prime 17.
Proof.
  apply (is_prime_correct 17).
  compute. reflexivity.
Time Qed.

Lemma prime17' : prime 17.
Proof.
  apply (is_prime_correct 17).
  reflexivity.
Time Qed.

Print prime17.

Lemma prime1069 : prime 1069.
Proof.
  apply (is_prime_correct 1069).
  reflexivity.
Time Qed.

Print prime1069.

Ltac prime_tac :=
  match goal with
  | |- prime ?p =>
     apply (is_prime_correct p); reflexivity
  end.

Ltac prime_vm :=
  match goal with
  | |- prime ?p =>
     apply (is_prime_correct p); vm_compute; reflexivity
  end.

Ltac prime_nc :=
  match goal with
  | |- prime ?p =>
     apply (is_prime_correct p); native_compute; reflexivity
  end.

Lemma prime17_l : prime 17.
Proof. prime_tac. Time Qed.

Lemma prime17_vm : prime 17.
Proof. prime_vm. Time Qed.

Lemma prime17_nc : prime 17.
Proof. prime_nc. Time Qed.

Lemma prime1069_l : prime 1069.
Proof. prime_tac. Time Qed.

Lemma prime1069_vm : prime 1069.
Proof. prime_vm. Time Qed.

Lemma prime1069_nc : prime 1069.
Proof. prime_nc. Time Qed.

Lemma prime7919_l : prime 7919.
Proof. prime_tac. Time Qed.

Lemma prime7919_vm : prime 7919.
Proof. prime_vm. Time Qed.

Lemma prime7919_nc : prime 7919.
Proof. prime_nc. Time Qed.

(*Lemma prime65761_l : prime 65761.
Proof. prime_tac. Time Qed. *)

Lemma prime65761_vm : prime 65761.
Proof. prime_vm. Time Qed.

Lemma prime65761_nc : prime 65761.
Proof. prime_nc. Time Qed.

(* Improve the checker *)

Lemma prime_sqrt : forall z, 1 < z -> 
      (forall p, 2 <= p <= Z.sqrt z -> ~(p|z)) -> prime z.
Proof.
  (* You can skip it, in a first time.
     The nia tactic can help ... *)
Admitted.

(* improve again *)
Lemma prime_sqrt_odd : forall z, 1 < z -> ~(2|z) ->
      (forall p, 1 <= p <= Z.sqrt z / 2 -> ~((2*p + 1)|z)) -> prime z.
Proof.
  (* Use the previous lemma *)
Admitted.

Definition is_prime_sqrt p := 
   (1 <? p) && negb (p mod 2 =? 0) && 
    forallb (fun z : Z => negb (p mod (2*z+1) =? 0)) 1 (Z.sqrt p / 2 + 1).

Lemma is_prime_sqrt_correct p : is_prime_sqrt p = true -> prime p.
Proof.
Admitted. 

Ltac prime_nc' :=
  match goal with
  | |- prime ?p =>
     apply (is_prime_sqrt_correct p); native_compute; reflexivity
  end. 

Lemma prime65761''' : prime 65761.
Proof. 
  prime_nc'. 
Time Qed.

Lemma prime100000007 : prime 100000007.
Proof.
  prime_nc'.
Time Qed.

Lemma prime1234567891 : prime 1234567891.
Proof.
 prime_nc'.
Time Qed.

Lemma prime391283958491 : prime 3912839611.
Proof.
  prime_nc'.
Time Qed.

