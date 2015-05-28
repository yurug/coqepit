Require Import List.
Require Import Bool.
Require Import Bool_nat.
Require Import Permutation.

Require Import Mergesort.
Import NatSort.

Definition nat_eqb n1 n2 := 
  match nat_compare n1 n2 with
  | Eq => true
  | _  => false
  end.

Fixpoint all2 {A:Type} (P : A -> A -> bool) (l1 l2:list A) : bool := 
  match l1, l2 with
  | nil, nil       => true
  | a1::l1, a2::l2 => P a1 a2 && all2 P l1 l2
  | _, _           => false
  end.

Lemma all2_eq (l1 l2:list nat) : all2 nat_eqb l1 l2 = true -> l1 = l2.
Proof.
  generalize l2;clear l2;induction l1;destruct l2;simpl;auto;try discriminate.
  rewrite andb_true_iff; intros [H1 H2];rewrite (IHl1 l2);[f_equal | trivial].
  rewrite <-nat_compare_eq_iff. 
  generalize H1;unfold nat_eqb.
  case nat_compare;trivial;discriminate.
Qed.



(************************************************************************)
(*            Type for representing AST                                 *)
(************************************************************************)

Definition var := nat.

Inductive lexpr := 
  | Lnil : lexpr
  | Lvar : var -> lexpr
  | Lapp : lexpr -> lexpr -> lexpr.

Definition valuation A := list (list A).

Fixpoint eval {A:Type} (rho:valuation A) (le:lexpr) : list A:=
  match le with
  | Lnil         => nil
  | Lvar v       => nth v rho nil
  | Lapp le1 le2 => eval rho le1 ++ eval rho le2
  end.



(************************************************************************)
(*          Normalisation and Permutation checker                       *)
(************************************************************************)

Definition vlist := list var.

Fixpoint eval_l {A:Type} (rho:valuation A) (l : vlist) : list A := 
  match l with
  | nil => nil
  | n :: l => nth n rho nil ++ eval_l rho l
  end.

Fixpoint flatten (le:lexpr) : vlist :=
  match le with
  | Lnil         => nil
  | Lvar v       => v :: nil
  | Lapp le1 le2 => flatten le1 ++ flatten le2
  end.

Definition norm le1 := sort (flatten le1).

Definition check_perm (le1 le2:lexpr) := 
   all2 nat_eqb (norm le1) (norm le2).

(************************************************************************)
(*                       Correctness                                    *)
(************************************************************************) 

(** Replace the Admitted by Qed. *)

Lemma eval_l_app {A:Type} (rho:valuation A) (l1 l2 : list var) : 
  eval_l rho (l1 ++ l2) = eval_l rho l1 ++ eval_l rho l2.
Proof.
Admitted. 

Lemma flatten_correct {A:Type} (rho: valuation A) (le:lexpr) : 
  eval rho le =  eval_l rho (flatten le).
Proof.
Admitted.


Lemma Permutation_eval_l {A} (rho : valuation A) l1 l2 :
  Permutation l1 l2 ->
  Permutation (eval_l rho l1) (eval_l rho l2).
Proof.
Admitted.

Lemma norm_correct  {A:Type} (rho: valuation A) (le:lexpr) : 
  Permutation (eval rho le) (eval_l rho (norm le)).
Proof.
Admitted.

Lemma check_perm_correct {A:Type} (rho:valuation A) (le1 le2:lexpr) :
  check_perm le1 le2 = true -> Permutation (eval rho le1) (eval rho le2).
Proof.
Admitted.

(************************************************************************)
(*                          Example                                     *)
(************************************************************************)
  
Lemma test1 {A:Type} (l1 l2 l3 l4:list A) : 
   Permutation ((l1 ++ l2) ++ (l3 ++ (nil ++ l4))) (l1 ++ (nil ++ l2) ++ l3 ++ (l4 ++ nil)).
Proof.
  apply (check_perm_correct (l1 :: l2 :: l3 :: l4 :: nil)
            (Lapp (Lapp (Lvar 0) (Lvar 1)) (Lapp (Lvar 2) (Lapp Lnil (Lvar 3))))
            (Lapp (Lvar 0) (Lapp (Lapp Lnil (Lvar 1)) (Lapp (Lvar 2) (Lapp (Lvar 3) Lnil))))).
  native_compute. reflexivity.
Qed.

(************************************************************************)
(* Infering type automatically the arguments of check_perm_correct      *)
(* using type class                                                     *)
(************************************************************************)

(* reify rho e l : the e is a reification of l with respect to rho 
   invariant     : reify rho e l -> eval rho e is convertible with l
*)
   
Class reify {A:Type} (rho:valuation A) (e:lexpr) (l:list A).

(* Reification of the ++ *)
Instance reify_app {A:Type} (rho:valuation A) e1 e2 l1 l2
  {_: reify rho e1 l1} {_: reify rho e2 l2} : reify rho (Lapp e1 e2) (l1 ++ l2).

(* Reification of nil *)
Instance reify_nil {A:Type} (rho:valuation A) : reify rho Lnil nil.

(* Reification of variables *)
Class IsNth {A:Type} (p:var) (t: list A) (a:A).
Instance IsNth_O {A:Type} a (l:list A) : IsNth O (a :: l) a.
Instance IsNth_S {A:Type} p (a a':A) (l:list A) {_: IsNth p l a} : 
                IsNth (S p) (a'::l) a | 1.

Instance reify_var {A:Type} (rho:valuation A) v l {_:IsNth v rho l} : 
               reify rho (Lvar v) l | 100.

(* Reification of pair of list *)
Class Closed {A:Type} (t:list A).

Instance Closed_nil A : Closed (A:=A) nil.

Instance Closed_cons A (a:A) l {_:Closed l} : Closed (a::l).

Definition reify_2 {A:Type} (rho:valuation A) le1 le2 l1 l2
  {_:reify rho le1 l1} {_:reify rho le2 l2} {_:Closed rho} := 
  (rho, (le1, le2)).

(************************************************************************)
(*                   Testing the reification                            *)
(************************************************************************)
Section Test.

  Variables (A:Type) (l1 l2 l3 l4 : list A).

  Let test := reify_2 _ _ _  
                 ((l1 ++ l2) ++ (l3 ++ (nil ++ l4))) 
                 (l1 ++ (nil ++ l2) ++ l3 ++ (l4 ++ nil)).

  Print test. (* note that the lexpr are automatically infered *)

  Eval red in (reify_2 _ _ _  
                 ((l1 ++ l2) ++ (l3 ++ (nil ++ l4))) 
                 (l1 ++ (nil ++ l2) ++ l3 ++ (l4 ++ nil))).
  (* Eval red : one step of head reduction *)
End Test.


(************************************************************************)
(*                   Building the tactic                                *)
(************************************************************************)

(* Try to understand the tactic *)
Ltac permlist := 
  match goal with
  | |- Permutation ?l1 ?l2 => 
    match eval red in (@reify_2 _ _ _ _ l1 l2 _ _ _) with
    | (?rho, (?le1, ?le2)) =>
      let _le1 := fresh "le1" in
      let _le2 := fresh "le2" in
      pose (_le1 := le1);
      pose (_le2 := le2);
      apply (check_perm_correct rho _le1 _le2);native_compute;apply eq_refl
    end 
  end.

(* Testing the tactic *)
Lemma test1_infer {A:Type} (l1 l2 l3 l4:list A) : 
   Permutation ((l1 ++ l2) ++ (l3 ++ (nil ++ l4)))
                (l1 ++ (nil ++ l2) ++ l3 ++ (l4 ++ nil)).
Proof.
  permlist. 
Qed.

Print test1_infer.

Lemma test2_infer {A:Type} (l1 l2 l3 l4:list A) : 
   Permutation ((l1 ++ l2) ++ (l3 ++ (nil ++ l4)))
                   (l4 ++ (nil ++ l3) ++ l2 ++ (l1 ++ nil)).
Proof.
  permlist. 
Qed.


(* Extending the tactic to deal with cons *)

Lemma cons_app {A:Type} (a:A) l : a::l = (a::nil)++l. 
Proof. Admitted. 

Lemma test3_infer {A:Type} (a1 a2:A) (l1 l2 l3 l4:list A) : 
   Permutation ((a1::l1 ++ a2::l2) ++ (l3 ++ (nil ++ l4)))
                   ((a2::l4) ++ (nil ++ a1::l3) ++ l2 ++ (l1 ++ nil)).
Proof.
   (* use the lemma cons_app *)
Admitted.

Print test3_infer.

(*************************************************************************)
(* Add one instance of reify for (a::l), such that the last script works *)
(*************************************************************************)

(* Hints:
    - it should be an instance of "reify ? ? (a::l)"
    - (a::nil) ++ l is convertible with (a::l) *)

Instance reify_cons (* FILL HERE *)

Lemma test3_infer_auto {A:Type} (a1 a2:A) (l1 l2 l3 l4:list A) : 
   Permutation ((a1::l1 ++ a2::l2) ++ (l3 ++ (nil ++ l4)))
                   ((a2::l4) ++ (nil ++ a1::l3) ++ l2 ++ (l1 ++ nil)).
Proof.
  permlist. 
Qed.

Print test3_infer_auto.



