
(* coq 8.5beta2 *)

Require Import Coq.Logic.Eqdep.

Require Import ListSet.
Require Import ListSetMore. (* Some auxiliary definitions which should probably
                             * belong in ListSet *)

(* A type is finite if there is a finite set that covers it *)
Definition finite (A : Type) : Type :=
  { carrier : set A | forall x : A, set_In x carrier }.

(* Abstract Rewriting System *)
Structure ARS := mkARS {
    ars_term        : Type ;
    ars_step        : ars_term -> ars_term -> Type ;

    (* Decidable equality *)
    ars_term_dec_eq : dec_eq ars_term ;
    ars_step_dec_eq : forall s t, dec_eq (ars_step s t) ;

    (* Finitely branching *)
    ars_finitely_branching : forall s, finite { t : ars_term & ars_step s t }
}.

Definition term {A} := ars_term A.
Definition step {A} := ars_step A.

(* Finite reduction sequences *)
Inductive finreduction {A : ARS} :
  forall t s : @term A, Type :=
    | id     : forall {t : term}, finreduction t t
    | frcons : forall {t1 t2 t3 : term},
                 step t1 t2 ->
                 finreduction t2 t3 ->
                 finreduction t1 t3.

Fixpoint finreduction_length {A : ARS} {s t : @term A}
                             (P : finreduction t s) : nat :=
  match P with
  | id          => O
  | frcons _ P' => S (finreduction_length P')
  end.

Fixpoint finreduction_append {A : ARS} {t1 t2 t3 : @term A}
                             (P : finreduction t1 t2) :
                             finreduction t2 t3 -> finreduction t1 t3 :=
  match P with
  | id          => fun Q => Q
  | frcons u P' => fun Q => frcons u (finreduction_append P' Q)
  end.

Section ReductionExample.
    Variable A : ARS.
    Variable t : @term A.
    Variable ua ub uc ud ue uf : step t t.
    Check id.
    Check frcons ua id.
    Check frcons ua (frcons ub id).
    Check frcons ua (frcons ub (frcons uc id)).
    Eval compute in
      finreduction_length
        (frcons ua (frcons ub (frcons uc id))).
    Eval compute in
      finreduction_append
        (frcons ua (frcons ub (frcons uc id)))
        (frcons ud (frcons ue (frcons uf id))).
End ReductionExample.
 
(* The type of steps going out from t0 *)
Definition outgoing_step {A : ARS} (t0 : @term A) : Type := { t1 : term & step t0 t1 }.

(* The set of all steps going out from t0 *)
Definition set_of_outgoing_steps {A : ARS} (t0 : @term A) : set (outgoing_step t0) :=
  proj1_sig (ars_finitely_branching A t0).

(* Technical lemma, required for the following one *)
Lemma inj_pair1 :
  forall (A : Type) (B : A -> Type)
         (p q : { a : A & B a }),
         p = q -> projT1 p = projT1 q.
  intros A B p q E. destruct E. reflexivity.
Qed.

(* The type of outgoing steps from a term also has decidable equality. *)
Lemma outgoing_step_dec_eq :
          forall A : ARS, forall t0, dec_eq (@outgoing_step A t0).
Proof.
  intros A t0.
  intros t1_u1 t2_u2.
  destruct t1_u1 as (t1, u1).
  destruct t2_u2 as (t2, u2).
  case (ars_term_dec_eq A t1 t2).
    - intro t1_eq_t2.
      destruct t1_eq_t2.
      case (ars_step_dec_eq A t0 t1 u1 u2).
      + intro u1_eq_u2. destruct u1_eq_u2. left. reflexivity.
      + intro u1_neq_u2. right.
        intro t1u1_eq_t2u2.
        apply inj_pair2 in t1u1_eq_t2u2.
        contradiction.
    - intro t1_neq_t2. right.
      intro t1u1_eq_t2u2.
      apply inj_pair1 in t1u1_eq_t2u2.
      contradiction.
Qed.

(* Deterministic Residual Structure *)
Structure DRS := mkDRS {
    drs_ars : ARS ;
    drs_residual_relation : forall {t1 t2 : @term drs_ars},
                            forall u : step t1 t2,
                            forall t3_v : outgoing_step t1,
                            forall t4_w : outgoing_step t2,
                              bool ;

    (* Axioms of the residual relation *)
    drs_unique_ancestor : forall t1 t2 : @term drs_ars,
                          forall u : step t1 t2,
                          forall t3_v__1 : outgoing_step t1,
                          forall t3_v__2 : outgoing_step t1,
                          forall t4_w : outgoing_step t2,
                            drs_residual_relation u t3_v__1 t4_w = true ->
                            drs_residual_relation u t3_v__2 t4_w = true ->
                              t3_v__1 = t3_v__2 ;
    
    drs_acyclicity      : forall t1 t2 : @term drs_ars,
                          forall u : step t1 t2,
                          forall t3_v : outgoing_step t2,
                            drs_residual_relation u (existT _ _ u) t3_v = false
}.

(* Residual of a step after a step *)

Definition residual_relation_step_vs_step
             {R : DRS} {t1 t2 : @term (drs_ars R)}
             (u : step t1 t2)
             (t3_v : outgoing_step t1)
             (t4_w : outgoing_step t2) : bool :=
    drs_residual_relation R u t3_v t4_w.

Notation "s_v [ u ]¹ t_w" := (residual_relation_step_vs_step u s_v t_w)
                               (at level 30).

Definition residual_set_step_vs_step
             {R : DRS} {t1 t2 : @term (drs_ars R)}
             (u : step t1 t2)
             (t3_v : outgoing_step t1) : set (outgoing_step t2) :=
  set_filter
    (fun t4_w : outgoing_step t2 => t3_v [ u ]¹ t4_w)
    (set_of_outgoing_steps t2).

Notation "v /¹ u"   := (residual_set_step_vs_step u (existT _ _ v)) (at level 30).

Section ResidualStepVsStepExample.
  Variable R : DRS. 
  Variable t1 t2 t3 t4 : @term (drs_ars R).
  Variable u : step t1 t2.
  Variable v : step t1 t3.
  Variable w : step t2 t4.
  Check ((existT _ t3 v) [u]¹ (existT _ t4 w)).
  Check (v /¹ u).
End ResidualStepVsStepExample.

(* Residual of a multistep (set of steps) after a step *)

Definition residual_set_vs_step
             {R : DRS} {t1 t2 : @term (drs_ars R)}
             (u : step t1 t2)
             (V : set (outgoing_step t1)) : set (outgoing_step t2) :=
    set_concat_map
      (outgoing_step_dec_eq (drs_ars R) t2)
      (residual_set_step_vs_step u)
      V.

Definition residual_relation_set_vs_step
             {R : DRS} {t1 t2 : @term (drs_ars R)}
             (u : step t1 t2)
             (V : set (outgoing_step t1))
             (W : set (outgoing_step t2)) : bool :=
  set_eq (outgoing_step_dec_eq (drs_ars R) t2)
    (residual_set_vs_step u V) W.
