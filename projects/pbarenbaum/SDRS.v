
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

Definition step_src {A} {s t : @term A} (u : step s t) : term := s.
Definition step_tgt {A} {s t : @term A} (u : step s t) : term := t.

Section FiniteReductionSequences.

    (* Finite reduction sequences ("cons" representation) *)
    Inductive finreduction {A : ARS} :
      forall t s : @term A, Type :=
        | id     : forall {t : term}, finreduction t t
        | frcons : forall {t1 t2 t3 : term},
                     step t1 t2 ->
                     finreduction t2 t3 ->
                     finreduction t1 t3.

    (* Length of a finite reduction sequence *)
    Fixpoint finreduction_length {A : ARS} {s t : @term A}
                                 (P : finreduction t s) : nat :=
      match P with
      | id          => O
      | frcons _ P' => S (finreduction_length P')
      end.

    (* Concatenation of sequences *)
    Fixpoint finreduction_append {A : ARS} {t1 t2 t3 : @term A}
                                 (P : finreduction t1 t2) :
                                 finreduction t2 t3 -> finreduction t1 t3 :=
      match P with
      | id          => fun Q => Q
      | frcons u P' => fun Q => frcons u (finreduction_append P' Q)
      end.

    Definition finreduction_src {A} {s t : @term A} (P : finreduction s t) : term := s.
    Definition finreduction_tgt {A} {s t : @term A} (P : finreduction s t) : term := t.

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

    Lemma finreduction_append_id_left :
            forall {A : ARS} {t1 t2 : @term A} (P : finreduction t1 t2),
              finreduction_append id P = P.
      reflexivity.
    Qed.

    Lemma finreduction_append_id_right :
            forall {A : ARS} {t1 t2 : @term A} (P : finreduction t1 t2),
              finreduction_append P id = P.
      intros A t1 t2 P.
      induction P.
      - reflexivity.
      - simpl. rewrite IHP. reflexivity.
    Qed.

    Lemma finreduction_append_assoc :
            forall {A : ARS} {t1 t2 t3 t4 : @term A}
                   (P : finreduction t1 t2)
                   (Q : finreduction t2 t3)
                   (R : finreduction t3 t4),
              finreduction_append (finreduction_append P Q) R =
              finreduction_append P (finreduction_append Q R).
      intros A t1 t2 t3 t4 P Q R.
      induction P.
      - reflexivity.
      - simpl. rewrite IHP. reflexivity.
    Qed.

End FiniteReductionSequences.

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

(* Deterministic Residual Structure.
 * We are missing the finite developments axiom, which
 * will be treated as an extra hypothesis. *)
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

Notation "v /¹ u"   := (residual_set_step_vs_step u (existT _ _ v))
                           (at level 30).

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
    set_union_map
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

(* Residual of a multistep after a finite reduction *)

Fixpoint residual_set_vs_reduction
             {R : DRS} {t1 t2 : @term (drs_ars R)}
             (P : finreduction t1 t2) :
             forall V : set (outgoing_step t1), set (outgoing_step t2) :=
  match P with                                                 
  | id          => fun V => V
  | frcons u P' => fun V =>
                     residual_set_vs_reduction P' (residual_set_vs_step u V)
  end.

Definition residual_relation_set_vs_reduction
             {R : DRS} {t1 t2 : @term (drs_ars R)}
             (P : finreduction t1 t2)
             (V : set (outgoing_step t1))
             (W : set (outgoing_step t2)) : bool :=
  set_eq (outgoing_step_dec_eq (drs_ars R) t2)
         (residual_set_vs_reduction P V) W.

(* Definition: development.
 *
 * Note:
 *
 *   The standard definition of development is stated for
 *   both finite and infinite sequences, and then most of the
 *   work is done assuming the finite developments theorem.
 *
 *   To avoid this additional complexity, we will simply
 *   work with finite reduction sequences.
 *)

(* A reduction P is relative to a set of redexes V iff
 * every step in P is a residual of some redex in V. *)
Fixpoint relative_to
             {R : DRS} {t1 t2 : @term (drs_ars R)}
             (P : finreduction t1 t2) :
             forall V : set (outgoing_step t1), bool :=
  match P with
  | id          => fun _ => true
  | frcons u P' => fun V =>
    andb (set_mem
           (outgoing_step_dec_eq (drs_ars R) _)
           (existT _ _ u)
           V)
         (relative_to P' (residual_set_vs_step u V))
  end.

(* A reduction PQ is relative to a set of redexes V iff
 * P is relative to V and Q is relative to P/V. *)
Lemma relative_to_append : forall
             {R : DRS} {t1 t2 t3 : @term (drs_ars R)}
             (P : finreduction t1 t2)
             (Q : finreduction t2 t3)
             (V : set (outgoing_step t1)),
               relative_to (finreduction_append P Q) V =
               andb (relative_to P V)
                    (relative_to Q (residual_set_vs_reduction P V)).
  intros R t1 t2 t3 P Q V.
  induction P.
  - reflexivity.
  - cbn. rewrite <- Bool.andb_assoc. apply f_equal.
    rewrite IHP. reflexivity.
Qed.

(* We say a sequence P is "right maximal" with respect to a predicate pred
 * iff
 * - pred holds for P and
 * - P cannot be extended in one step in such a way that
 *   pred also holds for the extended sequence P ++ [u]
 * Since ARSs are assumed to be finitely branching, we may constructively
 * check that a sequence is right maximal wrt pred.
 *)
Definition right_maximal_sequence
             {A : ARS} {s t : @term A}
             (P : finreduction s t)
             (pred : forall t', finreduction s t' -> bool) : bool :=
  pred t P &&
  let steps_from_t := proj1_sig (ars_finitely_branching A t) in
    set_forall
      (fun t'_u =>
         let t' := projT1 t'_u in
         let u  := projT2 t'_u in
           negb (pred t' (finreduction_append P (frcons u id))))
      steps_from_t.

Lemma right_maximal_sequence_correct : forall
             {A : ARS} {s t : @term A}
             (P : finreduction s t)
             (pred : forall t', finreduction s t' -> bool),
    right_maximal_sequence P pred = true ->
    pred t P = true /\
    forall t', forall u : step t t',
        pred t' (finreduction_append P (frcons u id)) = false.
  intros A s t P pred.
  intro P_mxl.
  unfold right_maximal_sequence in P_mxl.  
  apply Bool.Is_true_eq_left, Bool.andb_prop_elim in P_mxl.
  destruct P_mxl as (pred_P, no_extensions).
  split.
  - apply Bool.Is_true_eq_true. assumption.
  - intros t' u.
    apply Bool.Is_true_eq_true in no_extensions.
    assert (no_extensions' := set_forall_correct
                                (outgoing_step_dec_eq _ t) _ _ no_extensions).
    specialize no_extensions' with (existT _ t' u).
    replace false with (negb true); try reflexivity.
    apply Bool.negb_sym. symmetry.
    apply no_extensions'.
    apply (proj2_sig (ars_finitely_branching A t)).
Qed.  

(* A development is a right maximal reduction relative to V. *)
Fixpoint development
             {R : DRS} {s t : @term (drs_ars R)}
             (P : finreduction s t)
             (V : set (outgoing_step s)) : bool :=
  right_maximal_sequence P (fun _ P' => relative_to P' V).

Notation "P ∝ V" := (development P V)
                      (at level 30).

(* Statement of the finite developments property *)

Definition singleton_step {R : DRS} {s : @term (drs_ars R)}
                          (t_u : outgoing_step s) : set (outgoing_step s) :=
  set_add (outgoing_step_dec_eq _ _) t_u (empty_set _).

(* If P1 and P2 develop V, then tgt(P1) = tgt(P2) *)
Definition developments_are_cofinal :=
       forall {R : DRS} {s : @term (drs_ars R)}
                        (V : set (outgoing_step s))
                        {t1 : term} (P1 : finreduction s t1)
                        {t2 : term} (P2 : finreduction s t2),
         P1 ∝ V = true ->
         P2 ∝ V = true ->
         t1 = t2.

(* If P1 and P2 develop V, then u/P1 = u/P2 for all u. *)
Definition developments_induce_same_residual_relation :=
       forall {R : DRS} {s : @term (drs_ars R)}
                        (V : set (outgoing_step s))
                        {t : term} (P1 P2 : finreduction s t),
         P1 ∝ V = true ->
         P2 ∝ V = true ->
         forall {t'} (u : step s t'), 
           set_eq (outgoing_step_dec_eq _ _)
             (residual_set_vs_reduction P1 (singleton_step (existT _ _ u)))
             (residual_set_vs_reduction P2 (singleton_step (existT _ _ u)))
           = true.

Definition finite_developments :=
  developments_are_cofinal /\
  developments_induce_same_residual_relation.

Definition multistep {R : DRS} {s : @term (drs_ars R)}
                     (V : set (outgoing_step s)) : Type :=
  { t : term & { P : finreduction s t | development P V = true } }.

(* Constructively build a development, given a set of steps *)
(**
Definition complete_development
       {R : DRS} {s : @term (drs_ars R)}
       (V : set (outgoing_step s)) : multistep V :=
**)
(*
 * Nope.
 *
 * We need König's lemma to ensure that the facts that
 * - ARSs are finitely branching, and
 * - developments are finite
 * imply that
 * - for any term, there is a bound to the length
 *   of all complete developments starting in that term.
 *
 * TODO: Look for constructive alternatives to König's lemma?
 *)
