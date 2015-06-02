
Require Import ListSet.

(* Auxiliary functions to provide a more complete ListSet implementation.
 * Beware we do use the internal representation of a ListSet. *)

(* Predicate stating that a given type A has decidable equality *)
Definition dec_eq (A : Type) : Type :=
  forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.

Section ListSetEquality.

  Context {A : Type}.
  Variable Adeceq : dec_eq A.
  
  Fixpoint set_contained (s t : set A) : bool :=
    match s with
    | nil      => true
    | cons x u => set_mem Adeceq x t && set_contained u t
    end.
  
  Lemma set_contained_correct : forall s t : set A,
                                  set_contained s t = true ->
                                  (forall a : A, set_In a s -> set_In a t).
    intros s t.
    induction s as [ | x u IHu ].
    - intros. contradiction.
    - intro xu_sub_t. intro y.
      simpl in xu_sub_t.
      apply Bool.Is_true_eq_left, Bool.andb_prop_elim in xu_sub_t.
      destruct xu_sub_t as (x_in_t, u_sub_t).
      intro y_in_xu.
      destruct y_in_xu as [x_eq_y | y_in_u].
      + apply Bool.Is_true_eq_true, set_mem_correct1 in x_in_t.
        rewrite <- x_eq_y. assumption.
      + apply Bool.Is_true_eq_true in u_sub_t.
        apply IHu; assumption.
  Qed.

  Lemma set_contained_complete : forall s t : set A,
                                   (forall a : A, set_In a s -> set_In a t) ->
                                   set_contained s t = true.
    intros s t.
    induction s as [ | x u IHu ].
    - intros. reflexivity.
    - intro xu_sub_t.
      simpl.
      apply Bool.Is_true_eq_true, Bool.andb_prop_intro.
      split.
      + specialize xu_sub_t with x.
        apply Bool.Is_true_eq_left, set_mem_correct2.
        apply xu_sub_t. left. reflexivity.
      + apply Bool.Is_true_eq_left.
        apply IHu.
        intro y. specialize xu_sub_t with y.
        intro y_in_u. apply xu_sub_t.
        right. assumption.
  Qed.

  Lemma set_contained_refl : forall s : set A, set_contained s s = true.
    intro s.
    apply set_contained_complete.
    trivial.
  Qed.

  Lemma set_contained_trans : forall s t u : set A,
                                set_contained s t = true ->
                                set_contained t u = true ->
                                set_contained s u = true.
    intros s t u st tu.
    apply set_contained_complete.
    intros x x_in_s.
    cut (set_In x t).
      generalize x. apply set_contained_correct. assumption.
    cut (set_In x s).
      generalize x. apply set_contained_correct. assumption.
    assumption.
  Qed.

  Definition set_eq (s t : set A) : bool := 
    set_contained s t && set_contained t s.
  
  Lemma set_eq_correct : forall s t : set A,
                           set_eq s t = true ->
                           forall x : A, set_In x s <-> set_In x t.
    intros s t s_eq_t.
    unfold set_eq in s_eq_t.
    apply Bool.Is_true_eq_left, Bool.andb_prop_elim in s_eq_t.
    destruct s_eq_t as (s_sub_t, t_sub_s).
    intro x.
    split.
    - generalize x. apply set_contained_correct.
      apply Bool.Is_true_eq_true. assumption.
    - generalize x. apply set_contained_correct.
      apply Bool.Is_true_eq_true. assumption.
  Qed.      

  Lemma set_eq_complete : forall s t : set A,
                           (forall x : A, set_In x s <-> set_In x t) ->
                           set_eq s t = true.
    intros s t s_eq_t.
    unfold set_eq.
    apply Bool.Is_true_eq_true, Bool.andb_prop_intro.
    split.
    - apply Bool.Is_true_eq_left. apply set_contained_complete. 
      intro x. specialize s_eq_t with x.
      destruct s_eq_t. assumption.
    - apply Bool.Is_true_eq_left. apply set_contained_complete. 
      intro x. specialize s_eq_t with x.
      destruct s_eq_t. assumption.
  Qed.    

  Lemma set_eq_refl : forall s : set A, set_eq s s = true.
    intro s.
    apply set_eq_complete.
    intro x. apply iff_refl.
  Qed.

  Lemma set_eq_sym : forall s t : set A, set_eq s t = true -> set_eq t s = true.
    intros s t s_eq_t.
    apply set_eq_complete.
    intro x. apply iff_sym. generalize x.
    apply set_eq_correct.
    assumption.
  Qed.

  Lemma set_eq_trans : forall s t u : set A,
                         set_eq s t = true ->
                         set_eq t u = true ->
                         set_eq s u = true.
    intros s t u s_eq_t t_eq_u. 
    apply set_eq_complete.
    intro x.
    apply iff_trans with (set_In x t).
    generalize x. apply set_eq_correct. assumption.
    generalize x. apply set_eq_correct. assumption.
  Qed.

End ListSetEquality.
  
Fixpoint set_concat_map {A B} (Bdeceq : dec_eq B) (f : A -> set B) (x : set A) : set B :=
  match x with
  | nil       => empty_set B
  | cons y ys => set_union Bdeceq (f y) (set_concat_map Bdeceq f ys)
  end.

Definition set_filter {A} (p : A -> bool) (x : set A) : set A := List.filter p x.
