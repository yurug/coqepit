(** The goal of these exercises is to familiarize yourself with
  inductive data structures and predicates to prove the correctness of
  functional programs. You will certainly need to lookup the reference
  manual and sometimes use the search tools of your interface (Query
  Pane in coqide, C-c C-f in ProofGeneral) to solve these exercises. *)

(* ****************************)
(* Prelude, you can ignore it *)
(* ****************************)

Definition convtest {A} (a b : A) (p : a = b) := unit.

Notation convertible a b := (convtest a b (eq_refl a)).
Ltac forward H :=
  match type of H with
    ?A -> ?B => let H' := fresh in assert (H':A); [|specialize (H H'); clear H']
                                                                              
  end.

Notation they_are_convertible := eq_refl.
(* ****************************)

(* Enumerations: proofs on booleans *)

Print bool.
Print true.

(** We define a somewhat trivial function on booleans... *)
Definition is_true_triv (b : bool) : bool :=
  if b then true else false.

(* Show that it is indeed trivial.
  Using [case] you can do case analysis on datatypes during a proof.
  [simpl] and [reflexivity] might be useful too. *)
Lemma is_true_triv_is_trivial b : b = is_true_triv b.
Proof. case b; simpl; reflexivity. Qed.

(** Look at the proof, case distinction = pattern-Matching *)

(** We can see experimentally that constructors are distinct. *)
Check convertible true true.
Fail Check convertible true false.

(* Let's prove it. Use tactics [left], [right] to introduce conjunctions. *)
Lemma bool_case (b : bool) : b = true \/ b = false.
Proof. case b. left. reflexivity. right; reflexivity. Qed.

(* The [discriminate] tactic allows to prove that different constructors
   are distinct. Remember that disequality is defined as 
   [t <> u = (t = u -> False)]. *)

Lemma bool_noconfusion : true <> false.
Proof. intro H. discriminate. Qed. 

(** Define [weekday] as the set of days of the week *)
Inductive weekday : Set :=
| monday | tuesday | wednesday | thursday | friday | saturday | sunday.

(** Define a function [next_day] to compute the day following a given day using
  pattern-matching. *)

Definition next_day (d : weekday) : weekday :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

(* Recursive datatypes. *)
(** Yesterday you've seen Peano naturals, generated from 0 and +1 (S) *)

Print nat.

Definition one : nat := S O.

(** Define three using [S] and [one] *)
Definition three : nat := S (S one).

(** Addition is a recursive definition, structural on the first argument. *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | 0 => m
  | S n => S (add n m)
  end.

(** The natural numbers also enjoy the discrimination property: two
  expressions headed by the same constructor cannot be equal. Prove it
  using previous tactics and have a look at the proof.*)

Lemma nat_noconfusion n : 0 <> S n.
Proof. intro.  discriminate H. Qed.
  
(** Constructors with arguments are injective.
  The [injection] tactic can be used here. *)

Lemma nat_inj n m : S n = S m -> n = m.
Proof. intros H. injection H. trivial. Qed.
  
(* Using simplification, show the following: *)
Lemma add_0_n n : 0 + n = n.
Proof. simpl; reflexivity. Qed.


(** For the next proof, you will need induction and equational reasoning.
  Assuming you have an hypothesis [H : t = u], and want to replace [t] by [u]
  in your goal, you can use [rewrite H] to perform the rewriting (rewrite <- to
  rewrite an equation the other way.

*)
Lemma add_n_0 n : n + 0 = n.
Proof.
  induction n.
  + reflexivity.
  + simpl. rewrite IHn. reflexivity.
Qed.

(* Exercise: define mult by pattern-mathing (on the first argument) *)
Fixpoint mult (n m : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => m + mult n' m
  end.

(* Exercise: Find some simple property on multiplication and prove it *)
Lemma some_property_on_mult m : m * 0 = 0.
Proof.
  induction m; simpl; trivial.
Qed.

(* * Higher-Order functions: 

  Define [iter_fun f n a] that will iterate the function [f] [n] times, starting with 
  seed value [a], by recursion on [n].
 *)
Fixpoint iter_fun {A : Type} (f : A -> A) (n : nat) (a : A) : A :=
  match n with
  | 0 => a
  | S n => f (iter_fun f n a)
  end.

(** Prove the following two lemmas that show the equations [iter_fun0] must respect. *)
Lemma iter_fun0 {A} (f : A -> A) a : iter_fun f 0 a = a.
Proof. reflexivity. (* can do simplification too *) Qed.

Lemma iter_funS {A} (f : A -> A) n a : iter_fun f (S n) a = f (iter_fun f n a).
Proof. reflexivity. Qed.

(* Putting it all together: 
   Prove that iterating next_day 7 times will give you back the same day:
 *)
Lemma next_day_invol (d : weekday) : iter_fun next_day 7 d = d.
Proof.
  destruct d; reflexivity.
Qed.


(* * Simply Linked Lists: a polymorphic datatype. *)

Require Import List.

Print list.

(* [list] is a defined polymorphic recursive datatype with two constructors *)

Definition nat_list := list nat.
Definition bool_list := list bool.

Notation "[]" := nil : list_scope.
Notation " a :: l " := (cons a l) : list_scope.

Definition zerotothree : nat_list := 0 :: 1 :: 2 :: 3 :: [].

(** As usual, [list] enjoy the no confusion property. *)
Lemma list_noconfusion {A} a (l : list A) : [] <> a :: l.
Proof. intro H. inversion H.
       (* Actually, injection is a form of inversion on the equality predicate *)
Qed.

(** State the induction principle associated to lists (without looking at
  [list_rect]...). You can prove it using list_rect though. *)
Lemma list_ind' : forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (a :: l)) ->
    forall l : list A, P l.
Proof. induction l; auto. Qed.

(** We'll now prove a lemma on list concatenation. We put ourseleves in a section
 and parameterize the definitions inside it by some type [T]. *)
Section ListConcatenation.

  Context {T : Type}.

  (** Define the length of a list, we'll use it later. *)

  Fixpoint length (l : list T) : nat :=
    match l with [] => 0 | _ :: l' => S (length l') end.

  (** Concatenation is a simple recursive function. *)
  Fixpoint list_app (l l' : list T) : list T :=
    match l with
    | [] => l'
    | a :: l => a :: list_app l l'
    end.

  (** Use induction to show that concatenating a list with the empty
  list gives back the first list. *)
  
  Lemma list_app_nil l : list_app l nil = l.
  Proof.
    induction l; simpl; trivial.
  (* now tac must solve the goal with [tac; done] where done is defined
     in the standard library. Use [Print Ltac] to see its definition *)
    now rewrite IHl.
  Qed.

End ListConcatenation.

(** At the end of the secion, all definitions inside it using {T} become parameterized
   by this variable: see the types of [list_app] and [list_app_nil]. *)

(** * Back to partial functions: the [option] type.

  Take the max of two optional nats, returning None only if both are
  None. You can use multiple pattern-matching at the same time,
  e.g. (match t, u with p1, p2 => t end *)

Definition max_nat_opt (n m : option nat) : option nat :=
  match n, m with
  | None, None => None
  | Some n, Some m => Some (max n m)
  | None, Some n
  | Some n, None => Some n
    (* As in ocaml, we can write a disjunction of patterns on the left
       if they all bind exactly the same variables with the same types. *)
  end.
               

Lemma max_nat_opt_test1 : max_nat_opt None (Some 1) = Some 1.
Proof. apply they_are_convertible. Qed.

(* Now you can define list lookup as a partial function: if the list is not large 
  enough for the index we return None. Again multi-pattern-matching is useful *)

Section ListLookup.
  Context {A : Type}.

  (** Return the element at index [n] of the list [l], if any. *)
  Fixpoint nth (l : list A) (n : nat) : option A :=
    match l, n with
    | [], _ => None
    | a :: _, 0 => Some a
    | _ :: l, S n => nth l n
    end.

  (** This lemmas need inversion on the [lt] predicate. *)
  Lemma list_lookup_lt n (l : list A) : n < length l -> exists a, nth l n = Some a.
  Proof.
    (* We need to generalize the goal by l first, to get the right induction
       hypothesis. In other words, [l] should not be fixed in the induction 
       hypothesis as we desctruct it before calling nth recursively *)
    revert l.
    induction n; destruct l; simpl; intros Hlen;
    (* Solve the n < length [] -> foo goals *)
    try solve [inversion Hlen].
    now exists a.
    apply IHn. auto with arith.
  Qed.
    
  Lemma list_lookup_gt n l : ~ n < length l -> nth l n = None.
  Proof. 
    revert l.
    induction n; destruct l; simpl; try reflexivity.
    intros H. red in H.
    (* Applying the eliminator for the False proposition appearing in H
       gives us just the premise of H to prove *)
    elim H. apply PeanoNat.Nat.lt_0_succ. (* Found using Search *)
    intros HS. apply IHn.
    intro Hn. elim HS. now apply Lt.lt_n_S. (* Found using Search (S _) < (S _) *)
  Qed.

End ListLookup.

(** Inductive predicates *)

(** Define [ltb] as a boolean test that some natural is strictly less to
another one *)


Fixpoint ltb (n m : nat) :=
  match n, m with
  | 0, 0 => false
  | 0, S _ => true
  | S n, 0 => false
  | S n, S m => ltb n m
  end.

(** Show that this corresponds to the inductive predicate [lt] (defined
  in terms of [le] *)

Lemma ltb_spec : forall x y, ltb x y = true -> lt x y.
Proof.
  (* todo, using [Lt.lt_n_S] and [auto with arith] to discharge [0 < S y'] *)
  induction x as [|x']; destruct y as [|y'] ; simpl; intros; try discriminate.
  auto with arith.
  apply Lt.lt_n_S. now apply IHx'.
Qed.

Lemma nltb_spec : forall x y, ltb x y = false -> ~ lt x y.
Proof.
  induction x as [|x']; destruct y as [|y'] ; simpl; 
  intros Heq Hlt; try discriminate.
  - inversion Hlt.
  - inversion Hlt.
  - eapply IHx'. apply Heq.
    apply Lt.lt_S_n. assumption.
Qed.

(** More inductive predicates: we define a higher-order predicate that
  proves that some predicate holds on every element of a list. *)

Section Forall.
  Context {T : Type}.
  
  Inductive Forall (P : T -> Prop) : list T -> Prop :=
  | forall_nil : Forall P nil
  | forall_cons a l : P a -> Forall P l -> Forall P (a :: l).

  (** Show this property by induction on the list [l], using
   [inversion], [subst] and the [forward] tactic where needed. [subst x]
   substitutes a variable [x] and some term [a] everywhere in the
   context and goal, assuming there is an equation [x = a] in the context.
   The [forward] tactic takes an hypothesis of the form [H : A -> B], adds
   a new subgoal to show [A] and changes the current goal to [H : B |- G].
   *)

  Lemma forall_app P l l' : Forall P l /\ Forall P l' -> Forall P (list_app l l').
  Proof.
    induction l; intros IH. simpl.
    apply (proj2 IH). 
    destruct IH. inversion H; subst.
    forward IHl. 
    simpl. now constructor. 
    simpl. constructor; assumption.
  Qed.

  (** Show the same property using induction on the first [Forall P l] hypothesis 
   instead (this is called "rule" induction). How does it compare to
   the previous proof.? *)
  Lemma forall_app' P l l' : Forall P l -> Forall P l' -> Forall P (list_app l l').
  Proof.
    induction 1; intros HPl'. simpl. apply HPl'.
    simpl. constructor. assumption. apply IHForall. apply HPl'.
  Qed.

  (** Show the following. Be careful about induction loading, i.e. which
    variables are generalized in the induction hypothesis. *)

  Lemma forall_app_inv P l l' : Forall P (list_app l l') -> Forall P l /\ Forall P l'.
  Proof.
    revert l'; induction l; intros l' IH.
    simpl in IH. split; [apply forall_nil|assumption].

    simpl in IH. inversion IH; subst.
    destruct (IHl _ H2) as [Pl Pl'].
    split.
    now apply (forall_cons _ _ _ H1).
    trivial.
  Qed.
End Forall.

(* * Trees, the pervasive data structure. Structural induction on trees
  follows the same idea as for natural numbers: have a look at [tree_ind]. *)

Inductive tree : Set :=
| Leaf : tree
| Node : nat -> tree -> tree -> tree.

Definition empty := Leaf.

Definition all0s := Node 0 empty empty.

(* Structural recursion on trees: *)

Fixpoint height (t : tree) : nat :=
  match t with
    |Leaf => 0
    |Node _ t1 t2 => max (height t1) (height t2) + 1
  end.

Remark all0sheight : height all0s = 1.
Proof.
  apply they_are_convertible.
Qed.

(** Define the size function on a tree by recursion. *)
Fixpoint size (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ l r => S (size l + size r)
  end.

(** This is to avoid unnecessary qualifications *)
Import PeanoNat.

(** Exercise: Use the search tools to find the lemmas on [max] and [le] 
  necessary to prove the following. *)
Lemma le_height_size : forall t : tree,
           height t <= size t.
Proof.
  induction t; simpl. auto with arith.
  rewrite Nat.add_1_r. apply Le.le_n_S.
  (* We can rewrite with <-> lemmas as if they were equalities *)
  rewrite Nat.max_lub_iff.
  intuition auto with arith. rewrite Nat.add_comm. auto with arith.
Qed.

Definition gt x y := lt y x.

(** A binary inductive predicate: the list of elements represented by a
  tree.  We add conditions that force the tree to be a search tree by
  prescribing that elements on the left of a node labeled by some [n] be
  be strictly smaller than [n] and strictly larger on the right, so we
  can implement an efficient lookup function. *)

Inductive repr : tree -> list nat -> Prop :=
| repr_leaf : repr Leaf []
| repr_node n l ml r mr :
    repr l ml -> repr r mr ->
    Forall (gt n) ml ->
    Forall (lt n) mr ->
    repr (Node n l r) (n :: ml ++ mr).


(** The [In] predicate characterizes membership in a list.  The [in_inv]
  and [Lt.asymm] lemmas are useful here, combined with the [apply .. in
  ..]  variant of [apply]. [contradiction] solves goals containing
  hypotheses [A] and [~ A] using elimination of falsehood.  *)

Lemma forall_gt_notin {l x y} : Forall (gt y) l -> y < x ->
                              ~ In x l.
Proof.
  induction 1; intros Hyx Inxl. inversion Inxl.
  apply in_inv (* new *) in Inxl. destruct Inxl as [Hax|HInxl].
  subst a. (* new *) red in H. apply Nat.lt_asymm in Hyx. contradiction (* new *).

  apply (IHForall Hyx). assumption.
Qed.

Lemma forall_lt_notin {l x y} : Forall (lt y) l -> x < y ->
                              ~ In x l.
Proof.
  induction 1; intros Hxy Inxl.
  - inversion Inxl.
  - apply in_inv in Inxl.
    destruct Inxl as [Hax|Inxl].
    + subst a. now apply Nat.lt_asymm in Hxy.
    + now apply IHForall. 
Qed.

(** The function [member x t] computes whether [x] belongs
    to the tree [t]. If uses comparisons with the values
    stored in the node so that it only needs to traverse 
    one path down the tree. *)

Fixpoint member x t := 
  match t with
  | Leaf => false
  | Node y t1 t2 =>
    if ltb x y then member x t1
    else
      if ltb y x then member x t2
      else true
  end.

(** Specification and verification of the [empty] tree, just one Leaf *)

Lemma empty_spec : repr Leaf [].
Proof. 
  apply repr_leaf.
Qed.

(** Specification and verification of [member]. The proof works by induction
 on the [repr t E] hypothesis *)

Lemma member_spec : forall x t E,
    repr t E -> (member x t = true <-> In x E).
Proof.
  intros x t E R. induction R.
  (* Case [t = Leaf] *)
  unfold member.
  split; try discriminate.  
  intro H; inversion H.
  
  (* Case [t = Node y t1 t2] *)
  simpl. case_eq (ltb x n); intros Hxn. apply ltb_spec in Hxn.
  rewrite IHR1. (* rewrite with <->, assume it *)
  assert (Inxmr:=forall_lt_notin H0 Hxn).
  rewrite in_app_iff.
  split.
  + intros Inxml. now intuition.
  + intros [Hnx|Hxmlmr].
    * subst x. now apply Nat.lt_irrefl in Hxn.
    * now destruct Hxmlmr.
  + case_eq (ltb n x); intros Hnx.
    apply nltb_spec in Hxn; apply ltb_spec in Hnx.
    rewrite IHR2. assert (Inxml:=forall_gt_notin H Hnx).
    rewrite in_app_iff; split; intros; try solve [ intuition ].
    destruct H1.
    * subst x. contradiction.
    * intuition.
    * apply nltb_spec in Hxn; apply nltb_spec in Hnx.
      assert (n = x). destruct (Nat.lt_total x n); intuition.
      subst n. intuition.
Qed.
