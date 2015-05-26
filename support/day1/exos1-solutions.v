
(** * A few propositional proofs. *)

Lemma implrefl (A:Prop) : A -> A.
Proof.
 intro h. assumption. (* or: exact h. *)
Qed.

(** To be compared with:
Lemma implrefl' : forall A:Prop, A -> A.
*)
(* It's the same to having a parameter (A:Prop) in the 1st Lemma,
   or a forall as above. To verify this : Check implrefl. *)

Lemma impltrans (A B C:Prop) : (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros ab bc a.
  apply bc. apply ab. apply a.
  (* or: apply bc, ab, a *)
  (* or: exact (bc (ab a)). *)
Qed.

Lemma andsym (A B:Prop) : A /\ B <-> B /\ A.
Proof.
  split.
  - intros h. destruct h as (a,b). split; assumption.
  - (* intros+destruct could be shorten via a clever "intros": *)
    intros (b,a). split; assumption.
Qed.

Lemma orsym (A B:Prop) : A \/ B <-> B \/ A.
Proof.
  split.
  - intros h. destruct h.
    + right; assumption.
    + left; assumption.
  - (* a more compact formulation, via clever intro, and [ | ] *)
    intros [b|a]; [ right | left ]; assumption.
Qed.

Lemma andasso (A B C:Prop) : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
  split.
  - intros ((a,b),c).
    (* step-by-step proof *)
    split.
    + assumption.
    + split.
      * assumption.
      * assumption.
  - intros (a,(b,c)).
    (* compact proof, thanks to "repeat" and sequence ";" *)
    repeat split; assumption.
Proof.

Lemma orasso (A B C:Prop) : (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  split.
  - intros [[a|b]|c].
    + left. assumption.
    + right. left. assumption.
    + right. right. assumption.
  - intros [a|[b|c]].
    + left. left. assumption.
    + left. right. assumption.
    + right. assumption.
Qed.

Lemma notnot (A:Prop) : A -> ~~A.
Proof.
  intro a. intro na.
  destruct na. (* "apply na" is also fine here (goal is False) *)
  assumption.
Qed.

Lemma ornot (A B:Prop) : (B\/~A) -> (A -> B).
Proof.
  intros [b|na] a.
  - assumption.
  - destruct na. assumption.
Qed.

Lemma contra (A B : Prop) : (A -> B) -> (~B -> ~A).
Proof.
  intros ab nb a; apply nb, ab, a.
  (* or: intros ab nb. contradict nb. apply ab. assumption. *)
Qed.

(* Nota: all these propositional lemmas could also be solved
   via automated tactics, especially "intuition" here. *)

Lemma orasso' (A B C:Prop) : (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
  intuition.
Qed.

(** For the last three statements, try a proof of the reverse
    implication and see where you're stuck. *)

Lemma em0 (A:Prop) : ~~(A \/ ~A). (** This one is harder. *)
Proof.
  (* the easy way: intuition. *)
  intro h.
  apply h. (* avoid "destruct h" here, it discards h ! *)
  right. (* yes, believe me, :-) *)
  intro a.
  apply h. (* again :-) *)
  left. assumption.
Qed.


(** * Some proofs in classical logic *)

(** For classical proofs, we usually pose an extra axiom.
    Here, we simply add an extra hypothesis to our statements. *)

Definition classic := forall A:Prop, ~~A -> A.

Lemma em : classic -> forall A:Prop, A \/ ~A.
Proof.
  intros cl A. apply cl. apply em0.
Qed.

Lemma ornot' : classic -> forall A B:Prop, (A->B) <-> (B\/~A).
Proof.
  intros cl A B.
  split.
  - intros ab. destruct (em cl A) as [a|na].
    + left. apply ab, a.
    + right. assumption.
  - apply ornot.
Qed.

Lemma contra' : classic -> forall A B:Prop, (A->B) <-> (~B->~A).
Proof.
  intros cl A B.
  split.
  - apply contra.
  - intros nab a. apply cl. intros nb. apply nab; assumption.
Qed.

Lemma peirce : classic -> forall A B:Prop, ((A->B)->A)->A.
Proof.
  intros cl A B h.
  apply cl. intros na.
  apply na. apply h. intro a. destruct na. assumption.
Qed.

(** * Some proofs with predicates and relations. *)

(** For the rest of the session, we assume having two predicates
    P and Q over a certain domain X. *)
Parameter X : Set.
Parameter P Q : X -> Prop.

Lemma q0 :
  (forall x, P x /\ Q x) <-> (forall x, P x) /\ (forall x, Q x).
Proof.
  split.
  - intros h. split; intros x; destruct (h x); assumption.
  - intros (h,h') x. split. apply h. apply h'.
Qed.

Lemma q1 :
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  split.
  - intros (x,[p|q]); [left|right]; exists x; assumption.
  - intros [(x,p)|(x,q)]; exists x; [left|right]; assumption.
Qed.

(** We now add a binary relation R over X. *)
Parameter R : X -> X -> Prop.

Lemma q2 :
  (exists y, forall x, R x y) -> forall x, exists y, R x y.
Proof.
  intros (y,h) x. exists y. apply h.
Qed.


(** * The drinker paradox *)

(** State in Coq and prove this classical statement:

   There is someone in the pub such that, if he is drinking,
   everyone in the pub is drinking.

   Of course, we're speaking of a decent pub, that henceforth
   cannot be empty...
*)

Parameter pub : Set.
Parameter pal : pub. (* a way to ensure non-emptyness of our pub. *)
Parameter drinks : pub -> Prop.

Lemma smullyan :
  classic -> exists x:pub, drinks x -> forall y:pub, drinks y.
Proof.
  intros cl.
  (* we reason by case over the existence (or not) of a sober person: *)
 destruct (em cl (exists z, ~drinks z)) as [h|h].
 - (* here, we have a sober person, who satisfy our statement:
      out of a false precondition, we can deduce anything... *)
   destruct h as (z,nd).
   exists z. intro d. destruct nd. assumption.
 - (* here, everybody drinks, so we can pick anybody in the pub,
      for instance our pal. *)
   exists pal.
   intros _ y.
   apply cl. intro nd.
   destruct h. exists y. assumption.
Qed.

(** * Orders and extrema *)

(** Let's assume that our earlier relation R over X is an order: *)
Axiom refl : forall x : X, R x x.
Axiom trans : forall x y z : X, R x y -> R y z -> R x z.
Axiom antisym : forall x y : X, R x y -> R y x -> x = y.

(** We define the notion of smallest element and minimal element: *)
Definition smallest (x0 : X) := forall x:X, R x0 x.
Definition minimal  (x0 : X) := forall x:X, R x x0 -> x = x0.

(** State and prove in Coq the following statements: *)
(** a) If R has a smallest element, it is unique. *)
(** b) The smallest element, if it exists, is also minimal. *)
(** c) If R has a smallest element, there is no other minimal
       elements than this one. *)

Lemma lem_a x y : smallest x -> smallest y -> x = y.
Proof.
  unfold smallest. (* not mandatory, for readability. *)
  intros hx hy.
  apply antisym.
  - apply hx.
  - apply hy.
Qed.

Lemma lem_b x : smallest x -> minimal x.
Proof.
  unfold smallest, minimal.
  intros hx x' hx'.
  apply antisym.
  - apply hx'.
  - apply hx.
Qed.

Lemma lem_c x : smallest x -> forall y, minimal y -> y = x.
Proof.
   unfold smallest, minimal.
   intros hx y hy.
   symmetry.
   apply hy.
   apply hx.
Qed.


(** * Some basic Set theory... *)

(** We reuse the earlier abstract domain X.
    The subsets of X could be represented by predicates of
    type (X->Prop).
*)

Definition setX := X -> Prop.

(** Fix the following definition of an "included" relation
    between subsets of X, and prove that this relation is
    reflexive and transitive. Is it antisymmetric ? *)

Definition included (s s' : setX) := forall x, s x -> s' x.

(* Add a nice notation :-) *)
Infix "⊆" := included (at level 70).


Lemma incl_refl s : s ⊆ s.
Proof.
  intro x. trivial.
Qed.

Lemma incl_trans s1 s2 s3 : s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
Proof.
  intros h12 h23 x h1. apply h23, h12, h1.
Qed.

(* Not full antisymmetry (with respect to Coq's equality "=".
   We only have it with respect to an ad-hoc equivalence. *)

Definition iffX (s s' : setX) := forall x, s x <-> s' x.
Infix "≡" := iffX (at level 70).

(* Let's show it's indeed an equivalence. This allow later to
   use rewrite and other goodies.
   For more details, cf. documentation of type classes and
   setoid equalities... *)

Require Import Setoid Morphisms.
Instance : Equivalence iffX.
Proof.
  split.
  - intros s x. reflexivity.
  - intros s s' h x. symmetry. trivial.
  - intros s1 s2 s3 h12 h23 x. transitivity (s2 x); trivial.
Qed.

Lemma incl_antisym s1 s2 : s1 ⊆ s2 -> s2 ⊆ s1 -> s1 ≡ s2.
Proof.
  intros h12 h21 x. split. apply h12. apply h21.
Qed.


(** Fix below the union and intersection functions between
    subsets of X. Show a few properties of these functions. *)

Definition union (s s' : setX) := fun x => s x /\ s' x.
Definition inter (s s' : setX) := fun x => s x \/ s' x.

(* A few properties about union and inter. *)

Lemma union_sym s s' : union s s' ≡ union s' s.
Proof.
  intros x. unfold union. intuition.
Qed.

Lemma union_inter_distr s1 s2 s3 :
  inter (union s1 s2) s3 ≡ union (inter s1 s3) (inter s2 s3).
Proof.
  intros x. unfold union, inter. intuition.
Qed.

(* Nota: for rewriting inside expressions with union and inter,
   we need to prove that union and inter are morphisms
   with respect to ≡.
*)

Instance : Proper (iffX ==> iffX ==> iffX) union.
Proof.
  intros s1 s1' h1 s2 s2' h2 x. unfold union.
  rewrite (h1 x), (h2 x). reflexivity.
Qed.

Instance : Proper (iffX ==> iffX ==> iffX) inter.
Proof.
  intros s1 s1' h1 s2 s2' h2 x. unfold inter.
  rewrite (h1 x), (h2 x). reflexivity.
Qed.
