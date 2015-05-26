
(** * A few propositional proofs. *)

Lemma implrefl (A:Prop) : A -> A.
Proof.
Admitted.

(** To be compared with:
Lemma p0' : forall A:Prop, A -> A.
*)

Lemma impltrans (A B C:Prop) : (A -> B) -> (B -> C) -> (A -> C).
Proof.
Admitted.

Lemma andsym (A B:Prop) : A /\ B <-> B /\ A.
Proof.
Admitted.

Lemma orsym (A B:Prop) : A \/ B <-> B \/ A.
Proof.
Admitted.

Lemma andasso (A B C:Prop) : (A /\ B) /\ C <-> A /\ (B /\ C).
Proof.
Admitted.

Lemma orasso (A B C:Prop) : (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
Admitted.

Lemma notnot (A:Prop) : A -> ~~A.
Proof.
Admitted.

Lemma ornot (A B:Prop) : (B\/~A) -> (A -> B).
Proof.
Admitted.

Lemma contra (A B : Prop) : (A -> B) -> (~B -> ~A).
Proof.
Admitted.

(** For the last three statements, try a proof of the reverse
    implication and see where you're stuck. *)

Lemma em0 (A:Prop) : ~~(A \/ ~A). (** This one is harder. *)
Proof.
Admitted.


(** * Some proofs in classical logic *)

(** For classical proofs, we usually pose an extra axiom.
    Here, we simply add an extra hypothesis to our statements. *)

Definition classic := forall A:Prop, ~~A -> A.

Lemma em : classic -> forall A:Prop, A \/ ~A.
Proof.
Admitted.

Lemma ornot' : classic -> forall A B:Prop, (A->B) <-> (B\/~A).
Proof.
Admitted.

Lemma contra' : classic -> forall A B:Prop, (A->B) <-> (~B->~A).
Proof.
Admitted.

Lemma peirce : classic -> forall A B:Prop, ((A->B)->A)->A.
Proof.
Admitted.


(** * Some proofs with predicates and relations. *)

(** For the rest of the session, we assume having two predicates
    P and Q over a certain domain X. *)
Parameter X : Set.
Parameter P Q : X -> Prop.

Lemma q0 :
  (forall x, P x /\ Q x) <-> (forall x, P x) /\ (forall x, Q x).
Proof.
Admitted.

Lemma q1 :
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
Admitted.

(** We now add a binary relation R over X. *)
Parameter R : X -> X -> Prop.

Lemma q2 :
  (exists y, forall x, R x y) -> forall x, exists y, R x y.
Proof.
Admitted.


(** * The drinker paradox *)

(** State in Coq and prove this classical statement:

   There is someone in the pub such that, if he is drinking,
   everyone in the pub is drinking.

   Of course, we're speaking of a decent pub, that henceforth
   cannot be empty...
*)



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



(** * Some basic Set theory... *)

(** We reuse the earlier abstract domain X.
    The subsets of X could be represented by predicates of
    type (X->Prop).
*)

Definition setX := X -> Prop.

(** Fix the following definition of an "included" relation
    between subsets of X, and prove that this relation is
    reflexive and transitive. Is it antisymmetric ? *)

Definition included (s s' : setX) := False (* fixme *).

(** Fix below the union and intersection functions between
    subsets of X. Show a few properties of these functions. *)

Definition union (s s' : setX) := s (* fixme *).
Definition inter (s s' : setX) := s (* fixme *).
