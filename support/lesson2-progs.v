(** * Basic programming in Coq *)

(** First, a few keywords about Coq as a programming language:
    - Purely functional (cf. Haskell or a subset of OCaml)
    - Closed world (no I/O, no random, ...)
    - Typed (includes ML-like types, and a lot more)
    - Terminating (hence not Turing-complete)
    - In fact, strongly normalizing (pick your favorite
      reduction strategy !)
    - Total: no exception or abnormal outputs.

    These design choices allow an easy reasoning about "(f x)".
*)


(** I) A quick tour of predefined datatypes and functions. *)

Require Import Bool Arith ZArith List.

(** bool *)
Check true.
Check false.
Check true && false.
Compute true && false.
Print "&&".
Print "||".
Print negb.
Print xorb.
Compute if true && false then false else true.

(** nat : natural numbers via unary encoding *)
Check 0.
Check 10000.
Print Nat.pred. (** or simply pred *)
Compute pred 2.
Compute pred 0. (** Rounded to 0 *)
Check 1+1.
Compute 1+1.
Print "+". (* Nat.add or plus *)
Print "-".
Compute 1-2. (* Rounded to 0 *)
Compute Nat.log2 ((2^10)/3).


(** N : natural numbers via binary encoding *)
Check 10.
Open Scope N.
Check 10.
Check 10%nat.
Compute N.pred 2.
Compute N.pred 0.
Compute (2^(2^8)).
Compute (3^(3^8)).
Compute N.log2 (3^(3^8)).
Check 1+1.
Print "+".
Compute 1-2.
Close Scope N.

(** Z : integers via binary encoding *)
Open Scope Z.
Check 10.
Check -1.
Check 1+1.
Print "+".
Compute 1-2.
Compute 1/0.
Close Scope Z.

(** Pairs *)
Check (1,true).
Check fun (p:nat*bool) => let (a,b) := p in (b,a).

(** Lists *)
Check 1::2::3::nil.
Compute (1::2::3::nil)++(4::5::6::nil).
Locate "::".
Print "++".



(** II) Inductive types *)

(** How are defined these usual types ? *)
(** How do we define new ones ? *)

Print bool.
(* Inductive bool : Set :=
     | true : bool
     | false : bool.  *)

Print nat.
(* Inductive nat : Set :=
     | O : nat
     | S : nat -> nat.  *)

Print N.
(* Inductive N : Set :=
     | N0 : N
     | Npos : positive -> N. *)

Print Z.
(* Inductive Z : Set :=
      | Z0 : Z
      | Zpos : positive -> Z
      | Zneg : positive -> Z. *)

Print positive.
(* Inductive positive : Set :=
     | xI : positive -> positive
     | xO : positive -> positive
     | xH : positive. *)
(* xH is 1, xI adds a lower 1 digit, xO adds a lower 0 digit:
   Hence 6 = 110 = (xO (xI xH)). *)

Print list.
(* Inductive list (A:Type) : Type :=
     | nil : list A
     | cons : A -> list A -> list A. *)
(* This is a first "parameterized" type (by another type A). *)
Check list.
Check list nat.
Check cons 1 nil.
Check nil.
Check nil (A:=bool).

(** Another parameterized type : *)
Print option.
(* Inductive option (A:Type) : Type :=
      | Some : A -> option A
      | None : option A.
*)

(** Nota : some inductive definitions are refused by Coq, since
    they would endanger the coherence of the system.
    Cf. the "positivity condition" in the documentation. *)



(** III) Function abstraction *)

Definition id_nat (n:nat) := n.
Definition id_nat2 (n:nat) : nat := n.
Definition id_nat3 : nat -> nat := fun n => n.
Definition id_nat4 := fun (n:nat) => n.

(** Polymorphism *)

Definition id (A:Type) : A -> A := fun x => x.
Check id.
Definition id2 : forall A, A->A := fun _ x => x.
Check id2.
Definition id3 := fun (A:Type)(x:A) => x.
Check id3.

Compute id _ 0.  (* Coq infers the type argument *)
Compute id nat.  (* Partial application, we're back to id_nat *)

(* Via "implicit arguments", we can hide the types. *)

Definition id4 := fun {A:Type}(x:A) => x.
Check id4 0.
Check id4 (A:=nat).
Check @id4.

(* See also "Set Implicit Arguments". *)



(** IV) Pattern matching *)

Definition negb (b:bool) :=
  match b with
  | true => false
  | false => true
  end.

Print negb. (* we end back with an "if ... then ... else" *)

Definition iszero (n:nat) :=
 match n with
 | O => true
 | S _ => false
 end.

Compute iszero 55.
Print iszero.

Definition pred n := match n with
 | O => O
 | S p => p
 end.

Check pred.
Compute pred 10000.

Definition succ n := S n.
Definition succ' := fun n => S n.
Definition succ'' := S.

(** Complex pattern matching : bi-predecessor *)

Definition predpred n :=
  match n with
   | S (S m) => m
   | _ => O
  end.

Print predpred.



(** V) Recursion *)

Fixpoint double n :=
  match n with
  | O => O
  | S n => S (S (double n))
  end.

Compute double 6.

Fixpoint plus n m :=
 match n with
  | O => m
  | S n' => S (plus n' m)
 end.

Fixpoint div2 n :=
  match n with
   | S (S m) => S (div2 m)
   | _ => O
  end.

Compute div2 22.

(** Fixpoint is no more than a Definition followed by an inner
    recursion operator "fix". *)

Definition plus' :=
  fix plusrec n m :=
    match n with
    | O => m
    | S n' => S (plusrec n' m)
    end.

(** This "fix" construct may help for some tricky recursive
    definitions (ackermann, list merge, ...). *)

(** Fixpoint and polymorphism *)

Fixpoint length {A:Type} (l:list A) :=
  match l with
  | nil => 0
  | x::l' => S (length l')
  end.


(** Restrictions on recursion : the termination checker.
    Coq avoids infinite computations by checking that one
    specific argument gets "structurally smaller" at each
    recursive call.
    Otherwise:
     - undefined objects (e.g. a boolean value not true nor false)
     - contradictory objects (e.g. implying true=false)
     - direct inhabitant of False (you can program your proofs).
*)

(* Fixpoint alien (b:bool) : bool := alien b. *)

(* Fixpoint bogus (b:bool) : bool := negb (bogus b). *)

(* Fixpoint loop (n:nat) : False := loop n.
   Definition impossible : False := loop 0. *)


(** This decreasing constraint might get into the way: *)

Compute 3 <=? 5.
Print "<=?".

Fail Fixpoint div (a b:nat) : nat :=
  if b <=? a
  then S (div (a-b) b)
  else 0.

(** Possible workarounds:
    1) an extra argument used as counter, or "fuel"
    2) old-style approach: use of accessibility relation "acc"
    3) use of modern extensions of Coq: "Function" or "Program"
       (see later). *)


(** The previous "div", with a counter *)

Fixpoint div_count (n:nat)(a b:nat) : nat :=
  match n with
    | 0 => 0
    | S n' =>
        if b <=? a
        then S (div_count n' (a-b) b)
        else 0
  end.

(** Here starting with n=a is always enough. *)

Definition div (a b:nat) : nat := div_count a a b.

Compute (div 100 3).
Compute (div 100 0).

(** Btw, another (awkward) definition of div is directly accepted *)

Fixpoint div_direct a b :=
  match a with
    | O => O
    | S a' =>
      let c := div_direct a' b in
      if ((S c)*b) <=? a then S c else c
  end.

Compute div_direct 100 3.


(** VI) Totality *)

(** By design, all Coq functions are total :
    - when f:A->B and x:A, then (f x) is always meaningful
      (and has type B).
    - no exceptions, failure, non-exhaustive patterns, ...

    Three ways to handle partial functions :
    1) answer an arbitrary value for problematic inputs
      (for instance 2-3=0, or 3/0 = 0)
    2) use the "option" type to mark the lack of output
      (for instance 2-3 = None, 3-2 = Some 1)
    3) use "dependent types" and restrict the input via a
      logical precondition.
       minus : forall a b, b<=a -> nat. *)

Definition pred_option (n:nat) : option nat :=
  match n with
    | O => None
    | S n' => Some n'
  end.

Fixpoint minus_option (a b:nat) : option nat :=
  match a, b with
    | _, 0 => Some a
    | 0, S _ => None
    | S a', S b' => minus_option a' b'
  end.

Compute (minus_option 2 3).
Compute (minus_option 2 2).

(* So far so good, but a real use would be quite painful.
   Think of 3+(5-(4-2)): *)

Definition smallcomputation :=
 match minus_option 4 2 with
 | Some r =>
   match minus_option 5 r with
   | Some r' => Some (3+r')
   | None => None
   end
 | None => None
 end.

Compute smallcomputation.

(** Monads might help in this situation, but that's another story. *)
