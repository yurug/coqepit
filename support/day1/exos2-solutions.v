
(** Programming exercices in Coq *)

(* Write a function addodd that sums the n first odd numbers.
   Check on a few values that this function produces square numbers.
   How do you state such a fact ? *)

Fixpoint addodd n :=
  match n with
  | 0 => 0
  | S n => (2*n+1) + addodd n
  end.

Compute addodd 10. (* 100 *)

Lemma addodd_spec : forall n, addodd n = n * n.
Admitted.

(* if you want to say that addodd n is a square without telling
   which one : *)

Lemma addodd_spec' : forall n, exists p, addodd n = p * p.
Admitted.

(* You could also avoid doing a multiplication at each step,
   by using tail-recursive programming (i.e. extra arguments
   during recursive loop). *)

Fixpoint addodd_aux n cur sum :=
  match n with
  | 0 => sum
  | S n => addodd_aux n (2+cur) (sum+cur)
  end.

Definition addodd' n := addodd_aux n 1 0.

Compute addodd 10.


(* Same for the sum of the n first natural numbers, and the
   formula n(n+1)/2. *)

Fixpoint addnat n :=
  match n with
  | 0 => 0
  | S n' => n + addnat n'
  end.

Compute addnat 100. (* 5050 *)

Lemma addnat_spec : forall n, 2 * addnat n = n * (n+1).
Admitted.

(* We've transformed the /2 on the right into a 2* on the left.
   Otherwise, we could define a division by two, but then you'll
   need someday to prove it correspond here to mathematical /2
   (especially justify why n*(n+1) is always even hence no
    rounding occurs). *)

Fixpoint div2 n :=
  match n with
    | S (S n) => S (div2 n)
    | _ => 0
  end.

Compute div2 100.

Lemma addnat_spec' : forall n, addnat n = div2 (n * (n+1)).
Admitted.



Inductive comparison := Eq | Lt | Gt. (* equal / less-than / greater-than *)

(* Write a compare function of type nat->nat->comparison. *)

Fixpoint compare_nat n m :=
  match n, m with
  | 0, 0 => Eq
  | 0, _ => Lt
  | _, 0 => Gt
  | S n', S m' => compare_nat n' m'
  end.

(* Write a compare_pos function of type positive->positive->comparison. *)

(* First, an auxiliary function that turns a Eq into
   something else, and otherwise keep the current Lt or Gt. *)

Definition hack_a_comp c c' :=
  match c with
  | Eq => c'
  | _ => c
  end.

Require Import BinPos. (* provides the "positive" type *)

Fixpoint compare_pos p q :=
  match p, q with
  | xH, xH => Eq
  | xH, _ => Lt
  | _, xH => Gt
  | xO p, xO q => compare_pos p q
  | xI p, xI q => compare_pos p q
  | xO p, xI q => hack_a_comp (compare_pos p q) Lt
  | xI p, xO q => hack_a_comp (compare_pos p q) Gt
  end.

Compute compare_pos 564 565.

(* Another solution: tail-rec programming.
   We add an extra argument that encode what to answer
   when the high parts of our numbers are equal.
   See also Pos.compare in the standard library.
 *)

Fixpoint comp p q c :=
  match p, q with
  | xH, xH => c
  | xH, _ => Lt
  | _, xH => Gt
  | xO p, xO q => comp p q c
  | xI p, xI q => comp p q c
  | xO p, xI q => comp p q Lt
  | xI p, xO q => comp p q Gt
  end.

Definition compare_pos' p q := comp p q Eq.

Compute compare_pos' 564 565.


(* Write a conversion function of type positive->nat.
   State that your comparison functions are compatible with
   this conversion, and test this fact on a few examples. *)

Fixpoint pos2nat p :=
  match p with
  | xH => 1
  | xO p => 2 * pos2nat p
  | xI p => 1 + 2 * pos2nat p
  end.

Compute pos2nat 100.

Lemma comp_morphism :
  forall p q,
    compare_nat (pos2nat p) (pos2nat q) = compare_pos p q.
Admitted.

Compute
  let p := 100%positive in
  let q := 101%positive in
  compare_nat (pos2nat p) (pos2nat q) = compare_pos p q.

(* A reverse conversion nat2pos, using operation such as +
   on positive. By convention, nat2pos 0 = 1. *)

Open Scope positive.
Fixpoint nat2pos (n:nat) : positive :=
  match n with
  | O => 1
  | S O => 1
  | S n => 1 + nat2pos n
  end.
Close Scope positive.

(* Write a few usual functions on lists : append, map, rev... *)

Require Import List. (* For the :: notation. *)

Fixpoint append {A:Type} (l l' : list A) :=
  match l with
  | nil => l'
  | x::l => x :: (append l l')
  end.

Fixpoint map {A B:Type} (f:A->B) l :=
  match l with
  | nil => nil
  | x::l => f x :: map f l
  end.

Compute map S (0::1::2::nil).

Fixpoint rev {A:Type} (l:list A) :=
  match l with
  | nil => nil
  | x::l => rev l ++ (x::nil)
  end.

(* Note: ++ is Coq's append, you could also use yours *)

Compute rev (0::1::2::nil).

(* rev above is quadratic. Here comes the usual linear version: *)

Fixpoint rev_append {A:Type} (l l' : list A) :=
  match l with
  | nil => l'
  | x::l => rev_append l (x::l')
  end.

Definition rev' {A:Type} (l:list A) := rev_append l nil.

Compute rev' (0::1::2::nil).

Lemma rev_equiv A : forall (l:list A), rev l = rev' l.
Admitted.


(* Write a function
    tabulate : forall A, (nat -> A) -> nat -> list A
   such that (tabulate f n = f 0 :: f 1 :: ... :: f (n-1)). *)

Fixpoint tabulate {A:Type} (f:nat->A) n :=
  match n with
  | 0 => nil
  | S n => tabulate f n ++ f n :: nil
  end.

Compute tabulate div2 10.

(* Once again, a tail-rec version is also possible (with no ++) *)

(* Write a compose function of type :
    forall A B C, (A->B)->(B->C)->(A->C) *)

Definition compose {A B C:Type} (f:A->B)(g:B->C) : A -> C :=
   fun x => g (f x).

(* Note: doesn't that look very similar with exos1's impltrans ?
   Curry-Howard correspondance at work: *)

Lemma impltrans (A B C:Prop) : (A->B) -> (B->C) -> (A->C).
Proof.
  exact (fun f g x => g (f x)).
Qed.

(* Write a function natiter : forall A, (A->A) -> n -> (A->A)
   such that natiter f n = f^n.
   How do you write the addition over nat via natiter ?
   Same for the multiplication and exponentiation. *)

Fixpoint natiter {A:Type} (f:A->A) n :=
  match n with
  | 0 => fun x => x
  | S n => compose f (natiter f n)
  end.

Definition add := natiter S. (* it's that simple :-) *)
Compute add 3 5. (* 8 *)

Definition mult n m := natiter (add m) n 0.
Compute mult 3 5. (* 15 *)

Definition exp n m := natiter (mult n) m 1.
Compute exp 2 10. (* 1024 *)


(* Write a function syracuse : positive->positive such that
    syracuse p = p/2 when p is even, and 3p+1 otherwise.
   State the Syracuse conjecture : repetition of this process
   ultimately reachs 1, regardless of the starting value.
   How do you experimently verify this conjecture for a few values ? *)

Open Scope positive.

Definition syracuse p :=
  match p with
  | xO p => p
  | _ => 3*p+1
  end.

Compute natiter syracuse 5 1024.

Lemma syracuse_conjecture :
  forall p:positive, exists n:nat, natiter syracuse n p = 1.
Admitted.

(* for tests, we use a modified version that stays at 1 after
   reaching it... *)

Definition syracuse' p :=
  match p with
  | xH => 1
  | xO p => p
  | _ => 3*p+1
  end.

(* Now we "just" have to iterate syracuse' enough times. *)

Compute natiter syracuse' 100 7.

(* To test syracuse conjecture on 1..20 *)

(* A tabulate for positive numbers *)
Definition tabulate_pos {A:Type} (f:positive->A)(p:positive) :=
  tabulate (fun n => f (nat2pos (S n))) (pos2nat p).

Compute tabulate_pos (natiter syracuse' 100) 20.

(* More intersesting : the number of steps needed for convergence.
   count: remaining number of allowed iteration.
   steps: number of iterations already done
 *)

Fixpoint syracuse_iter_and_count count steps p :=
  match count with
  | O => None (* we've exhausted our counter *)
  | S count' =>
    match p with
    | xH => Some steps (* finished, in "steps" steps *)
    | xO p => syracuse_iter_and_count count' (S steps) p
    | _ => syracuse_iter_and_count count' (S steps) (3*p+1)
    end
  end.

Compute syracuse_iter_and_count 100 0 7.
(* syracuse 7 converges in 16 steps *)

Compute
  tabulate_pos (syracuse_iter_and_count 100 0) 20.
  (* in 1..20, syracuse converges at most in 20 steps *)

Close Scope positive.


(* Define the inductive type of binary trees whose nodes contain
   elements of a given type A.
   Define a conversion function from trees to lists according
   to your favorite traversal order.
   Define a function checking whether a binary tree is perfect
   or not. *)

Inductive tree (A:Type) :=
| Leaf : tree A
| Node : A -> tree A -> tree A -> tree A.

(* We make the A argument of Leaf and Node be implicit. *)
Arguments Leaf [A].
Arguments Node [A] a l r.

(* Infix traversal *)
Fixpoint tree2list {A:Type} (t:tree A) :=
  match t with
  | Leaf => nil
  | Node a l r => tree2list l ++ a :: tree2list r
  end.

Compute tree2list (Node 1 (Node 2 Leaf Leaf) (Node 3 Leaf Leaf)).

Require Import Bool. (* For notation "&&" *)

(* Check that a tree is perfect of a given depth n. *)
Fixpoint perfect_n {A:Type} (t:tree A) n :=
  match t, n with
  | Leaf, O => true
  | Leaf, _ => false
  | _, O => false
  | Node _ l r, S n' => perfect_n l n' && perfect_n r n'
  end.

Fixpoint leftmostdepth {A:Type} (t:tree A) :=
  match t with
  | Leaf => 0
  | Node _ t _ => S (leftmostdepth t)
  end.

Definition perfect {A:Type} (t:tree A) :=
  perfect_n t (leftmostdepth t).

Compute perfect (Node 1 (Node 2 Leaf Leaf) (Node 3 Leaf Leaf)).
Compute perfect (Node 1 (Node 2 Leaf Leaf) Leaf).



(* Small arithmetic expressions and stack machine. *)

Inductive expr :=
| Num  : nat -> expr            (* Constant: n *)
| Plus : expr -> expr -> expr   (* Sum:      e1 + e2 *)
| Mult : expr -> expr -> expr.  (* Product:  e1 * e2 *)

(* Define a function eval : expr -> nat. *)

Fixpoint eval e :=
  match e with
  | Num n => n
  | Plus e e' => eval e + eval e'
  | Mult e e' => eval e * eval e'
  end.

Inductive instr :=
| PUSH : nat -> instr (* Push a value on top of the stack *)
| ADD : instr  (* remove the two topmost values on the stack
                  and replace them by their sum. *)
| MUL : instr.  (* same for multiplication *)
Definition prog := list instr.
Definition stack := list nat.

(* Define a function exec_instr : instr -> stack -> stack.
   Its behavior is unspecified if the stack hasn't enough elements. *)

Definition exec_instr i stk :=
  match i, stk with
  | PUSH n, _ => n::stk
  | ADD, a::b::stk => a+b :: stk
  | MUL, a::b::stk => a*b :: stk
  | _, _ => nil (* or anything else, isn't supposed to happen *)
  end.

(* Same for exec_prog : prog -> stack -> stack. *)

Fixpoint exec_prog p stk :=
  match p with
  | nil => stk
  | i::p' => exec_prog p' (exec_instr i stk)
  end.

(* Provide a compile function of type expr -> prog. *)

Fixpoint compile e :=
  match e with
  | Num n => PUSH n :: nil
  | Plus e e' => compile e ++ compile e' ++ ADD::nil
  | Mult e e' => compile e ++ compile e' ++ MUL::nil
  end.

(* State its correctness, and test it on some examples *)

Definition example_expr := Plus (Mult (Num 2) (Num 3)) (Num 5).

Compute eval example_expr.
Compute exec_prog (compile example_expr) nil.

Lemma correctness :
  forall e, exec_prog (compile e) nil = (eval e) :: nil.
Admitted.

(* Or a slightly stronger version speaking of any initial stack
   (this formulation will actually be easier to prove :-). *)

Lemma stronger_correctness :
  forall e stk, exec_prog (compile e) stk = (eval e) :: stk.
Admitted.