
(** Programming exercices in Coq *)

(* Write a function addodd that sums the n first odd numbers.
   Check on a few values that this function produces square numbers.
   How do you state such a fact ? *)

(* Same for the sum of the n first natural numbers, and the
   formula n(n+1)/2. *)

Inductive comparison := Eq | Lt | Gt. (* equal / less-than / greater-than *)

(* Write a compare function of type nat->nat->comparison. *)

(* Write a compare_pos function of type positive->positive->comparison. *)

(* Write a conversion function of type positive->nat.
   State that your comparison functions are compatible with
   this conversion, and test this fact on a few examples. *)

(* Write a few usual functions on lists : append, map, rev... *)

(* Write a function
    tabulate : forall A, (nat -> A) -> nat -> list A
   such that (tabulate f n = f 0 :: f 1 :: ... :: f (n-1)). *)

(* Write a compose function of type :
    forall A B C, (A->B)->(B->C)->(A->C) *)

(* Write a function natiter : forall A, (A->A) -> n -> (A->A)
   such that natiter f n = f^n.
   How do you write the addition over nat via natiter ?
   Same for the multiplication and exponentiation. *)

(* Write a function syracuse : positive->positive such that
    syracuse p = p/2 when p is even, and 3p+1 otherwise.
   State the Syracuse conjecture : repetition of this process
   ultimately reachs 1, regardless of the starting value.
   How do you experimently verify this conjecture for a few values ? *)

(* Define the inductive type of binary trees whose nodes contain
   elements of a given type A.
   Define a conversion function from trees to lists according
   to your favorite traversal order.
   Define a function checking whether a binary tree is perfect
   or not. *)


(* Small arithmetic expressions and stack machine. *)

Inductive expr :=
| Num  : nat -> expr            (* Constant: n *)
| Plus : expr -> expr -> expr   (* Sum:      e1 + e2 *)
| Mult : expr -> expr -> expr.  (* Product:  e1 * e2 *)

(* Define a function eval : expr -> nat. *)

Inductive instr :=
| PUSH : nat -> instr (* Push a value on top of the stack *)
| ADD : instr  (* remove the two topmost values on the stack
                  and replace them by their sum. *)
| MUL : instr.  (* same for multiplication *)
Definition prog := list instr.
Definition stack := list nat.

(* Define a function exec_instr : instr -> stack -> stack.
   Its behavior is unspecified if the stack hasn't enough elements. *)
(* Same for exec_prog : prog -> stack -> stack. *)

(* Provide a compile function of type expr -> prog. *)
(* State its correctness, and test it on some examples *)