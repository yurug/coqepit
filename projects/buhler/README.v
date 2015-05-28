
(*
  J'ai une preuve coq de la structure d'un treillis construit
  à partir d'un treillis sous-jacent.
  Le treillis sous-jacent L est une variable de la preuve ; ses opérations 'join'
  et 'narrow' sont infinitaires. Le nouveau treillis est une map de clés
  vers des éléments de ce treillis, représentée comme une fonction Key -> L.
  Un élément de ce treillis est dit fini si seul un nombre fini de clés est
  associé à un élément autre que 'top' (du treillis sous-jacent).
  J'aimerais montrer que les opérations sur ces maps préservent leur
  finitude (modulo une relation d'équivalence).

  Je ne sais pas comment formaliser de manière pratique le fait que ces
  fonctions soient 'finies'
  (i.e. que l'ensemble des arguments x qui vérifient '(map x) <> top' est fini).
*)


(** Lattice structure *)
Variable L: Type.
Variable join: (L -> Prop) -> L.
Variable narrow: (L -> Prop) -> L.

(* Definition of a join and narrow of arity 2. *)
Definition join2 l1 l2 := join (fun l => l = l1 \/ l = l2).
Definition narrow2 l1 l2 := narrow (fun l => l = l1 \/ l = l2).


(** Map from key to L. *)
Variable Key: Type.

Definition map := Key -> L.

(** Operations of maps using infinatary lattice operators. *)
Definition in_map (map: map) (P: Key -> Prop) : L -> Prop :=
  (fun l => exists p, P p /\ l = map p).

Definition consequence (map: map) (P: Key -> Prop) := narrow (in_map map P).

(* Lattice structure on maps. *)
Definition join_P (map1 map2: map) (P: Key -> Prop) :=
  fun p => join2 (consequence map1 p) (consequence map2 p).



