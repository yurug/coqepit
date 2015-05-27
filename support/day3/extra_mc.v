(** BEGIN HIDE **)

Lemma double_sub n : n.*2 - n = n.
Proof. by rewrite -addnn addKn. Qed.

Lemma iota_Sr k : iota 1 k.+1 = iota 1 k ++ [:: k.+1].
Proof. by rewrite -[in LHS](addn1 k) iota_add add1n. Qed.

(** END HIDE **)


(* BEGIN HIDE *)
Section CoprimeProd.

Variables (I : eqType).

Lemma coprime_prodr (r : seq I) (P : pred I) (F : I -> nat) n :
  (forall x, x \in r -> P x -> coprime n (F x)) ->
  coprime n (\prod_(i <- r | P i) F i).
Proof.
elim: r => [|x r ihr] hc; first by rewrite big_nil coprimen1.
have {ihr} ihr : coprime n (\prod_(j <- r | P j) F j).
  by apply: ihr => y ry Py; rewrite hc // in_cons ry orbT.
by rewrite big_cons; case: ifP => Px //; rewrite coprime_mulr hc // in_cons eqxx.
Qed.

Lemma coprime_prodl (r : seq I) (P : pred I) (F : I -> nat) n :
  (forall x, x \in r -> P x -> coprime (F x) n) ->
  coprime (\prod_(i <- r | P i) F i) n.
Proof.
move=> h; rewrite coprime_sym; apply: coprime_prodr=> i; rewrite coprime_sym.
exact: h.
Qed.

End CoprimeProd.

(* END HIDE *)
