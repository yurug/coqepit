
Require Import List.
Require Import Ensembles.
Require Import Bool.
Require Import Even.
Require Import FunctionalExtensionality.

Definition tail (A:Type)(l : list A) : list A :=
  match l with
  | nil => nil
  | cons a l => l
  end.


Definition head (A : Type)(x : A)(l : list A) : A :=
  match l with 
  | nil => x
  | a :: m => a
  end.


Theorem cons_injective : 
  forall (A : Type)(a b : A)(l m : list A),
    a :: l = b :: m <-> l = m /\ a=b.
intros A a b l m.
split.
intro H.
injection H.
intros H0 H1.
split.
apply H0.
apply H1.
intro H.
destruct H as (H0, H1).
f_equal.
apply H1. apply H0.
Qed.

(* GOTO STDLIB *)
Lemma app_inj :forall A:Type, forall (a b c d:list A),
 a++b=c++d -> length a = length c -> a=c /\ b=d.
Proof.
 induction a as [|x a IH]; intros b [|y c] d EQ LEN;
  auto; try discriminate.
 injection EQ; clear EQ; intros EQ1 EQ2.
 destruct (IH b c d); auto with arith. split; congruence.
Qed.


Inductive players :Type :=
|O:players
|P:players
.

Definition reverse_player p:players :=
match p with
|O => P
|P => O
end.

Definition reverse_player_function {A:Type} (lambda:A->players):=
fun x:A =>reverse_player(lambda x).

Lemma reverse_invo : forall p:players, reverse_player(reverse_player p)=p.
Proof.
intro.
destruct p;simpl;reflexivity.
Qed.


Lemma reverse_function_invo : forall A:Type, forall lambda:A->players, reverse_player_function (reverse_player_function lambda)=lambda.
Proof.
intros.
unfold reverse_player_function.
apply functional_extensionality_dep.
intros.
rewrite reverse_invo.
reflexivity.
Qed.

Fixpoint is_alternate_play {A:Type} (lambda:A->players) (l:list(A)) :=
match l with
|nil => True
|a::suite => (lambda a)=O /\ is_alternate_play (reverse_player_function lambda) suite
end.


Definition prefixe {A:Type} (v:list A) (u:list A) := exists w, u = v++w.
 

Lemma even_SS : forall n:nat, even (S (S n)) -> even n.
Proof.
intros.
replace (S (S n)) with (2 + n) in H.
apply even_plus_split in H.
destruct H.
apply H.
destruct H.
apply not_even_and_odd in H.
contradict H.
apply even_S.
apply odd_S.
apply even_O.
simpl.
reflexivity.
Qed.


Lemma odd_SS : forall n:nat, odd (S (S n)) -> odd n.
Proof.
intros.
replace (S (S n)) with (2 + n) in H.
apply odd_plus_split in H.
destruct H.
destruct H.
apply not_even_and_odd in H.
contradict H.
apply even_S.
apply odd_S.
apply even_O.
apply H.
simpl.
reflexivity.
Qed.




Lemma is_alternate_play_app : forall B:Type, forall (p:(list B)), forall (q:(list B)), forall (lambda:B->players),  (is_alternate_play lambda (p++q)  -> (is_alternate_play lambda p /\ ( even (length p) -> is_alternate_play lambda q) /\ (odd (length p) -> is_alternate_play (reverse_player_function lambda) q))) .
Proof.
intro.
intro.
induction p.
intros.
 simpl.
split.
tauto.
split.
intro.
simpl in H.
apply H.
intro.
contradict H0.
intro.
apply (not_even_and_odd 0).
apply even_O.
apply H0.
intros.
split.
simpl in *.
split.
apply H.
destruct H.
assert (G:= (IHp q (reverse_player_function lambda))).
assert (I:= G H0).
destruct I.
apply H1.

split.
simpl in *.
intro.
apply odd_S in H0. 
apply odd_SS in H0.
assert (G:= (IHp q (reverse_player_function lambda))).
destruct H.
assert (I:= G H1).
destruct I.
destruct H3.
assert (J:= H4 H0).
simpl in J.
rewrite reverse_function_invo in J.
apply J.

intro.
simpl in *.
apply even_S in H0. 
apply even_SS in H0.
assert (G:= (IHp q (reverse_player_function lambda))).
destruct H.
assert (I:= G H1).
destruct I.
destruct H3.
assert (J:= H3 H0).
simpl in J.
apply J.
Qed.

Lemma is_alternate_play_prefixe : forall B:Type, forall (lambda:B->players), forall (p:(list B)), forall (q:(list B)), ((prefixe q p) /\ is_alternate_play lambda p ) -> is_alternate_play lambda q.
Proof.
intros.
destruct H.
unfold prefixe in H.
destruct H.
rewrite H in H0.
apply (is_alternate_play_app B q x lambda) in H0.
apply H0.
Qed.



Record Game : Type := MkGame
{moves:Set;
lambda: moves -> players;
plays: Ensemble(list(moves));
alt_plays: forall p:(list(moves)), (plays p)   -> (is_alternate_play lambda p);
prefixe_plays : forall p:(list(moves)), forall q:(list(moves)), (((plays p) /\ (prefixe q p) )  -> (plays q));
plays_not_null : plays nil}.


Definition LinearLambda {A:Game} {B:Game} (x:(sum A.(moves) B.(moves)))  :=
match x with
| inl y => (reverse_player_function (lambda A)) y
| inr y => (lambda B) y
end.


Definition left_sub_element {A:Game}  {B:Game} (a :(moves A + moves B)) : list(moves A) :=
match a with
|(inl y) => y::nil
|(inr y) => nil
end.



Definition right_sub_element {A:Game} {B:Game} (a :(moves A + moves B)) : list(moves B) :=
match a with
|(inl y) => nil
|(inr y) => y::nil
end.

Fixpoint left_sub_play {A:Game} {B:Game} (p:list((sum A.(moves) B.(moves)))) : list(A.(moves)) :=
match p with
| nil => nil
| y :: suite => (left_sub_element y)++(left_sub_play suite)
end.


(**fonctions donnant les séquences obtenues par projection sur B a partir de A cons B **)
Fixpoint right_sub_play {A:Game} {B:Game} (p:list((sum A.(moves) B.(moves)))) : list(B.(moves)) :=
match p with
| nil => nil
| y :: tl => (right_sub_element y)++(right_sub_play tl)
end.

Definition is_linear_play  {A:Game} {B:Game} (p:list((sum A.(moves) B.(moves)))) : Prop :=
(is_alternate_play (LinearLambda) p)/\
 is_alternate_play (A.(lambda))  (left_sub_play p) /\
 is_alternate_play (B.(lambda)) (right_sub_play p) .


Lemma left_sub_play_app : forall A:Game, forall B:Game, forall (p:list((sum A.(moves) B.(moves)))),  forall (q:list((sum A.(moves) B.(moves)))),  (left_sub_play(p++q))  = (left_sub_play  p) ++ (left_sub_play  q).
Proof.
intros.
induction p.

simpl.
reflexivity.

simpl.
rewrite app_ass.
f_equal.
apply IHp.
Qed.


Lemma left_sub_play_prefixe : forall A:Game, forall B:Game, forall (p:list((sum A.(moves) B.(moves)))),  forall (q:list((sum A.(moves) B.(moves)))), prefixe q p  -> prefixe  (left_sub_play q)   (left_sub_play p).
Proof.
intros.
unfold prefixe in H.
destruct H.
unfold prefixe.
exists (left_sub_play  x).
replace p with (q++x).
simpl.
apply left_sub_play_app.

Qed.



Lemma right_sub_play_app : forall A:Game, forall B:Game, forall (p:list((sum A.(moves) B.(moves)))),
  forall (q:list((sum A.(moves) B.(moves)))),
  (right_sub_play(p++q))  = (right_sub_play  p) ++ (right_sub_play  q).
Proof.
intros.
induction p.

simpl.
reflexivity.

simpl.
rewrite app_ass.
f_equal.
apply IHp.
Qed.


Lemma right_sub_play_prefixe : forall A:Game, forall B:Game, forall (p:list((sum A.(moves) B.(moves)))),
  forall (q:list((sum A.(moves) B.(moves)))),
 prefixe q p  -> prefixe  (right_sub_play q)   (right_sub_play p).
Proof.
intros.
unfold prefixe in H.
destruct H.
unfold prefixe.
exists (right_sub_play  x).
replace p with (q++x).
simpl.
apply right_sub_play_app.

Qed.

Program Definition LinearGame (A:Game) (B:Game) : Game := MkGame (sum A.(moves) B.(moves)) (LinearLambda) (is_linear_play ) _ _ _.

Next Obligation.
Proof.
unfold is_linear_play in H.
apply H.
Qed.

Next Obligation.
Proof.
unfold is_linear_play in *.
destruct H.
destruct H1.
split.
apply (is_alternate_play_prefixe ( (moves A + moves B)) LinearLambda p q ).
split.
apply H0.
apply H.
split.
apply (is_alternate_play_prefixe  (moves A ) (lambda A) (left_sub_play p) (left_sub_play q) ).
split.
apply left_sub_play_prefixe.
apply H0.
apply H1.

apply (is_alternate_play_prefixe  (moves B ) (lambda B) (right_sub_play p) (right_sub_play q) ).
split.
apply right_sub_play_prefixe.
apply H0.
apply H2.
Qed.


Next Obligation.
unfold is_linear_play.
simpl.
tauto.
Qed.


(* définition d'une stratégie, avec les propriétés à vérifier *)
Record Strategie (G:Game) : Type := MkStrat 
{strats:(Ensemble(list(moves G)));
even_strats:forall p:(list((moves G))), ((strats p)   -> ((plays G) p)  /\ (even (length  p)));
strats_not_null: strats nil;
prefixe_strats: forall p q:(list((moves G))), ((strats p)/\ (prefixe  q p) /\ (even (length  q)))   ->  (strats q);
deterministic_strats: forall p:(list((moves G))),forall m:(moves G), forall n1:(moves G), forall n2:(moves G),
((strats ( app p (m::n1::nil))) /\ (strats ( app p (m::n2::nil)))) -> (n1=n2)
}.



(* définition de l'ensemble des parties de la stratégie identité*)
Definition is_identity_strat {G:Game} (s:(list (moves (LinearGame G G)))) : Prop := (is_linear_play s) /\ (even (length s)) /\ forall t:(list (moves (LinearGame G G))),
 ((prefixe  t s) /\ (even (length t)) )-> ((left_sub_play t) = (right_sub_play t)).



Program Definition IdentityStrat (G:Game) : (Strategie (LinearGame G G)) := MkStrat (LinearGame G G) (is_identity_strat) _ _ _ _  .

Next Obligation.
Proof.
unfold is_identity_strat in *.
destruct H.
split.
apply H.
apply H0.
Qed.

Next Obligation.
unfold is_identity_strat.
simpl.
split.
unfold is_linear_play.
simpl.
tauto.
split.
apply even_O.
intros.
destruct H.
destruct t.
simpl.
reflexivity.
unfold prefixe in H.
destruct H.
contradict H.
apply nil_cons.
Qed.

Next Obligation.
unfold is_identity_strat in *.
destruct H.
destruct H2.
destruct H0.
split.

apply (prefixe_plays (LinearGame G G) p q).
split.
apply H.
exists x.
apply H0.
split.
apply H1.
intros. 
destruct H4.
apply H3.
split.
2:apply H5.
destruct H4.
exists (x0++x).
rewrite H0.
rewrite H4.
apply app_ass.
Qed.


SearchAbout app.
Lemma identity_deterministic_strats_sub_plays : forall G:Game, (forall (p : list (moves (LinearGame G G)))
     (m n1 n2 : moves (LinearGame G G)),
     ((left_sub_play (p ++ m :: n2 :: nil)) = (right_sub_play (p ++ m :: n2 :: nil))  /\ 

     (left_sub_play (p ++ m :: n1 :: nil)) = (right_sub_play  (p ++ m :: n1 :: nil))) -> n1=n2).
Proof.
intros.
destruct H.

simpl.
rewrite left_sub_play_app in *.
rewrite right_sub_play_app in *.

unfold left_sub_play at 2 in H.

unfold left_sub_play at 2 in H0.
unfold right_sub_play at 2 in H.
unfold right_sub_play at 2 in H0.
rewrite <- app_ass in H0.
rewrite <- app_ass in H0.
rewrite <- app_ass in H0.
rewrite <- app_ass in H0.
apply app_inv_tail in H0.
repeat (rewrite <- app_ass in H).
apply app_inv_tail in H.

destruct n1,n2; simpl in *.
rewrite <- H in H0.
apply app_inv_head in H0.
SearchAbout cons.
f_equal.
apply cons_injective in H0.
apply H0.
repeat (rewrite app_nil_r in *).
rewrite <- H0 in H.

repeat (rewrite -> app_ass in H).
apply app_inj in H.
destruct H.
rewrite <- (app_nil_r (left_sub_element m)) in H1.
apply app_inj in H1.
simpl in H1.
destruct H1.
contradict H2.
apply nil_cons.
rewrite app_nil_r.
reflexivity.
reflexivity.

repeat (rewrite app_nil_r in *).
rewrite <- H in H0.
repeat (rewrite -> app_ass in H0).
apply app_inj in H0.
destruct H0.
simpl in H1.

rewrite <- (app_nil_r (left_sub_element m)) in H1.
apply app_inj in H1.
simpl in H1.

destruct H1.
contradict H2.
apply nil_cons.
rewrite app_nil_r.
reflexivity.
reflexivity.
repeat (rewrite app_nil_r in *).

rewrite H in H0.
apply app_inv_head in H0.
f_equal.
apply cons_injective in H0.
symmetry.
apply H0.
Qed.

Next Obligation.
unfold is_identity_strat in *.
destruct H,H0.
destruct H1,H2.
unfold is_linear_play in *.
destruct H,H0.
destruct H5,H6.
rewrite left_sub_play_app in H5,H6.
rewrite right_sub_play_app in H7,H8.
apply is_alternate_play_app in H.
apply is_alternate_play_app in H5.
apply is_alternate_play_app in H7.
apply is_alternate_play_app in H0.
apply is_alternate_play_app in H6.
apply is_alternate_play_app in H8.
destruct H,H5,H7,H0,H6,H8.
destruct H9,H10,H11,H12,H13,H14.

simpl in *.
assert (H21:=H3 (p ++ m ::  n1 :: nil)).

assert (H22:=H4 (p ++ m :: n2 :: nil)).
assert ( left_sub_play (p ++ m :: n1 :: nil) =
      right_sub_play (p ++ m :: n1 :: nil)).
apply H21.
split. 
exists nil.
intuition.
apply H1.

assert ( left_sub_play (p ++ m :: n2 :: nil) =
      right_sub_play (p ++ m :: n2 :: nil)).
apply H22.
split. 
exists nil.
intuition.
apply H2.


apply (identity_deterministic_strats_sub_plays G p m).
split .
apply H24.
apply H23. 

Qed.

Definition check_adjacency {A B C:Game}  (p:list(sum (sum (moves A) (moves B)) (moves C))) (m:(sum (sum (moves A) (moves B)) (moves C))) :=match p with
nil => True
|a::suite => match m,a with 
              |(inl (inl x)),(inl y) => True 
              |(inl (inl x)),(inr y) => False
              |(inl (inr x)),y => True
              |(inr x), (inl (inl y)) => False
              |(inr x), (inl (inr y)) => True
              |(inr x), (inr y) => True
              end
                
end.


Fixpoint is_cover_play {A B C:Game}  (p:list(sum (sum (moves A) (moves B)) (moves C))):= 
match p with
nil => True
|a::suite => check_adjacency suite a /\ is_cover_play suite

end.








Fixpoint right_center_sub_play {A B C:Game} (p:(list(sum (sum A.(moves) B.(moves)) C.(moves)))) := match p with
nil => nil
|(inr y)::tl => (inr (B.(moves)) y) :: right_center_sub_play  tl
| (inl x)::tl => match x with inl z => right_center_sub_play  tl | inr z => (inl  (C.(moves)) z) :: (right_center_sub_play tl)end
end
.

Fixpoint left_center_sub_play {A B C:Game} (p:(list(sum (sum A.(moves) B.(moves)) C.(moves)))) := match p with
nil => nil
|(inr y)::tl => left_center_sub_play tl
| (inl x)::tl => match x with inl z => (inl (B.(moves)) z ):: left_center_sub_play tl | inr z => (inr  (A.(moves)) z) :: (left_center_sub_play  tl)end
end
.

Definition left_right_sub_element {A B C:Game} (a :(sum (sum A.(moves) B.(moves)) C.(moves))):= match a with 
|(inr y) => (inr (A.(moves)) y)::nil 
| (inl x) => match x with inr z => nil | inl z => (inl  (C.(moves)) z) ::nil end
end.


Fixpoint left_right_sub_play {A B C:Game} (p:(list(sum (sum A.(moves) B.(moves)) C.(moves)))) := match p with
|nil => nil
|hd::tl => left_right_sub_element hd ++ left_right_sub_play tl
end
.

Fixpoint right_right_sub_play {A B C:Game} (p:(list(sum (sum A.(moves) B.(moves)) C.(moves)))) := match p with
nil => nil
|(inr y)::tl => y :: right_right_sub_play  tl
| (inl x)::tl => match x with inr z => right_right_sub_play tl | inl z =>   (right_right_sub_play tl) end
end
.


Fixpoint left_left_sub_play {A B C:Game} (p:(list(sum (sum A.(moves) B.(moves)) C.(moves)))) := match p with
nil => nil
|(inr y)::tl =>left_left_sub_play  tl
| (inl x)::tl => match x with inr z => left_left_sub_play  tl | inl z =>  z :: (left_left_sub_play tl)end
end
.


Fixpoint center_center_sub_play {A B C:Game} (p:(list(sum (sum A.(moves) B.(moves)) C.(moves)))) := match p with
nil => nil
|(inr y)::tl => center_center_sub_play  tl
| (inl x)::tl => match x with inl z => center_center_sub_play  tl | inr z => z:: (center_center_sub_play  tl)end
end
.



Definition is_composed_strat {A B C:Game} (sigma:Strategie (LinearGame A B)) (tau:Strategie (LinearGame B C))  (p:list(moves (LinearGame A C))):=
exists x,is_cover_play x /\ (strats (LinearGame A B) sigma) (left_center_sub_play x) /\ (strats (LinearGame B C)tau)  (right_center_sub_play x) /\ left_right_sub_play x = p.



Lemma left_right_sub_play_p_q :forall A B C:Game, forall p q :list(sum (sum A.(moves) B.(moves)) C.(moves)),
left_right_sub_play (p++q) = left_right_sub_play p ++left_right_sub_play q.
Proof.
intros.
induction p.
simpl.
reflexivity.
simpl.
rewrite IHp.
intuition.
Qed.

Lemma check_adjacency_p_q_a : forall A B C:Game, forall p q :list(sum (sum A.(moves) B.(moves)) C.(moves)), forall a:(sum (sum A.(moves) B.(moves)) C.(moves)),
(p=nil -> check_adjacency (p++q) a= check_adjacency q a )/\ (p<>nil -> check_adjacency (p++q) a = check_adjacency p a).
Proof.
intros.
split.
intro.
induction p.
simpl in *.
reflexivity.
symmetry in H.
contradict H.
apply nil_cons.
intro.
destruct p.
contradict H.
reflexivity.
destruct s,a; simpl in *.
destruct s,s0; simpl in *.
reflexivity.
reflexivity.
reflexivity.
reflexivity.

unfold check_adjacency .
simpl.

Qed.

Lemma is_cover_play_p_q : forall A B C:Game, forall p q :list(sum (sum A.(moves) B.(moves)) C.(moves)),
is_cover_play (p++q) -> is_cover_play p.
Proof.
intros.
induction p.
simpl.
tauto.
simpl in*.
Qed.




Lemma is_cover_play_prefixe : forall A B C:Game, forall p q :list(sum (sum A.(moves) B.(moves)) C.(moves)),
prefixe q p /\ is_cover_play p -> is_cover_play q.
Proof.
intros.
induction q.
unfold is_cover_play.
tauto.
simpl in *.
destruct H.
destruct H.
rewrite H in H0.
simpl in H0.
Qed.

Program Definition ComposedStrat {A B C:Game} (sigma:Strategie (LinearGame A B)) (tau:Strategie (LinearGame B C)) : (Strategie (LinearGame A C)) := MkStrat (LinearGame A C) (is_composed_strat sigma tau) _ _ _ _  .

Next Obligation.
unfold is_composed_strat in H.
induction p.

simpl.
unfold is_linear_play.
simpl.
intuition.

destruct H.
destruct H.
destruct H0.
destruct H1.

split.
unfold is_linear_play.
simpl in *.
split.
split.

destruct a.
simpl in *.
destruct x.
simpl in H2.
contradict H2.
apply nil_cons.
destruct s.
destruct s.

simpl in *.
apply cons_injective in H2.
destruct H2.
injection H3.
intro.
assert (H5:=even_strats (LinearGame A B) sigma (inl m0 :: left_center_sub_play x)).
assert (H6:= H5 H0).

destruct H6.
simpl in *.
unfold is_linear_play in H6.
simpl in H6.
rewrite <- H4.
apply H6.

simpl in *.
assert (H3:=even_strats  (LinearGame A B) sigma (inr m0 :: left_center_sub_play x)).
assert (H4:= H3 H0).
simpl in *.
unfold is_linear_play in H4.
simpl in H4.
destruct H4.
destruct H4.
destruct H4.
assert (H10:=even_strats  (LinearGame B C) tau (inl m0 :: right_center_sub_play x)).
assert (H11:= H10 H1).
simpl in *.
unfold is_linear_play in H11.
simpl in H11.
destruct H11.
destruct H8.
destruct H8.
unfold reverse_player_function in H8.
simpl in H8.
rewrite H4 in H8.
simpl in H8.
discriminate H8.


simpl in *.
apply cons_injective in H2.
destruct H2.
discriminate H3.

destruct x.

simpl in *.
contradict H2.
apply nil_cons.

destruct s.
destruct s.
simpl in H2.
apply cons_injective in H2.
destruct H2.
discriminate H3.
simpl in *.


assert (H3:=even_strats  (LinearGame A B) sigma (inr m0 :: left_center_sub_play x)).
assert (H4:= H3 H0).
simpl in *.
unfold is_linear_play in H4.
simpl in H4.
destruct H4.
destruct H4.
destruct H4.


assert (H10:=even_strats  (LinearGame B C) tau (inl m0 :: right_center_sub_play x)).
assert (H11:= H10 H1).
simpl in *.
unfold is_linear_play in H11.
simpl in H11.
destruct H11.
destruct H8.
destruct H8.
unfold reverse_player_function in H8.
simpl in H8.
rewrite H4 in H8.
simpl in H8.
discriminate H8.


simpl in *.
apply cons_injective in H2.
destruct H2.
injection H3.
intro.
assert (H5:=even_strats (LinearGame B C) tau (inr m0 :: right_center_sub_play x)).
assert (H6:= H5 H1).

destruct H6.
simpl in *.
unfold is_linear_play in H6.
simpl in H6.
rewrite <- H4.
apply H6.

simpl.

simpl in *.
unfold is_linear_play in IHp.
Admitted.




Next Obligation.
unfold is_composed_strat.
exists nil.
simpl in *.
split.
tauto.
split.
apply (strats_not_null (LinearGame A B) sigma).
split.
apply (strats_not_null (LinearGame B C) tau).
reflexivity.
Qed.

Next Obligation.
unfold is_composed_strat in *.
Admitted.

Next Obligation.
Admitted.






