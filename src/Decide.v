Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Denote.

Generalizable All Variables.

Section Decide.

Program Instance term_denote_proper C objs arrs dom cod :
  Proper ((fun x y => term_beq x y = true) ==> @equiv _ (@option_setoid _ _))
         (@term_denote C objs arrs dom cod).
Next Obligation.
  proper.
  generalize dependent y;
  generalize dependent cod;
  generalize dependent dom;
  induction x; simpl in *; intros.
  - destruct y; repeat equalities; reflexivity.
  - destruct y0; try discriminate.
    repeat equalities.
    destruct (arrs _); auto.
    destruct s, s; equalities.
    do 4 (equalities'; auto).
    simpl_eq; reflexivity.
  - destruct y; try discriminate.
    repeat equalities.
    specialize (IHx1 m0 cod _ H2).
    specialize (IHx2 dom m0 _ H1).
    destruct (term_denote _ _ _ _ x1) eqn:?;
    destruct (term_denote _ _ _ _ y1) eqn:?;
    try discriminate;
    destruct (term_denote _ _ _ _ x2) eqn:?;
    destruct (term_denote _ _ _ _ y2) eqn:?;
    try discriminate; auto.
    rewrite IHx1, IHx2; reflexivity.
Defined.

Lemma term_denote_term_append C objs arrs x m y f1 f2 f' g' :
  term_denote objs arrs m y (term_append f1 (Identity m)) ≈ Some f' ->
  term_denote objs arrs x m (term_append f2 (Identity x)) ≈ Some g' ->
  @term_denote C objs arrs x y (term_append (Compose m f1 f2) (Identity x)) ≈ Some (f' ∘ g').
Proof.
  simpl; intros.
  destruct (term_append f2 (Identity x)); simpl in *.
  - repeat equalities; simpl_eq.
    admit.
  - admit.
  - simpl.
Admitted.

Lemma normalize_equiv C objs arrs x y f f' :
  @term_denote C objs arrs x y f = Some f' ->
  @term_denote C objs arrs x y (term_append f (Identity x)) ≈ Some f'.
Proof.
  intros.
  generalize dependent y.
  generalize dependent x.
  induction f; intros.
  - simpl in *; repeat equalities.
    inversion_clear H.
    reflexivity.
  - simpl in *.
    destruct (arrs a); [|discriminate].
    destruct s, s; equalities.
    equalities'; auto.
    equalities'; auto.
    equalities; [|discriminate].
    inversion_clear H.
    reflexivity.
  - simpl in H.
    destruct (term_denote _ _ _ _ f1) eqn:?; [|discriminate].
    destruct (term_denote _ _ _ _ f2) eqn:?; [|discriminate].
    inversion_clear H.
    specialize (IHf1 _ _ _ Heqo); clear Heqo.
    specialize (IHf2 _ _ _ Heqo0); clear Heqo0.
    now apply term_denote_term_append.
Qed.

Lemma normalize_decides C objs arrs x y f f' g g' :
  @term_denote C objs arrs x y f = Some f' ->
  @term_denote C objs arrs x y g = Some g' ->
  term_beq (term_append f (Identity x)) (term_append g (Identity x)) = true ->
  f' ≈ g'.
Proof.
  intros.
  apply normalize_equiv in H.
  apply normalize_equiv in H0.
  pose proof (@term_denote_proper C objs arrs x y _ _ H1).
  rewrite <- X in H0; clear X.
  rewrite H in H0; clear H.
  red in H0.
  assumption.
Qed.

End Decide.
