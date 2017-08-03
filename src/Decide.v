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

Program Definition Term_Category {C objs arrs} : Category := {|
  obj := obj_idx;
  hom := fun x y => ∃ f f', @term_denote C objs arrs x y f = Some f';
  homset := fun x y => {| equiv := fun f g => `1 `2 f ≈ `1 `2 g |};
  id := fun x => (Identity x; (@id C (objs x); _));
  compose := fun x y z f g => (Compose y `1 f `1 g; (`1 `2 f ∘ `1 `2 g; _))
|}.
Next Obligation. now equalities. Defined.
Next Obligation. now rewrite X2, X0. Defined.

Program Definition Term_Category' {C objs arrs} : Category := {|
  obj := obj_idx;
  hom := fun _ _ => Term;
  homset := fun x y => {| equiv := fun f g =>
    @term_denote C objs arrs x y f ≈ @term_denote C objs arrs x y g |};
  id := Identity;
  compose := fun _ y _ => Compose y
|}.
Next Obligation.
  equivalence.
  - destruct (term_denote objs arrs x y x0) eqn:?; auto.
    reflexivity.
  - destruct (term_denote objs arrs x y x0) eqn:?;
    destruct (term_denote objs arrs x y y0) eqn:?; auto.
    now symmetry.
  - destruct (term_denote objs arrs x y x0) eqn:?;
    destruct (term_denote objs arrs x y y0) eqn:?;
    destruct (term_denote objs arrs x y z) eqn:?; auto.
      now transitivity h0.
    contradiction.
Defined.
Next Obligation.
  proper.
  destruct (term_denote objs arrs y z x0) eqn:?;
  destruct (term_denote objs arrs x y x1) eqn:?;
  destruct (term_denote objs arrs y z y0) eqn:?;
  destruct (term_denote objs arrs x y y1) eqn:?; auto.
  now rewrite X, X0.
Defined.
Next Obligation.
  equalities'; auto.
  equalities.
  destruct (term_denote objs arrs x y f) eqn:?; cat.
Qed.
Next Obligation.
  equalities'; auto.
  equalities.
  destruct (term_denote objs arrs x y f) eqn:?; cat.
Qed.
Next Obligation.
  destruct (term_denote objs arrs z w f) eqn:?;
  destruct (term_denote objs arrs y z g) eqn:?;
  destruct (term_denote objs arrs x y h) eqn:?; cat.
Qed.
Next Obligation.
  destruct (term_denote objs arrs z w f) eqn:?;
  destruct (term_denote objs arrs y z g) eqn:?;
  destruct (term_denote objs arrs x y h) eqn:?; cat.
Qed.

Existing Instance Term_Category'.

Lemma term_denote_append C objs arrs x m y (f1 : Term) :
  (f1 : @hom (@Term_Category' C objs arrs) x y) ≈ term_append f1 (Identity m).
Proof.
  simpl.
  generalize dependent y.
  generalize dependent m.
  generalize dependent x.
  induction f1; simpl; intros; equalities.
  - reflexivity.
  - destruct (arrs _) eqn:?; auto.
    destruct s, s; equalities.
    equalities'; auto.
    equalities'; auto.
    equalities; reflexivity.
  - specialize (IHf1_1 m m y).
    destruct (term_denote objs arrs m y f1_1) eqn:?;
    destruct (term_denote objs arrs m y (term_append f1_1 (Identity m))) eqn:?.
Admitted.

Lemma term_denote_term_append C objs arrs x m y f1 f2 f' g' :
  term_denote objs arrs m y (term_append f1 (Identity m)) ≈ Some f' ->
  term_denote objs arrs x m (term_append f2 (Identity x)) ≈ Some g' ->
  @term_denote C objs arrs x y (term_append (Compose m f1 f2) (Identity x)) ≈ Some (f' ∘ g').
Proof.
  simpl; intros.
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
  apply term_beq_eq in H1.
  rewrite <- H1 in H0.
  rewrite H in H0.
  now red in H0.
Qed.

End Decide.
