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
Require Import Solver.Normal.

Generalizable All Variables.

Section Decide.

Program Definition Term_Category {C objs arrs} : Category := {|
  obj := obj_idx;
  hom := fun x y => ∃ f f', @termD C objs arrs x y f = Some f';
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
    @termD C objs arrs x y f ≈ @termD C objs arrs x y g |};
  id := Identity;
  compose := fun _ y _ => Compose y
|}.
Next Obligation.
  equivalence.
  - destruct (termD objs arrs x y x0) eqn:?; auto.
    reflexivity.
  - destruct (termD objs arrs x y x0) eqn:?;
    destruct (termD objs arrs x y y0) eqn:?; auto.
    now symmetry.
  - destruct (termD objs arrs x y x0) eqn:?;
    destruct (termD objs arrs x y y0) eqn:?;
    destruct (termD objs arrs x y z) eqn:?; auto.
      now transitivity h0.
    contradiction.
Defined.
Next Obligation.
  proper.
  destruct (termD objs arrs y z x0) eqn:?;
  destruct (termD objs arrs x y x1) eqn:?;
  destruct (termD objs arrs y z y0) eqn:?;
  destruct (termD objs arrs x y y1) eqn:?; auto.
  now rewrite X, X0.
Defined.
Next Obligation.
  equalities'; auto.
  equalities.
  destruct (termD objs arrs x y f) eqn:?; cat.
Qed.
Next Obligation.
  equalities'; auto.
  equalities.
  destruct (termD objs arrs x y f) eqn:?; cat.
Qed.
Next Obligation.
  destruct (termD objs arrs z w f) eqn:?;
  destruct (termD objs arrs y z g) eqn:?;
  destruct (termD objs arrs x y h) eqn:?; cat.
Qed.
Next Obligation.
  destruct (termD objs arrs z w f) eqn:?;
  destruct (termD objs arrs y z g) eqn:?;
  destruct (termD objs arrs x y h) eqn:?; cat.
Qed.

Existing Instance Term_Category'.

Lemma termD_append C objs arrs x y (f1 : Term) :
  (f1 : @hom (@Term_Category' C objs arrs) x y) ≈ term_normal f1.
Proof.
  simpl.
  generalize dependent y.
  generalize dependent x.
  induction f1; simpl; intros; equalities.
  - reflexivity.
  - destruct (arrs _) eqn:?; auto.
    destruct s, s; equalities.
    equalities'; auto.
    equalities'; auto.
    equalities; reflexivity.
  - specialize (IHf1_1 m y).
    destruct (termD objs arrs m y f1_1) eqn:?;
    destruct (termD objs arrs m y (term_append f1_1 (Identity m))) eqn:?.
Admitted.

Program Definition term_rect' x y (f : Term) :
  ∀ (P : forall (f : Term), Type),
    (∀ o : obj_idx, x = o -> y = o -> P (Identity o))
    → (∀ (x' y' : obj_idx) (a : arr_idx),
          x = x' -> y = y' -> P (Morph x' y' a))
    → (∀ (x m y : obj_idx) (f1 : Term),
          P f1 → ∀ g : Term, P g → P (Compose m f1 g))
    → P f :=
  match f with
  | Identity o => _
  | Morph x y a => _
  | Compose m f g => _
  end.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Lemma term_normal_compose C objs arrs x m y f1 f2 f' g' :
  termD objs arrs m y (term_normal f1) ≈ Some f' ->
  termD objs arrs x m (term_normal f2) ≈ Some g' ->
  @termD C objs arrs x y (term_normal (Compose m f1 f2)) ≈
  @termD C objs arrs x y (Compose m (term_normal f1) (term_normal f2)).
Proof.
  intros.
  unfold term_normal in *.
  simpl term_append in *.
Admitted.

Lemma termD_term_append C objs arrs x m y f1 f2 f' g' :
  termD objs arrs m y (term_normal f1) ≈ Some f' ->
  termD objs arrs x m (term_normal f2) ≈ Some g' ->
  @termD C objs arrs x y (term_normal (Compose m f1 f2)) ≈ Some (f' ∘ g').
Proof.
  intros.
  rewrite term_normal_compose; eauto.
  simpl.
  destruct (termD objs arrs m y (term_normal f1)); auto.
  destruct (termD objs arrs x m (term_normal f2)); auto.
  red in X.
  red in X0.
  cat.
Qed.

Lemma normalize_equiv C objs arrs x y f f' :
  @termD C objs arrs x y f = Some f' ->
  @termD C objs arrs x y (term_normal f) ≈ Some f'.
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
    destruct (termD _ _ _ _ f1) eqn:?; [|discriminate].
    destruct (termD _ _ _ _ f2) eqn:?; [|discriminate].
    inversion_clear H.
    specialize (IHf1 _ _ _ Heqo); clear Heqo.
    specialize (IHf2 _ _ _ Heqo0); clear Heqo0.
    now apply termD_term_append.
Qed.

Lemma normalize_decides C objs arrs x y f f' g g' :
  @termD C objs arrs x y f = Some f' ->
  @termD C objs arrs x y g = Some g' ->
  term_beq (term_normal f) (term_normal g) = true ->
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

Lemma arrows_decide C objs arrs x y f f' g g' :
  @termD C objs arrs x y f = Some f' ->
  @termD C objs arrs x y g = Some g' ->
  arrows_bequiv (arrows f) (arrows g) = true ->
  f' ≈ g'.
Proof.
  intros.
  generalize dependent g'.
  generalize dependent f'.
  generalize dependent g.
  generalize dependent y.
  generalize dependent x.
  induction f; simpl; intros; equalities.
  - destruct g; simpl in *; equalities; simpl_eq.
    + inversion_clear H.
      inversion_clear H0.
      reflexivity.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
    + discriminate.
  - destruct g; simpl in *; equalities; simpl_eq.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      inversion H; subst.
      inversion H0; subst.
      reflexivity.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
  - destruct g; simpl in *; equalities; simpl_eq;
    (destruct (termD _ _ _ _ f1) eqn:?; [|discriminate]);
    (destruct (termD _ _ _ _ f2) eqn:?; [|discriminate]).
    + inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      clear -H1 Heqo0 Heqo1.
      destruct (arrows f1) eqn:?; simpl in H1; [|discriminate].
      destruct (arrows f2) eqn:?; simpl in H1; discriminate.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      destruct (arrows f1) eqn:?; simpl in H1; [|discriminate].
      destruct (arrows f2) eqn:?; simpl in H1; discriminate.
    + destruct (termD _ _ _ _ g1) eqn:?; [|discriminate].
      destruct (termD _ _ _ _ g2) eqn:?; [|discriminate].
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      destruct (arrows f1) eqn:?; simpl in H1;
      destruct (arrows f2) eqn:?; simpl in H1;
      destruct (arrows g1) eqn:?; simpl in H1;
      destruct (arrows g2) eqn:?; simpl in H1;
      equalities; try discriminate;
      repeat match goal with
      | [ H : term_beq _ _ = true |- _ ] => 
        apply term_beq_eq in H; subst
      end;
      rewrite Heqo in Heqo1; inversion_clear Heqo1;
      rewrite Heqo0 in Heqo2; inversion_clear Heqo2;
      reflexivity.
Qed.

End Decide.
