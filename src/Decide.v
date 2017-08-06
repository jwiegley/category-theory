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

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Import EqNotations.

Lemma arrows_identity {f x} :
  arrows f = [] -> @termD C objs arrs x x f ≈ Some id.
Proof.
  unfold termD.
  generalize dependent x.
  induction f; simpl; intros; subst; auto.
  - equalities.
    reflexivity.
  - discriminate.
  - assert (arrows f1 = []). {
      destruct (arrows f2); simpl in H.
        now rewrite app_nil_r in H.
      destruct (arrows f1); simpl in H; inversion H.
    }
    assert (arrows f2 = []). {
      destruct (arrows f1); simpl in H.
        assumption.
      destruct (arrows f2); simpl in H; inversion H.
    }
    specialize (IHf2 x).
    destruct (termD_work objs _ _ f2) eqn:?.
    + destruct s.
      specialize (IHf1 x0).
      destruct (termD_work objs _ _ f1) eqn:?.
      * destruct s.
        equalities'; auto.
        equalities; try contradiction.
        red in X.
        red in X0.
        simpl_eq.
        rewrite X, X0; cat.
      * intuition.
    + intuition.
Qed.

Lemma arrows_morph {f a x y} {f' : objs x ~> objs y} :
  arrows f = [a] ->
  arrs a = Some (x; (y; f')) ->
  @termD C objs arrs x y f ≈ Some f'.
Proof.
  unfold termD.
  generalize dependent x.
  induction f; simpl; intros; subst; auto.
  - equalities.
  - inversion_clear H.
    rewrite H0.
    repeat equalities.
    reflexivity.
  - assert ((arrows f1 = [a] ∧ arrows f2 = []) ∨
            (arrows f2 = [a] ∧ arrows f1 = [])). {
      destruct (arrows f1); simpl in H.
        now right.
      destruct (arrows f2); simpl in H.
        rewrite app_nil_r in H.
        now left.
      destruct l; simpl in H.
        inversion H.
      destruct l0; simpl in H; inversion H.
    }
    destruct H1, p.
    + specialize (IHf1 _ f' e H0).
      pose proof (arrows_identity (x:=x) e0).
      unfold termD in X.
      destruct (termD_work objs _ _ f2) eqn:?; [|contradiction].
      destruct s; equalities; [|contradiction].
      destruct (termD_work objs _ _ f1) eqn:?; [|contradiction].
      destruct s; equalities; simpl_eq.
      red in IHf1.
      red in X.
      rewrite IHf1, X.
      cat.
    + specialize (IHf2 _ f' e H0).
      pose proof (arrows_identity (x:=y) e0).
      unfold termD in X.
      destruct (termD_work objs _ _ f1) eqn:?; [|contradiction].
      destruct s; equalities; [|contradiction].
      destruct (termD_work objs _ _ f2) eqn:?; [|contradiction].
      destruct s; equalities; [|contradiction]; simpl_eq.
      red in IHf2.
      red in X.
      rewrite Heqo.
      equalities.
      rewrite IHf2, X.
      cat.
Qed.

Lemma arrows_compose {f x y} {f' : objs x ~> objs y}
      mid i j (i' : objs mid ~> objs y) (j' : objs x ~> objs mid) :
  arrows f = arrows i ++ arrows j ->
  @termD C objs arrs mid y i ≈ Some i' ->
  @termD C objs arrs x mid j ≈ Some j' ->
  @termD C objs arrs x y f ≈ Some (i' ∘ j').
Proof.
  unfold termD.
  generalize dependent x.
  induction f; simpl; intros; subst; auto.
  - equalities'; auto.
    destruct (termD_work objs _ _ i) eqn:?; [|contradiction]; destruct s.
    destruct (termD_work objs _ _ j) eqn:?; [|contradiction]; destruct s.
    repeat equalities; simpl_eq.
      admit.
    admit.
  - assert ((arrows i = [a] ∧ arrows j = []) ∨
            (arrows j = [a] ∧ arrows i = [])). {
      destruct (arrows i); simpl in H.
        now right.
      destruct (arrows j); simpl in H.
        rewrite app_nil_r in H.
        now left.
      destruct l; simpl in H.
        inversion H.
      destruct l0; simpl in H; inversion H.
    }
    destruct H0, p.
    + pose proof (arrows_morph (x:=x) (y:=mid) (f':=j') e).
      unfold termD in X1.
      destruct (arrs a).
        destruct s, s.
        admit.
      admit.
    + admit.
Admitted.

Lemma arrows_decide {x y f f' g g'} :
  @termD C objs arrs x y f = Some f' ->
  @termD C objs arrs x y g = Some g' ->
  list_beq Eq_eqb (arrows f) (arrows g) = true ->
  f' ≈ g'.
Proof.
  unfold termD; intros.
  generalize dependent g.
  generalize dependent x.
  induction f; simpl; intros; equalities.
  - destruct (arrows g) eqn:?; [|discriminate].
    pose proof (arrows_identity (x:=y) Heql).
    unfold termD in X.
    destruct (termD_work objs _ _ g) eqn:?; [|discriminate]; destruct s.
    equalities; simpl_eq.
    inversion_clear H.
    inversion H0; subst; clear H0.
    red in X.
    rewrite X.
    reflexivity.
  - destruct (arrows g) eqn:?; [discriminate|].
    destruct l; [|now equalities].
    equalities.
    pose proof (arrows_morph (x:=x) (y:=y) (f':=f') Heql).
    unfold termD in X.
    destruct (termD_work objs _ _ g) eqn:?; [|discriminate]; destruct s.
    equalities; simpl_eq.
    destruct (arrs a0); [|discriminate].
    destruct s, s; equalities.
    inversion H; subst; clear H.
    inversion H0; subst.
    specialize (X eq_refl).
    red in X.
    symmetry.
    assumption.
  - symmetry in H1.
    destruct (termD_work objs _ _ f2) eqn:?; [|discriminate]; destruct s.
    destruct (termD_work objs _ _ f1) eqn:?; [|discriminate]; destruct s.
    equalities.
    pose proof (arrows_compose (x:=x) (y:=y) (f':=f') x0 f1 f2 h0 h H1).
    simpl_eq.
    unfold termD in *.
    rewrite Heqo in X.
    rewrite Heqo0 in X.
    rewrite !Eq_eq_dec_refl in X.
    equalities; simpl_eq.
    specialize (X (reflexivity _) (reflexivity _)).
    destruct (termD_work objs _ _ g) eqn:?; [|discriminate]; destruct s.
    equalities.
    inversion H; subst.
    inversion H0; subst.
    red in X.
    rewrite X.
    reflexivity.
Admitted.

End Decide.
