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

Lemma arrows_decide {x y f f' g g'} :
  @termD C objs arrs x y f = Some f' ->
  @termD C objs arrs x y g = Some g' ->
  list_beq Eq_eqb (arrows f) (arrows g) = true ->
  f' ≈ g'.
Proof.
  unfold termD; intros.
  generalize dependent g'.
  generalize dependent f'.
  generalize dependent g.
  generalize dependent y.
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
  - idtac.
Admitted.

End Decide.
