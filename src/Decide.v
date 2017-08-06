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

Lemma arrows_decide x y f f' g g' :
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
  - destruct g; simpl in *; equalities; simpl_eq.
    + inversion_clear H.
      inversion_clear H0.
      reflexivity.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
    + inversion_clear H.
      destruct (termD_work objs _ _ g2) eqn:?; [|discriminate].
      destruct s.
      destruct (termD_work objs _ _ g1) eqn:?; [|discriminate].
      destruct s.
      equalities.
      inversion_clear H0.
      admit.
  - destruct g; simpl in *; equalities; simpl_eq.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      inversion H; subst.
      inversion H0; subst.
      reflexivity.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      admit.
  - destruct g; simpl in *; equalities; simpl_eq;
    (destruct (termD_work objs _ _ f2) eqn:?; [|discriminate]; destruct s);
    (destruct (termD_work objs _ _ f1) eqn:?; [|discriminate]; destruct s).
    + equalities.
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      admit.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      inversion H; subst; clear H.
      inversion H0; rewrite <- H2; clear H0 H2.
      admit.
    + destruct (termD_work objs _ _ g2) eqn:?; [|discriminate]; destruct s.
      destruct (termD_work objs _ _ g1) eqn:?; [|discriminate]; destruct s.
      equalities.
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      admit.
Admitted.

End Decide.
