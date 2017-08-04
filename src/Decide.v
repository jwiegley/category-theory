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
    + admit.
  - destruct g; simpl in *; equalities; simpl_eq.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      admit.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      admit.
  - destruct g; simpl in *; equalities; simpl_eq;
    (destruct (termD _ _ _ _ f1) eqn:?; [|discriminate]);
    (destruct (termD _ _ _ _ f2) eqn:?; [|discriminate]).
    + inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      clear -H1 Heqo0 Heqo1.
      destruct (arrows f1) eqn:?; simpl in H1; [|discriminate].
      destruct (arrows f2) eqn:?; simpl in H1; [|discriminate].
      admit.
    + destruct (arrs _); [|discriminate].
      destruct s, s; equalities.
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      destruct (arrows f1) eqn:?; simpl in H1.
        destruct (arrows f2) eqn:?; simpl in H1; [discriminate|].
        admit.
      destruct (arrows f2) eqn:?; simpl in H1.
        admit.
      admit.
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
      admit.
Admitted.

End Decide.
