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
  - destruct (arrows g) eqn:?; [|discriminate].
    inversion_clear H.
    destruct (termD_work objs _ _ g) eqn:?; [|discriminate]; destruct s.
    equalities.
    simpl in H0.
    inversion H0.
    rewrite <- H2.
    clear H0 H2.
    clear -Heqo Heql.
    generalize dependent y.
    induction g; intros; simpl in Heql; try discriminate.
    + simpl in Heqo.
      inversion Heqo.
      rewrite (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec _ _ _ _ H0).
      reflexivity.
    + simpl in Heqo.
      destruct (termD_work objs _ _ g2) eqn:?; [|discriminate]; destruct s.
      destruct (termD_work objs _ _ g1) eqn:?; [|discriminate]; destruct s.
      assert (arrows g1 = []).
        destruct (arrows g2); simpl in Heql.
          now rewrite app_nil_r in Heql.
        destruct (arrows g1); simpl in Heql; inversion Heql.
      assert (arrows g2 = []).
        destruct (arrows g1); simpl in Heql.
          assumption.
        destruct (arrows g2); simpl in Heql; inversion Heql.
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
