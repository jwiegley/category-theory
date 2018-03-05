Set Warnings "-notation-overridden".

Require Import Coq.Bool.Bool.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.
Require Import Solver.Normal.Valid.

Generalizable All Variables.

Section NormalValidSound.

Context `{Env}.

Theorem termD_ValidArrow {dom cod} {f : Term} {f'} :
  termD dom cod f = Some f' ->
  ValidArrow dom cod (arrows f).
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold termD; induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate].
    subst.
    simpl_eq.
    inversion H0; subst; clear H0.
    constructor.
  - destruct (arrs a) eqn:?; [|discriminate].
    destruct s, s.
    destruct (Pos.eq_dec x dom); [|discriminate].
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst.
    simpl_eq.
    inversion H0; subst; clear H0.
    eapply ComposedArrow; eauto.
    constructor.
  - destruct (termD_work dom f2) eqn:?; [|discriminate].
    destruct s.
    destruct (termD_work x f1) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst.
    simpl_eq.
    inversion H0; subst; clear H0.
    eapply ValidArrow_compose; eauto.
      eapply IHf1; eauto.
      rewrite Heqo0.
      rewrite Eq_eq_dec_refl.
      reflexivity.
    eapply IHf2; eauto.
    rewrite Heqo.
    rewrite Eq_eq_dec_refl.
    reflexivity.
Defined.

Theorem ValidArrow_termD {dom cod fs} :
  forall a : ValidArrow dom cod fs,
    ∃ f, arrows f = fs ∧
         termD dom cod f = Some (getArrMorph a).
Proof.
  unfold termD; induction a; simpl; intros.
  - exists Identity; simpl.
    split; auto.
    rewrite Pos_eq_dec_refl.
    reflexivity.
  - destruct IHa, p.
    destruct (termD_work dom x) eqn:?; [|discriminate].
    destruct s.
    destruct (Eq_eq_dec x0 mid); [|discriminate].
    simpl_eq.
    destruct e2.
    inversion e1; subst; clear e1.
    exists (Compose (Morph f) x).
    simpl; split; auto.
    rewrite Heqo, e.
    now rewrite !Pos_eq_dec_refl.
Defined.

End NormalValidSound.
