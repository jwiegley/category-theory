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
Require Import Solver.Normal.TList.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.
Require Import Solver.Normal.Valid.

Generalizable All Variables.

Section NormalValidSound.

Context `{Env}.

Import EqNotations.

Theorem termD_ArrowList {dom cod} {f : Term} {f'} :
  termD dom cod f = Some f' ->
  ArrowList dom cod.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold termD; induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate].
    subst.
    inversion H0; subst; clear H0.
    constructor.
  - destruct (arrs a) eqn:?; [|discriminate].
    destruct s, s.
    destruct (Pos.eq_dec x dom); [|discriminate].
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst.
    inversion H0; subst; clear H0.
    eapply tcons; eauto.
    econstructor; eauto.
    constructor.
  - destruct (termD_work dom f2) eqn:?; [|discriminate].
    destruct s.
    destruct (termD_work x f1) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst.
    inversion H0; subst; clear H0.
    eapply tlist_app; eauto.
      eapply IHf1; eauto.
      rewrite Heqo0.
      rewrite Eq_eq_dec_refl.
      reflexivity.
    eapply IHf2; eauto.
    rewrite Heqo.
    rewrite Eq_eq_dec_refl.
    reflexivity.
Defined.

Lemma getArrMorph_termD_ArrowList {dom cod} {f : Term} {f'}
      (Hf : termD dom cod f = Some f') :
  getArrMorph (termD_ArrowList Hf) = f'.
Proof.
  unfold termD in Hf.
  induction f; simpl in *.
  - destruct (Pos.eq_dec dom cod); [|discriminate].
    inversion Hf; subst.
    simpl_eq.
Abort.

Theorem ArrowList_termD {dom cod} :
  forall a : ArrowList dom cod,
    ∃ f, tlist_mapv (fun _ _ => arr) a = arrows f ∧
         termD dom cod f = Some (getArrMorph a).
Proof.
  unfold termD; induction a; simpl; intros.
  - exists Identity; simpl.
    split; auto.
    rewrite Pos_eq_dec_refl.
    reflexivity.
  - destruct x; simpl in *.
    destruct IHa, p.
    destruct (termD_work k x) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x0 j); [|discriminate].
    subst; simpl_eq.
    inversion e0; subst; clear e0.
    exists (Compose (Morph arr) x).
    simpl; split.
      now rewrite e.
    rewrite Heqo, present.
    now rewrite !Pos_eq_dec_refl.
Defined.

End NormalValidSound.
