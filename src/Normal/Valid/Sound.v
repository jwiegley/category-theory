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
  termD dom cod f = Some f' -> ArrowList dom cod.
Proof.
  intros.
  pattern f, dom, cod, f'.
  refine (termD_rect (fun dom cod a' a => ArrowList dom cod)
                     _ _ _ _ _ _ _ H0); intros.
  - exact tnil.
  - exact (Build_Arrow dom0 cod0 a f'0 H1 ::: tnil).
  - exact (X +++ X0).
Defined.

Lemma getArrMorph_termD_ArrowList {dom cod} {f : Term} {f'}
      (Hf : termD dom cod f = Some f') :
  getArrMorph (termD_ArrowList Hf) ≈ f'.
Proof.
  unfold termD in Hf.
  induction f; simpl in *.
  - destruct (Pos.eq_dec dom cod); [|discriminate].
    inversion Hf; subst.
    simpl_eq.
    unfold EqdepFacts.internal_eq_rew_r_dep.
    unfold EqdepFacts.internal_eq_sym_involutive.
    unfold EqdepFacts.internal_eq_sym_internal.
    simpl.
Admitted.

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
