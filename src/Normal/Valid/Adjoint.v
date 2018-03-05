Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Equations.Equations.

Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.
Require Import Solver.Expr.Valid.
Require Import Solver.Expr.Category.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.
Require Import Solver.Normal.Valid.
Require Import Solver.Normal.Valid.Sound.
Require Import Solver.Normal.Category.

Generalizable All Variables.

Section NormalValidAdjoint.

Context `{Env}.

Definition ValidTerm_to_ValidArrow {dom cod} `(f : ValidTerm dom cod t) :
  ValidArrow dom cod (arrows t).
Proof.
  induction f; simpl.
  - constructor.
  - econstructor; eauto.
    constructor.
  - eapply ValidArrow_compose; eauto.
Defined.

Lemma getArrMorph_ValidTerm_to_ValidArrow {dom cod}
      `(f : ValidTerm dom cod t) :
  getArrMorph (ValidTerm_to_ValidArrow f) ≈ getMorph f.
Proof.
  induction f; simpl; cat.
  now rewrite getArrMorph_ValidArrow_compose, IHf1, IHf2.
Qed.

Definition ValidTermEx_to_ValidArrowEx {dom cod} (f : ValidTermEx dom cod) :
  ValidArrowEx dom cod :=
  (arrows `1 f; ValidTerm_to_ValidArrow `2 f).

Program Instance Terms_Arrows : Terms ⟶ Arrows := {
  fobj := fun x => x;
  fmap := @ValidTermEx_to_ValidArrowEx
}.
Next Obligation.
  proper.
  induction x0, y0; simpl in *.
  now rewrite !getArrMorph_ValidTerm_to_ValidArrow.
Qed.
Next Obligation.
  destruct f, g; simpl.
  induction v, v0; simpl; cat.
  - destruct (ValidArrow_compose (_ v0_1) (_ v0_2)); simpl; cat.
  - destruct (ValidArrow_compose (_ v1) (_ v2)); simpl; cat.
  - destruct (ValidArrow_compose (_ v1) (_ v2)); simpl; cat.
  - destruct (ValidArrow_compose (_ v1) (_ v2)); simpl; cat;
    destruct (ValidArrow_compose (_ v0_1) (_ v0_2)); simpl; cat.
    rewrite getArrMorph_ValidArrow_compose; simpl; cat.
Qed.

Definition ValidArrow_to_ValidTerm {dom cod} `(f : ValidArrow dom cod fs) :
  ValidTerm dom cod (unarrows fs).
Proof.
  induction f; simpl.
  - constructor.
  - econstructor; eauto.
    econstructor; eauto.
Defined.

Lemma getMorph_ValidArrow_to_ValidTerm {dom cod}
      `(f : ValidArrow dom cod t) :
  getMorph (ValidArrow_to_ValidTerm f) ≈ getArrMorph f.
Proof.
  induction f; simpl; cat.
Qed.

Definition ValidArrowEx_to_ValidTermEx {dom cod} (f : ValidArrowEx dom cod) :
  ValidTermEx dom cod :=
  (unarrows `1 f; ValidArrow_to_ValidTerm `2 f).

Program Instance Arrows_Terms : Arrows ⟶ Terms := {
  fobj := fun x => x;
  fmap := @ValidArrowEx_to_ValidTermEx
}.
Next Obligation.
  proper.
  destruct x0, y0; simpl in *.
  now rewrite !getMorph_ValidArrow_to_ValidTerm.
Qed.
Next Obligation.
  destruct f, g; simpl.
  induction v, v0; simpl; cat; simpl_eq.
  destruct v; simpl; cat.
Qed.

Definition TA_adj {x y} : Arrows_Terms x ~> y ≊ x ~> Terms_Arrows y.
Proof.
  isomorphism; simpl.
  - morphism; intros.
    + destruct X.
      exact (arrows x0; ValidTerm_to_ValidArrow v).
    + proper.
      destruct x0, y0; simpl in *.
      now rewrite !getArrMorph_ValidTerm_to_ValidArrow.
  - morphism; intros.
    + destruct X.
      exact (unarrows x0; ValidArrow_to_ValidTerm v).
    + proper.
      destruct x0, y0; simpl in *.
      now rewrite !getMorph_ValidArrow_to_ValidTerm.
  - destruct x0; simpl.
    rewrite getArrMorph_ValidTerm_to_ValidArrow.
    rewrite getMorph_ValidArrow_to_ValidTerm.
    reflexivity.
  - destruct x0; simpl.
    rewrite getMorph_ValidArrow_to_ValidTerm.
    rewrite getArrMorph_ValidTerm_to_ValidArrow.
    reflexivity.
Defined.

Lemma TA_to_adj_nat_l {x y c} (f : Arrows_Terms y ~> c) (g : x ~> y) :
  to TA_adj (f ∘ fmap[Arrows_Terms] g) ≈ to TA_adj f ∘ g.
Proof.
  destruct f, g, v, v0; simpl; simpl_eq; cat.
  - rewrite getArrMorph_ValidTerm_to_ValidArrow.
    rewrite getMorph_ValidArrow_to_ValidTerm.
    reflexivity.
  - rewrite getArrMorph_ValidTerm_to_ValidArrow.
    rewrite getMorph_ValidArrow_to_ValidTerm.
    reflexivity.
  - try destruct (ValidArrow_compose (_ v0_1) (_ v0_2));
    try destruct (ValidArrow_compose (_ v1) (_ v2)); simpl; cat.
  - try destruct (ValidArrow_compose (_ v0_1) (_ v0_2));
    try destruct (ValidArrow_compose (_ v1) (_ v2)); simpl; cat.
      rewrite getArrMorph_ValidTerm_to_ValidArrow.
      rewrite getMorph_ValidArrow_to_ValidTerm.
      reflexivity.
    comp_left.
    rewrite !getArrMorph_ValidArrow_compose; simpl.
    rewrite getArrMorph_ValidTerm_to_ValidArrow.
    rewrite getMorph_ValidArrow_to_ValidTerm.
    reflexivity.
Qed.

Lemma TA_to_adj_nat_r {x y c} (f : y ~> c) (g : Arrows_Terms x ~> y) :
  to TA_adj (f ∘ g) ≈ fmap[Terms_Arrows] f ∘ to TA_adj g.
Proof.
  destruct f, g, v, v0; simpl; simpl_eq; cat;
  try destruct (ValidArrow_compose (_ v0_1) (_ v0_2));
  try destruct (ValidArrow_compose (_ v1) (_ v2)); simpl; cat.
  rewrite !getArrMorph_ValidArrow_compose; simpl; cat.
Qed.

Lemma TA_from_adj_nat_l {x y c} (f : y ~> Terms_Arrows c) (g : x ~> y) :
  TA_adj⁻¹ (f ∘ g) ≈ TA_adj⁻¹ f ∘ fmap[Arrows_Terms] g.
Proof.
  destruct f, g; simpl in *; destruct v, v0; simpl;
  rewrite ?getMorph_ValidArrow_to_ValidTerm; cat.
  rewrite getArrMorph_ValidArrow_compose; cat.
Qed.

Lemma Compose_ComposeTerm f g dom mid cod t u :
  (Compose f g; ComposeTerm dom mid cod f g t u) ≈ (f; t) ∘[Terms] (g; u).
Proof.
  generalize dependent dom.
  induction t, u; simpl; intros; cat.
Qed.

Lemma cons_ComposedArrow f fs dom mid cod f' Hf u :
  (f :: fs; ComposedArrow dom mid cod f f' _ Hf u)
    ≈ ([f]; ComposedArrow _ _ _ _ _ _ Hf (IdentityArrow _)) ∘[Arrows] (fs; u).
Proof.
  generalize dependent dom.
  induction u; simpl; intros; cat.
Qed.

Lemma TA_from_adj_nat_r {x y c} (f : y ~> c) (g : x ~> Terms_Arrows y) :
  TA_adj⁻¹ (fmap[Terms_Arrows] f ∘ g) ≈ f ∘ TA_adj⁻¹ g.
Proof.
  destruct f, g.
  generalize dependent v0.
  generalize dependent x1.
  induction v; intros;
  simpl in v0; destruct v0; try solve [ simpl; cat ].
    rewrite !id_right; simpl.
    rewrite getMorph_ValidArrow_to_ValidTerm.
    rewrite getArrMorph_ValidArrow_compose.
    now rewrite !getArrMorph_ValidTerm_to_ValidArrow.
  rewrite Compose_ComposeTerm.
  rewrite cons_ComposedArrow.
  rewrite !fmap_comp.
  rewrite !TA_from_adj_nat_l.
  rewrite fmap_comp.
  rewrite !comp_assoc.
  apply Category.Terms_obligation_1; [|reflexivity].
  apply Category.Terms_obligation_1; cat.
  apply Category.Terms_obligation_1; simpl; cat;
  rewrite getMorph_ValidArrow_to_ValidTerm;
  rewrite getArrMorph_ValidTerm_to_ValidArrow;
  reflexivity.
Qed.

Program Instance Terms_Arrows_Adjunction : Arrows_Terms ⊣ Terms_Arrows := {
  adj := @TA_adj;
  to_adj_nat_l := @TA_to_adj_nat_l;
  to_adj_nat_r := @TA_to_adj_nat_r;
  from_adj_nat_l := @TA_from_adj_nat_l;
  from_adj_nat_r := @TA_from_adj_nat_r
}.

End NormalValidAdjoint.

Print Assumptions Terms_Arrows_Adjunction.
