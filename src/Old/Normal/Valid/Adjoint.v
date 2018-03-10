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
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.
Require Import Solver.Normal.TList.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.
Require Import Solver.Normal.Sound.
Require Import Solver.Normal.Valid.
Require Import Solver.Normal.Valid.Sound.
Require Import Solver.Normal.Category.

Generalizable All Variables.

Section NormalValidAdjoint.

Context `{Env}.

Program Instance Terms_Arrows : Terms ⟶ Arrows := {
  fobj := fun x => x;
  fmap := fun x y => arrows
}.

Program Instance Arrows_Terms : Arrows ⟶ Terms := {
  fobj := fun x => x;
  fmap := fun x y => unarrows
}.
Next Obligation.
Admitted.

(*
Corollary weaken_eq {A : Type} `{Setoid A} {a b : A} : a = b -> a ≈ b.
Proof. intros; subst; reflexivity. Qed.

Program Instance DefinedTerms_DefinedArrows : DefinedTerms ⟶ DefinedArrows := {
  fobj := fun x => x;
  fmap := fun x y '(f; (f'; Hf)) =>
    let '(t; (_, Ht)) := arrowsD_sound_r Hf in
    (arrows f; (t; weaken_eq Ht))
}.
Next Obligation.
  proper.
  simpl in *.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Instance DefinedArrows_DefinedTerms : DefinedArrows ⟶ DefinedTerms := {
  fobj := fun x => x;
  fmap := fun x y '(f; (f'; Hf)) =>
    let '(t; (_, Ht)) := @arrowsD_sound _ _ x y _ _ in
    (_; (_; Ht))
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
*)

(*
Definition TA_adj {x y} : Arrows_Terms x ~> y ≊ x ~> Terms_Arrows y.
Proof.
  isomorphism; simpl.
  - morphism; intros.
    + destruct X.
      exact (arrows x0; ValidTerm_to_ArrowList v).
    + proper.
      destruct x0, y0; simpl in *.
      now rewrite !getArrMorph_ValidTerm_to_ArrowList.
  - morphism; intros.
    + destruct X.
      exact (unarrows x0; ArrowList_to_ValidTerm v).
    + proper.
      destruct x0, y0; simpl in *.
      now rewrite !getMorph_ArrowList_to_ValidTerm.
  - destruct x0; simpl.
    rewrite getArrMorph_ValidTerm_to_ArrowList.
    rewrite getMorph_ArrowList_to_ValidTerm.
    reflexivity.
  - destruct x0; simpl.
    rewrite getMorph_ArrowList_to_ValidTerm.
    rewrite getArrMorph_ValidTerm_to_ArrowList.
    reflexivity.
Defined.

Lemma TA_to_adj_nat_l {x y c} (f : Arrows_Terms y ~> c) (g : x ~> y) :
  to TA_adj (f ∘ fmap[Arrows_Terms] g) ≈ to TA_adj f ∘ g.
Proof.
  destruct f, g, v, v0; simpl; simpl_eq; cat.
  - rewrite getArrMorph_ValidTerm_to_ArrowList.
    rewrite getMorph_ArrowList_to_ValidTerm.
    reflexivity.
  - rewrite getArrMorph_ValidTerm_to_ArrowList.
    rewrite getMorph_ArrowList_to_ValidTerm.
    reflexivity.
  - try destruct (ArrowList_compose (_ v0_1) (_ v0_2));
    try destruct (ArrowList_compose (_ v1) (_ v2)); simpl; cat.
  - try destruct (ArrowList_compose (_ v0_1) (_ v0_2));
    try destruct (ArrowList_compose (_ v1) (_ v2)); simpl; cat.
      rewrite getArrMorph_ValidTerm_to_ArrowList.
      rewrite getMorph_ArrowList_to_ValidTerm.
      reflexivity.
    comp_left.
    rewrite !getArrMorph_ArrowList_compose; simpl.
    rewrite getArrMorph_ValidTerm_to_ArrowList.
    rewrite getMorph_ArrowList_to_ValidTerm.
    reflexivity.
Qed.

Lemma TA_to_adj_nat_r {x y c} (f : y ~> c) (g : Arrows_Terms x ~> y) :
  to TA_adj (f ∘ g) ≈ fmap[Terms_Arrows] f ∘ to TA_adj g.
Proof.
  destruct f, g, v, v0; simpl; simpl_eq; cat;
  try destruct (ArrowList_compose (_ v0_1) (_ v0_2));
  try destruct (ArrowList_compose (_ v1) (_ v2)); simpl; cat.
  rewrite !getArrMorph_ArrowList_compose; simpl; cat.
Qed.

Lemma TA_from_adj_nat_l {x y c} (f : y ~> Terms_Arrows c) (g : x ~> y) :
  TA_adj⁻¹ (f ∘ g) ≈ TA_adj⁻¹ f ∘ fmap[Arrows_Terms] g.
Proof.
  destruct f, g; simpl in *; destruct v, v0; simpl;
  rewrite ?getMorph_ArrowList_to_ValidTerm; cat.
  rewrite getArrMorph_ArrowList_compose; cat.
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
    rewrite getMorph_ArrowList_to_ValidTerm.
    rewrite getArrMorph_ArrowList_compose.
    now rewrite !getArrMorph_ValidTerm_to_ArrowList.
  rewrite Compose_ComposeTerm.
  rewrite cons_ComposedArrow.
  rewrite !fmap_comp.
  rewrite !TA_from_adj_nat_l.
  rewrite fmap_comp.
  rewrite !comp_assoc.
  apply Category.Terms_obligation_1; [|reflexivity].
  apply Category.Terms_obligation_1; cat.
  apply Category.Terms_obligation_1; simpl; cat;
  rewrite getMorph_ArrowList_to_ValidTerm;
  rewrite getArrMorph_ValidTerm_to_ArrowList;
  reflexivity.
Qed.

Program Instance Terms_Arrows_Adjunction : Arrows_Terms ⊣ Terms_Arrows := {
  adj := @TA_adj;
  to_adj_nat_l := @TA_to_adj_nat_l;
  to_adj_nat_r := @TA_to_adj_nat_r;
  from_adj_nat_l := @TA_from_adj_nat_l;
  from_adj_nat_r := @TA_from_adj_nat_r
}.
*)

End NormalValidAdjoint.

(* Print Assumptions Terms_Arrows_Adjunction. *)
