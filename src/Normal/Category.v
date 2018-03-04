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
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Valid.

Generalizable All Variables.

Section NormalCategory.

Context `{Env}.

Definition ValidArrowEx dom cod := ∃ fs, ValidArrow dom cod fs.

Global Program Instance ValidArrow_Setoid dom cod :
  Setoid (ValidArrowEx dom cod) := {
  equiv := fun f g => getArrMorph `2 f ≈ getArrMorph `2 g
}.

Lemma ValidArrowEx_getArrList_equiv {dom cod} (f g : ValidArrowEx dom cod) :
  getArrList `2 f = getArrList `2 g -> f ≈ g.
Proof.
  destruct f, g; simpl in *; intros; subst.
  generalize dependent x0.
  induction v; intros; dependent destruction v0.
    rewrite getArrMorph_equation_1; cat.
  rewrite !getArrMorph_equation_2; cat.
  rewrite e in e0.
  inversion e0; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Pos.eq_dec].
  apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Pos.eq_dec].
  subst.
  comp_left.
  apply ValidArrow_eq_equiv.
Qed.

Equations ValidArrowEx_compose {dom mid cod}
          (f : ValidArrowEx mid cod)
          (g : ValidArrowEx dom mid) : ValidArrowEx dom cod :=
  ValidArrowEx_compose (existT IdentityArrow) g := g;
  ValidArrowEx_compose f (existT IdentityArrow) := f;
  ValidArrowEx_compose (existT (ComposedArrow f g)) (existT h) :=
    (_; ComposedArrow _ _ _ _ _ _ f (ValidArrow_app g h)).

Lemma getArrMorph_ValidArrowEx_compose {dom mid cod bs cs} f g :
  getArrMorph `2 (ValidArrowEx_compose (bs; f) (cs; g))
    ≈ getArrMorph (cod:=cod) f ∘
      getArrMorph (dom:=dom) (cod:=mid) g.
Proof.
  destruct g.
  - destruct f.
    + rewrite ValidArrowEx_compose_equation_1; cat.
    + rewrite ValidArrowEx_compose_equation_2; cat.
  - destruct f.
    + rewrite ValidArrowEx_compose_equation_1; cat.
    + rewrite ValidArrowEx_compose_equation_3; cat.
      rewrite !getArrMorph_equation_2.
      rewrite getArrMorph_ValidArrow_comp; cat.
Qed.

Lemma ValidArrowEx_compose_assoc {x y z w : obj_idx}
      `(f : ValidArrow z w fs) 
      `(g : ValidArrow y z gs)
      `(h : ValidArrow x y hs) :
  getArrMorph `2
    (ValidArrowEx_compose (fs; f) (ValidArrowEx_compose (gs; g) (hs; h))) ≈
  getArrMorph `2
    (ValidArrowEx_compose (ValidArrowEx_compose (fs; f) (gs; g)) (hs; h)).
Proof.
  destruct h; intros.
  - destruct g.
    + rewrite ValidArrowEx_compose_equation_1; cat.
      destruct f.
      * rewrite ValidArrowEx_compose_equation_1; cat.
      * rewrite ValidArrowEx_compose_equation_2; cat.
    + rewrite ValidArrowEx_compose_equation_2; cat.
      destruct f.
      * rewrite ValidArrowEx_compose_equation_1; cat.
      * rewrite ValidArrowEx_compose_equation_3; cat.
  - destruct g.
    + rewrite ValidArrowEx_compose_equation_1; cat.
      destruct f.
      * rewrite ValidArrowEx_compose_equation_1; cat.
      * rewrite ValidArrowEx_compose_equation_2; cat.
    + rewrite ValidArrowEx_compose_equation_3; cat.
      destruct f.
      * rewrite ValidArrowEx_compose_equation_1; cat.
      * rewrite ValidArrowEx_compose_equation_3; cat.
        rewrite !ValidArrowEx_compose_equation_3.
        rewrite !getArrMorph_equation_2.
        comp_left.
        rewrite !getArrMorph_ValidArrow_comp.
        comp_left.
        rewrite !getArrMorph_equation_2.
        rewrite !getArrMorph_ValidArrow_comp.
        rewrite !getArrMorph_equation_2.
        cat.
Qed.

Program Definition Arrows : Category := {|
  obj     := obj_idx;
  hom     := fun dom cod => ∃ xs, ValidArrow dom cod xs;
  homset  := ValidArrow_Setoid;
  id      := fun dom => ([]; IdentityArrow dom);
  compose := fun _ _ _ => ValidArrowEx_compose
|}.
Next Obligation. proper; now rewrite !getArrMorph_ValidArrowEx_compose, X, X0. Qed.
Next Obligation. rewrite getArrMorph_ValidArrowEx_compose; cat. Qed.
Next Obligation. apply ValidArrowEx_compose_assoc. Qed.
Next Obligation. symmetry; apply ValidArrowEx_compose_assoc. Qed.

End NormalCategory.
