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

Global Program Instance ValidArrowEx_Setoid dom cod :
  Setoid (ValidArrowEx dom cod) := {
  equiv := fun f g => getArrMorph `2 f ≈ getArrMorph `2 g
}.

Equations ValidArrowEx_compose {dom mid cod}
          (f : ValidArrowEx mid cod)
          (g : ValidArrowEx dom mid) : ValidArrowEx dom cod :=
  ValidArrowEx_compose (existT IdentityArrow) g := g;
  ValidArrowEx_compose f (existT IdentityArrow) := f;
  ValidArrowEx_compose (existT (ComposedArrow f g)) (existT h) :=
    (_; ComposedArrow _ _ _ _ _ _ f (ValidArrow_compose g h)).

Lemma getArrMorph_ValidArrowEx_compose {dom mid cod} f g :
  getArrMorph `2 (ValidArrowEx_compose f g)
    ≈ getArrMorph (cod:=cod) `2 f ∘
      getArrMorph (dom:=dom) (cod:=mid) `2 g.
Proof.
  destruct f, g, v, v0;
  repeat first
    [ rewrite ValidArrowEx_compose_equation_1
    | rewrite ValidArrowEx_compose_equation_2
    | rewrite ValidArrowEx_compose_equation_3 ]; cat.
  simpl; rewrite getArrMorph_ValidArrow_compose; cat.
Qed.

Lemma ValidArrowEx_compose_assoc {x y z w : obj_idx}
      `(f : ValidArrowEx z w) 
      `(g : ValidArrowEx y z)
      `(h : ValidArrowEx x y) :
  getArrMorph `2 (ValidArrowEx_compose f (ValidArrowEx_compose g h)) ≈
  getArrMorph `2 (ValidArrowEx_compose (ValidArrowEx_compose f g) h).
Proof.
  destruct f, g, h, v, v0, v1;
  repeat first
    [ rewrite ValidTermEx_compose_equation_1
    | rewrite ValidTermEx_compose_equation_2
    | rewrite ValidTermEx_compose_equation_3 ]; simpl; cat.
  do 2 rewrite !getArrMorph_equation_2, !getArrMorph_ValidArrow_compose; cat.
Qed.

Program Definition Arrows : Category := {|
  obj     := obj_idx;
  hom     := ValidArrowEx;
  homset  := ValidArrowEx_Setoid;
  id      := fun dom => ([]; IdentityArrow dom);
  compose := fun _ _ _ => ValidArrowEx_compose
|}.
Next Obligation. proper; now rewrite !getArrMorph_ValidArrowEx_compose, X, X0. Qed.
Next Obligation. rewrite getArrMorph_ValidArrowEx_compose; cat. Qed.
Next Obligation. apply ValidArrowEx_compose_assoc. Qed.
Next Obligation. symmetry; apply ValidArrowEx_compose_assoc. Qed.

End NormalCategory.
