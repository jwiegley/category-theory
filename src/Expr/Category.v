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
Require Import Solver.Expr.Valid.

Generalizable All Variables.

Section ExprCategory.

Context `{Env}.

Definition ValidTermEx dom cod := ∃ f, ValidTerm dom cod f.

Global Program Instance ValidTermEx_Setoid dom cod :
  Setoid (ValidTermEx dom cod) := {
  equiv := fun f g => getMorph `2 f ≈ getMorph `2 g
}.

Equations ValidTermEx_compose {dom mid cod}
          (f : ValidTermEx mid cod)
          (g : ValidTermEx dom mid) : ValidTermEx dom cod :=
  ValidTermEx_compose (existT IdentityTerm) g := g;
  ValidTermEx_compose f (existT IdentityTerm) := f;
  ValidTermEx_compose f g := (_; ComposeTerm _ _ _ _ _ `2 f `2 g).

Lemma getMorph_ValidTermEx_compose {dom mid cod} f g :
  getMorph `2 (ValidTermEx_compose f g)
    ≈ getMorph (cod:=cod) `2 f ∘
      getMorph (dom:=dom) (cod:=mid) `2 g.
Proof.
  destruct f, g, v, v0;
  repeat first
    [ rewrite ValidTermEx_compose_equation_1
    | rewrite ValidTermEx_compose_equation_2
    | rewrite ValidTermEx_compose_equation_3
    | rewrite ValidTermEx_compose_equation_4
    | rewrite ValidTermEx_compose_equation_5
    | rewrite ValidTermEx_compose_equation_6
    | rewrite ValidTermEx_compose_equation_7 ]; cat.
Qed.

Lemma ValidTermEx_compose_assoc {x y z w : obj_idx}
      (f : ValidTermEx z w) 
      (g : ValidTermEx y z)
      (h : ValidTermEx x y) :
  getMorph `2 (ValidTermEx_compose f (ValidTermEx_compose g h)) ≈
  getMorph `2 (ValidTermEx_compose (ValidTermEx_compose f g) h).
Proof.
  destruct f, g, h, v, v0, v1;
  repeat first
    [ rewrite ValidTermEx_compose_equation_1
    | rewrite ValidTermEx_compose_equation_2
    | rewrite ValidTermEx_compose_equation_3
    | rewrite ValidTermEx_compose_equation_4
    | rewrite ValidTermEx_compose_equation_5
    | rewrite ValidTermEx_compose_equation_6
    | rewrite ValidTermEx_compose_equation_7 ]; simpl; cat.
Qed.

Program Definition Terms : Category := {|
  obj     := obj_idx;
  hom     := ValidTermEx;
  homset  := ValidTermEx_Setoid;
  id      := fun dom => (Identity; IdentityTerm dom);
  compose := fun _ _ _ => ValidTermEx_compose
|}.
Next Obligation.
  proper; rewrite !getMorph_ValidTermEx_compose, X, X0; reflexivity.
Defined.
Next Obligation. rewrite getMorph_ValidTermEx_compose; cat. Qed.
Next Obligation. apply ValidTermEx_compose_assoc. Qed.
Next Obligation. symmetry; apply ValidTermEx_compose_assoc. Qed.

End ExprCategory.
