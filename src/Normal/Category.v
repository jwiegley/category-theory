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
Require Import Solver.Normal.TList.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Valid.

Generalizable All Variables.

Section NormalCategory.

Context `{Env}.

Global Program Instance ArrowList_Setoid dom cod :
  Setoid (ArrowList dom cod) := {
  equiv := fun f g => getArrMorph f ≈ getArrMorph g
}.

Program Definition Arrows : Category := {|
  obj     := obj_idx;
  hom     := ArrowList;
  homset  := ArrowList_Setoid;
  id      := fun _ => tnil;
  compose := fun _ _ _ => tlist_app
|}.
Next Obligation. proper; now rewrite !getArrMorph_ArrowList_compose, X, X0. Qed.
Next Obligation. now rewrite getArrMorph_ArrowList_compose; cat. Qed.
Next Obligation. now rewrite tlist_app_assoc. Qed.
Next Obligation. symmetry; now rewrite tlist_app_assoc. Qed.

End NormalCategory.
