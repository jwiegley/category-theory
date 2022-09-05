Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition EilenbergMoore `(T : C ⟶ C) `{@Monad C T} : Category := {|
  obj     := ∃ a : C, TAlgebra T a;
  hom     := fun x y => TAlgebraHom T ``x ``y (projT2 x) (projT2 y);
  homset  := fun _ _ => {| equiv := fun f g => t_alg_hom[f] ≈ t_alg_hom[g] |};
  id      := fun _ => {| t_alg_hom := id |};
  compose := fun _ _ _ f g => {| t_alg_hom := t_alg_hom[f] ∘ t_alg_hom[g] |}
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- t_alg_hom_commutes.
  rewrite <- !comp_assoc.
  rewrite <- t_alg_hom_commutes.
  reflexivity.
Qed.
