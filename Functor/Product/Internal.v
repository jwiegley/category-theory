Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

#[global]
Program Instance InternalProductFunctor `(C : Category) `{@Cartesian C} :
  C ∏ C ⟶ C := {
  fobj := fun p => fst p × snd p;
  fmap := fun _ _ p => (fst p ∘ exl) △ (snd p ∘ exr)
}.
Next Obligation.
  proper.
  simpl in *.
  rewrites.
  reflexivity.
Qed.
Next Obligation.
  simpl in *.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc; cat.
Qed.

Notation "×( C )" := (@InternalProductFunctor C _)
  (at level 90, format "×( C )") : functor_scope.
