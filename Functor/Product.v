Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Cartesian.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance ProductFunctor `(C : Category) `{@Cartesian C} :
  C ∏ C ⟶ C := {
  fobj := fun p => Prod (fst p) (snd p);
  fmap := fun _ _ p => (fst p ∘ exl) △ (snd p ∘ exr)
}.
Next Obligation.
  proper.
  destruct x, y; simpl.
  destruct X; simpl in *.
  rewrite c, c0.
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc; cat.
Qed.
