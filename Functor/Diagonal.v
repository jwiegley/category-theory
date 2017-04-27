Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Instance Diagonal `(C : Category) : C ⟶ C ∏ C := {
  fobj := fun x => (x, x);
  fmap := fun _ _ f => (f, f)
}.

Notation "Δ( C )" := (@Diagonal C) (at level 90).
