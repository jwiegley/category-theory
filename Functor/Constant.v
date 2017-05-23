Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Constant `(C : Category) {D : Category} (d : D) :
  C ⟶ D := {|
  fobj := fun _ => d;
  fmap := fun _ _ _ => id[d]
|}.
