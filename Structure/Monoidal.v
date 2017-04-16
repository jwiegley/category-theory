Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Closed.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Monoidal.

Context `{C : Category}.

Class Monoidal := {
  tensor : C × C ⟶ C
}.