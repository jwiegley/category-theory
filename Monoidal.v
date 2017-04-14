Require Import Lib.
Require Export Adjunction.
Require Export Closed.
Require Export Bifunctor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Monoidal.

Context `{C : Category}.

Class Monoidal := {
  tensor : C × C ⟶ C
}.