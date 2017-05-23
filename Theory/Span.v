Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Opposite.
Require Export Category.Instance.Roof.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Span {C : Category} := Roof ⟶ C.

Definition Cospan {C : Category} := Roof ⟶ C^op.
