Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Constant.

Context `{C : Category}.
Context `{@Terminal C}.

Class Constant (A : Type) := {
  Const : ob;
  constant (x : A) : One ~{C}~> Const
}.

End Constant.

Arguments Const {_ _} A {_}.
