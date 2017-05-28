Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Constant.

Context {C : Category}.
Context `{@Terminal C}.

(* This structure represents "embedded constants", by way of an object that is
   able to host foreign values of a given Coq type. *)

Class Constant (A : Type) := {
  Const : A -> ob;
  constant (x : A) : One ~{C}~> Const x
}.

End Constant.

Arguments Const {_ _} A {_}.
