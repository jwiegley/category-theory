Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This structure represents "embedded constants", by way of an object that is
   able to host foreign values of a given Coq type. *)

Class Constant `{@Terminal C} (A : Type) := {
  constant_obj : A -> C;
  constant (x : A) : 1 ~> constant_obj x
}.

Arguments constant_obj {_ _} A {_}.
