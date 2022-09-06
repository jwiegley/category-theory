Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This structure represents "embedded constants", by way of an object that is
   able to host foreign values of a given Coq type. *)

Class Constant `{@Terminal C} (A : Type) := {
  constant_obj : A → C;
  constant (x : A) : 1 ~> constant_obj x
}.

Arguments constant_obj {_ _} A {_}.
