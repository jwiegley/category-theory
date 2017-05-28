Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Bicartesian.
Require Export Category.Structure.Closed.
Require Export Category.Structure.Distributive.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import EqNotations.

(* A discrete category has no arrows except for identity morphisms. *)

Definition Discrete (C : Category) :=
  ∀ X Y (f : X ~> Y), { H : X = Y & f ≈ rew H in id }.
