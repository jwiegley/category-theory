Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import EqNotations.

(* A discrete category has no arrows except for identity morphisms. *)

Definition Discrete (C : Category) :=
  (* jww (2017-06-02): Equality is too much here. *)
  ∀ x y (f : x ~> y), ∃ H : x = y, f ≈ rew H in id.
