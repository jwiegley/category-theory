Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Functor.Opposite.
Require Import Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* A C-valued presheaf on some category U.
  C is often taken to be Sets. *)
Definition Presheaf (U C : Category) := U^op ⟶ C.

(* The category of C-valued presheaves presheaves on a category U. *)
Definition Presheaves {U C : Category} := [U^op, C].

Definition Copresheaf (U C : Category) := U ⟶ C.

Definition Copresheaves {U C : Category} := [U, C].
