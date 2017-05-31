Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* A Groupoid is a category where all morphisms are isomorphisms, and morphism
   equivalence is equivalence of isomorphisms. *)

Program Definition Groupoid (C : Category) : Category := {|
  ob      := @ob C;
  hom     := @Isomorphism C;
  homset  := @isomorphism_setoid C;
  id      := @iso_id C;
  compose := @iso_compose C
|}.
