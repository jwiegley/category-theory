Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Cone `(F : J ⟶ C) := {
  vertex : C;
  vertex_map {X : J} : vertex ~{C}~> F X;

  ump_cones {X Y : J} (f : X ~{J}~> Y) :
    fmap[F] f ∘ @vertex_map X ≈ @vertex_map Y
}.

Coercion vertex : Cone >-> ob.

Notation "vertex_map[ C ]" := (@vertex_map _ _ _ C _)
  (at level 9, format "vertex_map[ C ]") : category_scope.

Definition Cocone `(F : J ⟶ C) := Cone (F^op).
