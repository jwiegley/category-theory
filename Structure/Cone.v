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
  vertex_map {x : J} : vertex ~{C}~> F x;

  ump_cones {x y : J} (f : x ~{J}~> y) :
    fmap[F] f ∘ @vertex_map x ≈ @vertex_map y
}.

Coercion vertex : Cone >-> obj.

Notation "vertex[ C ]" := (@vertex _ _ _ C)
  (at level 9, format "vertex[ C ]") : category_scope.
Notation "vertex_map[ C ]" := (@vertex_map _ _ _ C _)
  (at level 9, format "vertex_map[ C ]") : category_scope.

Definition Cocone `(F : J ⟶ C) := Cone (F^op).
