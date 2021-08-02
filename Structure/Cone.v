Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Cone `(F : J ⟶ C) := {
  vertex_obj : C;
  vertex_map {x : J} : vertex_obj ~{C}~> F x;

  ump_cones {x y : J} (f : x ~{J}~> y) :
    fmap[F] f ∘ @vertex_map x ≈ @vertex_map y
}.

Coercion vertex_obj : Cone >-> obj.

Notation "vertex_obj[ C ]" := (@vertex_obj _ _ _ C)
  (at level 9, format "vertex_obj[ C ]") : category_scope.
Notation "vertex_map[ C ]" := (@vertex_map _ _ _ C _)
  (at level 9, format "vertex_map[ C ]") : category_scope.

Notation "Cone[ N ] F" := { ψ : Cone F | vertex_obj[ψ] = N }
  (at level 9, format "Cone[ N ] F") : category_scope.

Definition Cocone `(F : J ⟶ C) := Cone (F^op).
