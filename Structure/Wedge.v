Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Wedge `(F : C^op ∏ C ⟶ D) := {
  wedge_obj : D;

  wedge_map {x : C} : wedge_obj ~{D}~> F (x, x);

  ump_wedges {x y : C} (f : x ~{C}~> y) :
    bimap[F] id f ∘ wedge_map ≈ bimap[F] (op f) id ∘ wedge_map
}.

Coercion Wedge_to_obj `(F : C^op ∏ C ⟶ D) (W : Wedge F) : D :=
  @wedge_obj _ _ _ W.

Notation "wedge_map[ C ]" := (@wedge_map _ _ _ C _)
  (at level 9, format "wedge_map[ C ]") : category_scope.

Definition Cowedge `(F : C^op ∏ C ⟶ D) := @Wedge (C^op) (D^op) (F^op).
