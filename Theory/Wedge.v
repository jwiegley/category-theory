Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Opposite.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Wedge.

Context {C : Category}.
Context {D : Category}.
Context {F : C^op ∏ C ⟶ D}.

Class Wedge := {
  wedge : D;

  wedge_map {X : C} : wedge ~{D}~> F (X, X);

  ump_wedges {X Y : C} (f : X ~{C}~> Y) :
    bimap[F] id f ∘ wedge_map ≈ bimap[F] (op f) id ∘ wedge_map
}.

End Wedge.

Coercion wedge : Wedge >-> ob.

Notation "wedge_map[ C ]" := (@wedge_map _ _ _ C _)
  (at level 9, format "wedge_map[ C ]") : category_scope.
