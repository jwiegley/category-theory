Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Functor.Op.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Wedge `(F : C^op ∏ C ⟶ D) := {
  wedge : D;

  wedge_map {X : C} : wedge ~{D}~> F (X, X);

  ump_wedges {X Y : C} (f : X ~{C}~> Y) :
    bimap[F] id f ∘ wedge_map ≈ bimap[F] (op f) id ∘ wedge_map
}.

Coercion wedge : Wedge >-> ob.

Notation "wedge_map[ C ]" := (@wedge_map _ _ _ C _)
  (at level 9, format "wedge_map[ C ]") : category_scope.

(* jww (2017-05-22): TODO
Definition Cowedge `(F : C^op ∏ C ⟶ D) := Wedge (F^op).
*)
