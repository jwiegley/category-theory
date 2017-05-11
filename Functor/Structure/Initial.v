Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Initial.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section InitialFunctor.

Context `{F : C ⟶ D}.
Context `{@Initial C}.
Context `{@Initial D}.

Class InitialFunctor := {
  map_zero : F Zero ~> Zero;

  fmap_zero {X : C} :
    fmap[F] zero ≈ @zero _ _ (F X) ∘ map_zero
}.

End InitialFunctor.
