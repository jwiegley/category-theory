Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class LaxMonoidal_Transform {C : Category} `{@Monoidal C}
      {F : C ⟶ C} `{@LaxMonoidalFunctor _ _ _ _ F}
      {G : C ⟶ C} `{@LaxMonoidalFunctor _ _ _ _ G} (N : F ⟹ G) := {
  lax_pure_transform : lax_pure[G] ≈ transform[N] _ ∘ lax_pure[F];

  lax_ap_transform {x y} :
    lax_ap[G] ∘ transform[N] x ⨂ transform[N] y ≈ transform[N] _ ∘ lax_ap[F]
}.
