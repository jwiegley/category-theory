Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Functor.Structure.Monoidal.

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
