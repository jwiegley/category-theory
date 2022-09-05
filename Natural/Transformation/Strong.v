Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Strong.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Strong_Transform {C : Category} `{@Monoidal C}
      {F : C ⟶ C} `{@StrongFunctor _ _ F}
      {G : C ⟶ C} `{@StrongFunctor _ _ G} (N : F ⟹ G) := {
  strength_transform {x y} :
    strength[G] ∘ id[x] ⨂ transform[N] y ≈ transform[N] _ ∘ strength[F]
}.
