Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Applicative.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Applicative_Transform {C : Category}
      `{@Cartesian C} `{@Terminal C} `{@Closed C _}
      {F : C ⟶ C} `{@Applicative _ _ _ _ F}
      {G : C ⟶ C} `{@Applicative _ _ _ _ G} (N : F ⟹ G) := {
  is_strong_transformation :>
    @StrongTransformation C InternalProduct_Monoidal _ _ _ _ N;
  is_lax_monoidal_transformation :>
    @LaxMonoidalTransformation C InternalProduct_Monoidal _ _ _ _ N
}.
