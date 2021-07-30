Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Functor.Applicative.
Require Export Category.Structure.Monoidal.Internal.Product.
Require Export Category.Natural.Transformation.Strong.
Require Export Category.Natural.Transformation.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Applicative_Transform {C : Category}
      `{@Cartesian C} `{@Terminal C} `{@Closed C _}
      {F : C ⟶ C} `{@Applicative _ _ _ _ F}
      {G : C ⟶ C} `{@Applicative _ _ _ _ G} (N : F ⟹ G) := {
  is_strong_transformation :>
    @Strong_Transform C InternalProduct_Monoidal _ _ _ _ N;
  is_lax_monoidal_transformation :>
    @LaxMonoidal_Transform C InternalProduct_Monoidal _ _ _ _ N
}.
