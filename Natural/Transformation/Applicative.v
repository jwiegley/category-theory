Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Applicative.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Natural.Transformation.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Applicative_Transform {C : Category}
      `{@Cartesian C} `{@Terminal C} `{@Closed C _}
      {F : C ⟶ C} `{@Applicative _ _ _ _ F}
      {G : C ⟶ C} `{@Applicative _ _ _ _ G} (N : F ⟹ G) := {
  applicative_transform_is_strong_transformation :
    @Strong_Transform C InternalProduct_Monoidal _ _ _ _ N;
  applicative_transform_is_lax_monoidal_transformation :
    @LaxMonoidal_Transform C InternalProduct_Monoidal _ _ _ _ N
}.
#[export] Existing Instance applicative_transform_is_strong_transformation.
#[export] Existing Instance applicative_transform_is_lax_monoidal_transformation.
