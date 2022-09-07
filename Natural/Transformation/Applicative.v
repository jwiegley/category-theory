Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Applicative.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Balanced.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Natural.Transformation.Monoidal.

Generalizable All Variables.

Class Applicative_Transform `{@ClosedMonoidal C}
  `{@Applicative C _ F}
  `{@Applicative C _ G} (N : F ⟹ G) := {
  applicative_transform_is_strong_transformation :
    @Strong_Transform C _ F _ G _ N;
  applicative_transform_is_lax_monoidal_transformation :
    @LaxMonoidal_Transform C _ F _ G _ N
}.
#[export] Existing Instance applicative_transform_is_strong_transformation.
#[export] Existing Instance applicative_transform_is_lax_monoidal_transformation.
