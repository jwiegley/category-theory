Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Strong.
Require Export Category.Functor.Hom.Internal.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Closed.
Require Export Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* An "applicative" functor is a strong lax monoidal functor in a cartesian
   closed category with terminal objects, whose monoidal structure is given by
   the internal product. This is indicated because we are "applying" mapped
   internal homs, thus closed and cartesian. Terminality is required to make
   the internal product monoidal (since the terminal object provides unit).
   This also makes the category cartesian monoidal. *)

Section ApplicativeFunctor.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context `{@Closed C _}.
Context {F : C ⟶ C}.

Class Applicative := {
  in_monoidal := @InternalProduct_Monoidal C _ _;
  is_strong :> @StrongFunctor C in_monoidal F;
  is_lax_monoidal :> LaxMonoidalFunctor F;

  ap {X Y} : F (X ≈> Y) ⨂ F X ~> F Y :=
    fmap[F] eval ∘ @lax_ap _ _ in_monoidal _ F _ (X ≈> Y) X
}.

End ApplicativeFunctor.

Arguments pure {C _ F _ _ A}.

Notation "pure[ F ]" := (@pure _ InternalProduct_Monoidal F _ _ _)
  (at level 9, format "pure[ F ]") : morphism_scope.
