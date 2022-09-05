Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Hom.Internal.
Require Export Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
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
  applicative_is_monoidal := @InternalProduct_Monoidal C _ _;
  applicative_is_strong : @StrongFunctor C applicative_is_monoidal F;
  applicative_is_lax_monoidal : LaxMonoidalFunctor F;

  ap {x y} : F (x ≈> y) ⨂ F x ~> F y :=
    fmap[F] eval ∘ @lax_ap _ _ applicative_is_monoidal _ F _ (x ≈> y) x
}.
#[export] Existing Instance applicative_is_strong.
#[export] Existing Instance applicative_is_lax_monoidal.

End ApplicativeFunctor.

Arguments pure {C _ F _ _ A}.

Notation "pure[ F ]" := (@pure _ InternalProduct_Monoidal F _ _ _)
  (at level 9, format "pure[ F ]") : morphism_scope.
