Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Internal comonoids in a monoidal category

    The dual of [Monoid]: a comonoid on [X : C] is a comultiplication
    [delta : X ~> X ⨂ X] and a counit [epsilon : X ~> I] satisfying the
    obvious dual associativity and unit laws.

    In principle [Comonoid X] could be obtained as [@Monoid (C^op) _ X], but
    defining a [Monoidal] instance on [C^op] requires extra machinery (the
    tensor reverses and the unit/associator flip), and the resulting class
    members would need to be re-unfolded everywhere.  Following the practice
    elsewhere in this library (cf. [Cocartesian], [Initial]) we instead state
    the dual class directly. *)

Section Comonoid.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Comonoid (X : C) : Type := {
  delta   : X ~> X ⨂ X;
  epsilon : X ~> I;

  delta_coassoc :
    bimap delta id[X] ∘ delta
      ≈ from (@tensor_assoc C M X X X) ∘ bimap id[X] delta ∘ delta;

  delta_counit_left :
    bimap epsilon id[X] ∘ delta
      ≈ from (@unit_left C M X);

  delta_counit_right :
    bimap id[X] epsilon ∘ delta
      ≈ from (@unit_right C M X)
}.

End Comonoid.

Arguments delta   {C M X _}.
Arguments epsilon {C M X _}.

Notation "'delta[' Co ]"   := (@delta _ _ _ Co)
  (at level 9, format "'delta[' Co ]") : morphism_scope.
Notation "'epsilon[' Co ]" := (@epsilon _ _ _ Co)
  (at level 9, format "'epsilon[' Co ]") : morphism_scope.
