Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(** * Commutative comonoids in a symmetric monoidal category

    The dual of [CommutativeMonoid]: a [Comonoid X] over a
    [SymmetricMonoidal] category is COCOMMUTATIVE when its
    comultiplication is invariant under post-composition with the
    braiding:

      σ ∘ δ ≈ δ

    Provided independently of [CommutativeFrobenius] so that an
    object can carry a cocommutative-comonoid structure WITHOUT being
    forced to also carry a multiplication.  Downstream callers that
    want to model "duplicate a tensor wire" (the canonical δ on a
    hypergraph object) without committing to a corresponding fan-in
    operation use this directly. *)

Section CommutativeComonoid.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeComonoid (X : C) : Type := {
  ccomon_comonoid : @Comonoid C
                      (@braided_is_monoidal C
                         (@symmetric_is_braided C S))
                      X;

  delta_cocommutative_of_ccomon :
    braid ∘ (@delta _ _ _ ccomon_comonoid)
      ≈ (@delta _ _ _ ccomon_comonoid)
}.

#[export] Existing Instance ccomon_comonoid.

Coercion ccomon_comonoid : CommutativeComonoid >-> Comonoid.

End CommutativeComonoid.

Arguments ccomon_comonoid {C S X _}.
Arguments delta_cocommutative_of_ccomon {C S X _}.

(** Convenience flat-projection aliases mirroring [scfa_delta] /
    [scfa_epsilon] from [SpecialCommutativeFrobenius.v]: project a
    [CommutativeComonoid X] to its underlying [delta] / [epsilon]. *)

Section CommutativeComonoidProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition ccomon_delta {X : C} (M : CommutativeComonoid X)
  : X ~> (X ⨂ X)%object :=
  @delta _ _ _ (ccomon_comonoid (X := X)).

Definition ccomon_epsilon {X : C} (M : CommutativeComonoid X)
  : X ~> @I _ _ :=
  @epsilon _ _ _ (ccomon_comonoid (X := X)).

End CommutativeComonoidProjections.

Arguments ccomon_delta   {C S X} M.
Arguments ccomon_epsilon {C S X} M.
