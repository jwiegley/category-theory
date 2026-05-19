Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.

Generalizable All Variables.

(** * Commutative monoids in a symmetric monoidal category

    A commutative monoid in [(C, ⨂, I, σ)] is a [Monoid X] whose
    multiplication satisfies [μ ∘ σ ≈ μ], i.e. is invariant under the
    braiding.  This is the "commutative monoid" / "abelian monoid" of
    the symmetric-monoidal setting.

    This class is provided independently of [Frobenius] / [Comonoid] so
    that an object can carry a commutative monoid structure WITHOUT
    being forced to also carry a comultiplication.  Downstream callers
    that want to model element-wise multiplication of tensor values
    (where there is no natural co-multiplication) use this directly. *)

Section CommutativeMonoid.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeMonoid (X : C) : Type := {
  cmon_monoid : @Monoid C
                  (@braided_is_monoidal C
                     (@symmetric_is_braided C S))
                  X;

  mu_commutative_of_cmon :
    (@mu _ _ _ cmon_monoid) ∘ braid
      ≈ (@mu _ _ _ cmon_monoid)
}.

#[export] Existing Instance cmon_monoid.

Coercion cmon_monoid : CommutativeMonoid >-> Monoid.

End CommutativeMonoid.

Arguments cmon_monoid {C S X _}.
Arguments mu_commutative_of_cmon {C S X _}.

(** Convenience aliases mirroring [scfa_mu] / [scfa_eta] from
    [SpecialCommutativeFrobenius.v]: project a [CommutativeMonoid X] to
    its underlying [mu] / [eta]. *)

Section CommutativeMonoidProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition cmon_mu {X : C} (M : CommutativeMonoid X)
  : X ⨂ X ~> X :=
  @mu _ _ _ (cmon_monoid (X := X)).

Definition cmon_eta {X : C} (M : CommutativeMonoid X)
  : I ~> X :=
  @eta _ _ _ (cmon_monoid (X := X)).

End CommutativeMonoidProjections.

Arguments cmon_mu  {C S X} M.
Arguments cmon_eta {C S X} M.
