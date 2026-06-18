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

(** * Commutative monoids in a symmetric monoidal category *)

(* A commutative monoid in [(C, ⨂, I, σ)] is a [Monoid X] whose
   multiplication is invariant under the braiding.  This is the
   "commutative monoid" / "abelian monoid" of the symmetric-monoidal
   setting.

   In this library's notation, with [braid : X ⨂ X ~> X ⨂ X] the
   symmetry of the inputs, the commutativity law reads

       mu ∘ braid ≈ mu              (commutativity of the multiplication)

   This is the categorical version of [a * b = b * a]: precomposing
   the multiplication with the swap of its two arguments leaves it
   unchanged.  Stated for a braiding it makes sense in any braided
   monoidal category; here we work in the symmetric setting, where the
   braiding is additionally involutive ([braid ∘ braid ≈ id]).

   nLab:      https://ncatlab.org/nlab/show/commutative+monoid
   nLab:      https://ncatlab.org/nlab/show/braided+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   This class is provided independently of [Frobenius] / [Comonoid] so
   that an object can carry a commutative monoid structure WITHOUT
   being forced to also carry a comultiplication.  Downstream callers
   that want to model element-wise multiplication of tensor values
   (where there is no natural co-multiplication) use this directly. *)

Section CommutativeMonoid.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeMonoid (X : C) : Type := {
  (* underlying monoid object, taken in the monoidal category
     underlying the symmetric structure [S] *)
  cmon_monoid : @Monoid C
                  (@braided_is_monoidal C
                     (@symmetric_is_braided C S))
                  X;

  (* multiplication is invariant under the braiding: [mu ∘ braid ≈ mu] *)
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
