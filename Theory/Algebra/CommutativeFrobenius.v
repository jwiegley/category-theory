Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.

Generalizable All Variables.

(** * Commutative Frobenius algebras in a symmetric monoidal category

    A Frobenius algebra is commutative when its multiplication is symmetric
    under the braiding, and equivalently when its comultiplication is
    symmetric.  In a symmetric monoidal category these are equivalent
    statements; we record both because they are both useful as rewrite
    rules. *)

Section CommutativeFrobenius.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CommutativeFrobenius (X : C) : Type := {
  cfrob_frobenius : @Frobenius C _ X;

  mu_commutative :
    (@mu _ _ _ (@frob_monoid _ _ _ cfrob_frobenius)) ∘ braid
      ≈ (@mu _ _ _ (@frob_monoid _ _ _ cfrob_frobenius));

  delta_cocommutative :
    braid ∘ (@delta _ _ _ (@frob_comonoid _ _ _ cfrob_frobenius))
      ≈ (@delta _ _ _ (@frob_comonoid _ _ _ cfrob_frobenius))
}.
#[export] Existing Instance cfrob_frobenius.

Coercion cfrob_frobenius : CommutativeFrobenius >-> Frobenius.

End CommutativeFrobenius.

Arguments cfrob_frobenius {C S X _}.
