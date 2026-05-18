Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(** * Frobenius algebras in a monoidal category

    A Frobenius algebra on [X] is a monoid [(X, mu, eta)] and a comonoid
    [(X, delta, epsilon)] on the same object, satisfying the Frobenius
    compatibility law:

        (id ⨂ mu) ∘ (delta ⨂ id) ≈ delta ∘ mu ≈ (mu ⨂ id) ∘ (id ⨂ delta)

    (up to suitable insertions of the tensor associator).  This is sometimes
    written as "the unique Frobenius condition" — both equalities together
    encode that [delta] is a bimodule map.

    To keep the statement first-order in the tensor associator (rather than
    awkward two-sided compositions) we follow the standard nLab convention
    and rephrase as

        (mu ⨂ id) ∘ α⁻¹ ∘ (id ⨂ delta) ≈ delta ∘ mu

    and dually

        (id ⨂ mu) ∘ α ∘ (delta ⨂ id) ≈ delta ∘ mu.

    Together these two axioms recover the standard double Frobenius equation. *)

Section Frobenius.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Frobenius (X : C) : Type := {
  frob_monoid   : Monoid X;
  frob_comonoid : Comonoid X;

  frob_law_left :
    bimap (@mu _ _ _ frob_monoid) id[X]
      ∘ from (@tensor_assoc C M X X X)
      ∘ bimap id[X] (@delta _ _ _ frob_comonoid)
    ≈ (@delta _ _ _ frob_comonoid) ∘ (@mu _ _ _ frob_monoid);

  frob_law_right :
    bimap id[X] (@mu _ _ _ frob_monoid)
      ∘ to (@tensor_assoc C M X X X)
      ∘ bimap (@delta _ _ _ frob_comonoid) id[X]
    ≈ (@delta _ _ _ frob_comonoid) ∘ (@mu _ _ _ frob_monoid)
}.
#[export] Existing Instance frob_monoid.
#[export] Existing Instance frob_comonoid.

Coercion frob_monoid   : Frobenius >-> Monoid.
Coercion frob_comonoid : Frobenius >-> Comonoid.

End Frobenius.

Arguments frob_monoid   {C M X _}.
Arguments frob_comonoid {C M X _}.
