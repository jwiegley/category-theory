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

    nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
    Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra

    A Frobenius algebra on [X] is a monoid [(X, mu, eta)] and a comonoid
    [(X, delta, epsilon)] on the same object, satisfying the Frobenius
    compatibility law:

        (id ⨂ mu) ∘ (delta ⨂ id) ≈ delta ∘ mu ≈ (mu ⨂ id) ∘ (id ⨂ delta)

    (up to suitable insertions of the tensor associator).  Per nLab, the two
    equalities collapse into the single condition equating the outer
    composites, [(id ⨂ mu) ∘ (delta ⨂ id) ≈ (mu ⨂ id) ∘ (id ⨂ delta)], with
    the middle [delta ∘ mu] recovered using (co)unitality; together they
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
  frob_monoid   : Monoid X;     (* the multiplication [mu] and unit [eta] *)
  frob_comonoid : Comonoid X;   (* the comultiplication [delta] and counit [epsilon] *)

  (* Frobenius law, left form: [(mu ⨂ id) ∘ α⁻¹ ∘ (id ⨂ delta) ≈ delta ∘ mu]. *)
  frob_law_left :
    bimap (@mu _ _ _ frob_monoid) id[X]
      ∘ from (@tensor_assoc C M X X X)
      ∘ bimap id[X] (@delta _ _ _ frob_comonoid)
    ≈ (@delta _ _ _ frob_comonoid) ∘ (@mu _ _ _ frob_monoid);

  (* Frobenius law, right form: [(id ⨂ mu) ∘ α ∘ (delta ⨂ id) ≈ delta ∘ mu]. *)
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

(** ** Flat projections

    Convenience aliases paralleling [scfa_mu] / [scfa_eta] /
    [scfa_delta] / [scfa_epsilon] (in
    [Theory/Algebra/SpecialCommutativeFrobenius.v]) and [cfrob_*]
    (in [Theory/Algebra/CommutativeFrobenius.v]).  Project a
    [Frobenius X] to its underlying [mu] / [eta] / [delta] /
    [epsilon] without going through [frob_monoid] / [frob_comonoid]
    one-by-one.

    The instance arguments are explicit so downstream code can
    write e.g. [frob_mu F] unambiguously. *)

Section FrobeniusProjections.

Context {C : Category}.
Context `{M : @Monoidal C}.

Definition frob_mu {X : C} (F : Frobenius X) : (X ⨂ X)%object ~> X :=
  @mu _ _ _ (frob_monoid (X := X)).

Definition frob_eta {X : C} (F : Frobenius X) : @I _ _ ~> X :=
  @eta _ _ _ (frob_monoid (X := X)).

Definition frob_delta {X : C} (F : Frobenius X) : X ~> (X ⨂ X)%object :=
  @delta _ _ _ (frob_comonoid (X := X)).

Definition frob_epsilon {X : C} (F : Frobenius X) : X ~> @I _ _ :=
  @epsilon _ _ _ (frob_comonoid (X := X)).

End FrobeniusProjections.

Arguments frob_mu      {C M X} F.
Arguments frob_eta     {C M X} F.
Arguments frob_delta   {C M X} F.
Arguments frob_epsilon {C M X} F.
