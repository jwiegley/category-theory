Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Internal monoids in a monoidal category

    Given a monoidal category [(C, ⨂, I)], a monoid (object) on an object
    [X : C] is a triple [(X, mu, eta)] with [mu : X ⨂ X ~> X], [eta : I ~> X]
    satisfying the usual associativity and unit laws.

    This is the standard nLab definition of "monoid in a monoidal category".
    The existing [Structure.Monoid] file gives an equivalent presentation, but
    its definition is paired with [MonoidObject] in a cartesian category and
    uses the cartesian unit/associator.  Here we factor out the abstract
    monoid-in-a-monoidal-category form so it can be reused as the building
    block for Frobenius algebras (and dualised to give comonoids).

    The laws are stated as setoid equalities ([≈]), so that morphisms which
    are merely equivalent up to the homset equivalence are considered to be
    "the same" structural map. *)

Section Monoid.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Monoid (X : C) : Type := {
  mu  : X ⨂ X ~> X;
  eta : I ~> X;

  mu_assoc :
    mu ∘ bimap mu id[X]
      ≈ mu ∘ bimap id[X] mu ∘ to tensor_assoc;

  mu_unit_left :
    mu ∘ bimap eta id[X]
      ≈ to (@unit_left C M X);

  mu_unit_right :
    mu ∘ bimap id[X] eta
      ≈ to (@unit_right C M X)
}.

End Monoid.

Arguments mu  {C M X _}.
Arguments eta {C M X _}.

Notation "'mu[' Mon ]"  := (@mu _ _ _ Mon)
  (at level 9, format "'mu[' Mon ]") : morphism_scope.
Notation "'eta[' Mon ]" := (@eta _ _ _ Mon)
  (at level 9, format "'eta[' Mon ]") : morphism_scope.
