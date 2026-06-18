Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Internal monoids in a monoidal category *)

(* nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   Given a monoidal category (C, ⨂, I), a monoid (object) on an object X : C
   is a triple (X, mu, eta) with a multiplication mu : X ⨂ X ~> X and a unit
   eta : I ~> X satisfying the associativity and left/right unit laws, with
   the associator and unitors inserted to make the maps composable:

     associativity  mu ∘ (mu ⨂ id) ≈ mu ∘ (id ⨂ mu) ∘ α     (α = to tensor_assoc)
     left unit      mu ∘ (eta ⨂ id) ≈ λ                       (λ = to unit_left)
     right unit     mu ∘ (id ⨂ eta) ≈ ρ                       (ρ = to unit_right)

   Here ⨂ on morphisms is [bimap], α : (X ⨂ X) ⨂ X ≅ X ⨂ (X ⨂ X) is the
   associator, and λ : I ⨂ X ≅ X, ρ : X ⨂ I ≅ X are the left/right unitors;
   the [to] direction of each isomorphism is the one used above.

   This is the standard nLab/Wikipedia definition of "monoid in a monoidal
   category". The existing [Structure.Monoid] file gives an equivalent
   presentation, but its [MonoidObject] is developed alongside the cartesian
   case using the cartesian unit/associator. Here we factor out the abstract
   monoid-in-a-monoidal-category form so it can be reused as the building
   block for Frobenius algebras (and dualised to give comonoids).

   The laws are stated as setoid equalities ([≈]), so that morphisms which
   are merely equivalent up to the homset equivalence are considered to be
   "the same" structural map. *)

Section Monoid.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Monoid (X : C) : Type := {
  mu  : X ⨂ X ~> X;             (* multiplication μ : X ⨂ X ~> X *)
  eta : I ~> X;                 (* unit           η : I     ~> X *)

  (* associativity: mu ∘ (mu ⨂ id) ≈ mu ∘ (id ⨂ mu) ∘ α *)
  mu_assoc :
    mu ∘ bimap mu id[X]
      ≈ mu ∘ bimap id[X] mu ∘ to tensor_assoc;

  (* left unit: mu ∘ (eta ⨂ id) ≈ λ (left unitor) *)
  mu_unit_left :
    mu ∘ bimap eta id[X]
      ≈ to (@unit_left C M X);

  (* right unit: mu ∘ (id ⨂ eta) ≈ ρ (right unitor) *)
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
