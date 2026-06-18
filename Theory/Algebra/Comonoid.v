Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Internal comonoids in a monoidal category *)

(* The dual of [Monoid]: a comonoid on [X : C] is a comultiplication
   [delta : X ~> X ⨂ X] and a counit [epsilon : X ~> I] satisfying the dual
   of the associativity and unit laws.  Writing [α] for the associator
   [tensor_assoc], [λ] for [unit_left] and [ρ] for [unit_right], the laws in
   this library's notation are:

     coassociativity   (δ ⨂ 1) ∘ δ ≈ α⁻¹ ∘ (1 ⨂ δ) ∘ δ
     left counit       (ε ⨂ 1) ∘ δ ≈ λ⁻¹
     right counit      (1 ⨂ ε) ∘ δ ≈ ρ⁻¹

   These are exactly the [Monoid] axioms with every arrow reversed (and hence
   every composite read right-to-left, [to] iso directions becoming [from]).

   In principle [Comonoid X] could be obtained as [@Monoid (C^op) _ X], but
   defining a [Monoidal] instance on [C^op] requires extra machinery (the
   tensor reverses and the unit/associator flip), and the resulting class
   members would need to be re-unfolded everywhere.  Following the practice
   elsewhere in this library (cf. [Cocartesian], [Initial]) we instead state
   the dual class directly.

   nLab:      https://ncatlab.org/nlab/show/comonoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory) *)

Section Comonoid.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Comonoid (X : C) : Type := {
  delta   : X ~> X ⨂ X;            (* comultiplication, dual of [mu]  *)
  epsilon : X ~> I;                (* counit, dual of [eta]           *)

  (* coassociativity: dual of [mu_assoc] *)
  delta_coassoc :
    bimap delta id[X] ∘ delta
      ≈ from (@tensor_assoc C M X X X) ∘ bimap id[X] delta ∘ delta;

  (* left counit law: dual of [mu_unit_left] *)
  delta_counit_left :
    bimap epsilon id[X] ∘ delta
      ≈ from (@unit_left C M X);

  (* right counit law: dual of [mu_unit_right] *)
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
