Require Import Lib.
Require Export Category.
Require Export Functor.

Generalizable All Variables.

Class Initial `(_ : Category ob) := {
  Zero : ob;
  zero {A} : Zero ~> A;

  zero_eqv {A} {f g : Zero ~> A} : f ≈ g
}.

Arguments Initial ob {_}.

Hint Resolve @zero_eqv : category_laws.

Notation "0 ~> X" := (Zero ~> X) (at level 50).

Corollary zero_comp `{Initial C} {A B : C} {f : A ~> B} :
  f ∘ zero ≈ zero.
Proof.
  intros.
  apply zero_eqv.
Defined.

Hint Rewrite @zero_comp : categories.

Class InitialFunctor `(_ : Initial C) `(_ : Initial D) := {
  initial_category_functor :> @Functor C _ D _;

  map_zero : fobj Zero ~> Zero;

  fmap_zero {X : C} :
    @fmap C _ D _ _ Zero X zero ≈ @zero _ _ _ (fobj X) ∘ map_zero
}.

Arguments InitialFunctor C {_ _} D {_ _}.
