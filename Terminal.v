Require Import Lib.
Require Export Category.
Require Export Functor.

Generalizable All Variables.

Class Terminal (ob : Type) := {
  terminal_category :> Category ob;
  One : ob;
  one {A} : A ~> One;

  one_eqv {A} (f g : A ~> One) : f ≈ g
}.

Notation "X ~> 1" := (X ~> One) (at level 50) : category_scope.

Hint Resolve @one_eqv : category_laws.

Corollary one_comp `{Terminal C} {A B : C} {f : A ~> B} :
  one ∘ f ≈ one.
Proof.
  intros.
  apply one_eqv.
Defined.

Hint Rewrite @one_comp : categories.

Class TerminalFunctor `(_ : Terminal C) `(_ : Terminal D) := {
  terminal_category_functor :> @Functor C _ D _;

  map_one : One ~> fobj One;

  fmap_one {X : C} : fmap one ≈ map_one ∘ @one _ _ (fobj X)
}.

Arguments TerminalFunctor C {_} D {_}.
