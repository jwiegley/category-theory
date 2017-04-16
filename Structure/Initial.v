Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Class Initial `(C : Category) := {
  Zero : ob;
  zero {A} : Zero ~> A;

  zero_eqv {A} {f g : Zero ~> A} : f ≈ g
}.

Hint Resolve @zero_eqv : category_laws.

Notation "0 ~> X" := (Zero ~> X) (at level 50).

Corollary zero_comp `{@Initial C} {A B : C} {f : A ~> B} :
  f ∘ zero ≈ zero.
Proof.
  intros.
  apply zero_eqv.
Defined.

Hint Rewrite @zero_comp : categories.

Section InitialFunctor.

Context `{F : C ⟶ D}.
Context `{@Initial C}.
Context `{@Initial D}.

Class InitialFunctor := {
  map_zero : F Zero ~> Zero;

  fmap_zero {X : C} :
    fmap[F] zero ≈ @zero _ _ (F X) ∘ map_zero
}.

End InitialFunctor.
