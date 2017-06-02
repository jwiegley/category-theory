Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Terminal.

Context {C : Category}.

Class Terminal := {
  One : ob;
  one {x} : x ~> One;

  one_unique {x} (f g : x ~> One) : f ≈ g
}.

End Terminal.

Notation "1" := One : object_scope.

Hint Resolve @one_unique : category_laws.

Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.

Hint Rewrite @one_comp : categories.

Notation "one[ C ]" := (@one _ _ C)
  (at level 9, format "one[ C ]") : morphism_scope.
