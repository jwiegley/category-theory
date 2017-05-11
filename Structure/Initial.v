Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Initial `(C : Category) := {
  Zero : ob;
  zero {A} : Zero ~> A;

  zero_unique {A} {f g : Zero ~> A} : f ≈ g
}.

Notation "0" := Zero : object_scope.

Hint Resolve @zero_unique : category_laws.

Corollary zero_comp `{@Initial C} {A B : C} {f : A ~> B} :
  f ∘ zero ≈ zero.
Proof. intros; apply zero_unique. Qed.

Hint Rewrite @zero_comp : categories.
