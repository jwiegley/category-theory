Set Warnings "-notation-overridden".

Set Warnings "-deprecated-ident-entry".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Unique {C : Category} {x y : C} (P : (x ~> y) -> Type) := {
  unique_morphism : x ~> y;
  unique_property : P unique_morphism;
  uniqueness      : ∀ v : x ~> y, P v -> unique_morphism ≈ v
}.

Arguments unique_morphism {_ _ _ _} _.
Arguments unique_property {_ _ _ _} _.
Arguments uniqueness {_ _ _ _} _.

Notation "∃! f : A , P" := (Unique (fun f : A => P))
  (at level 9, f ident, A at level 200, P at level 200) : category_theory_scope.
