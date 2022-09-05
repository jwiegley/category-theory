Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Wedge.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class End `(F : C^op ∏ C ⟶ D) := {
  end_wedge : Wedge F;

  ump_ends : ∀ W : Wedge F, ∃! u : W ~> end_wedge, ∀ x : C,
    wedge_map[end_wedge] ∘ u ≈ @wedge_map _ _ _ W x
}.

Arguments End {_%category _%category} F%functor.
Arguments end_wedge {_%category _%category} F%functor {_}.

Coercion wedge_obj `(F : C^op ∏ C ⟶ D) (E : End F) := @end_wedge _ _ _ E.

Require Import Category.Functor.Opposite.

Definition Coend `(F : C^op ∏ C ⟶ D) := @End (C^op) (D^op) (F^op).
