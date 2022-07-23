Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".
Set Warnings "-fragile-hint-constr".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Structure.Terminal.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* To be initial is just to be terminal in the opposite category; but to avoid
   confusion, we'd like a set of notations specific to categories with initial
   objects. *)

Notation "'Initial' C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
  (at level 9) : category_theory_scope.

Section Initial_.

Context `{I : @Initial C}.

Definition initial_obj : C := @terminal_obj _ I.
Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

Definition zero_unique {x} (f g : initial_obj ~{C}~> x) : f ≈ g :=
  @one_unique _ I _ _ _.

End Initial_.

Notation "0" := initial_obj : object_scope.

Notation "zero[ C ]" := (@zero _ _ C)
  (at level 9, format "zero[ C ]") : morphism_scope.

#[export] Hint Resolve @zero_unique : category_laws.

Corollary zero_comp `{T : @Initial C} {x y : C} {f : x ~> y} :
  f ∘ zero ≈ zero.
Proof. apply (@one_comp _ T). Qed.

#[export] Hint Rewrite @zero_comp : categories.
