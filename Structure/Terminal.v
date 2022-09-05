Set Warnings "-notation-overridden".
Set Warnings "-fragile-hint-constr".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Terminal.

Context {C : Category}.

Class Terminal := {
  terminal_obj : C;
  one {x} : x ~> terminal_obj;

  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g
}.

End Terminal.

Notation "1" := terminal_obj : object_scope.

#[export] Hint Resolve @one_unique : category_laws.

Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.

#[export] Hint Rewrite @one_comp : categories.

Notation "one[ C ]" := (@one _ _ C)
  (at level 9, format "one[ C ]") : morphism_scope.

Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].
