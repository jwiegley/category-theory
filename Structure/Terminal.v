Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Terminal.

Context `{C : Category}.

Class Terminal := {
  One : ob;
  one {A} : A ~> One;

  one_unique {A} (f g : A ~> One) : f ≈ g
}.

End Terminal.

Notation "1" := One : object_scope.

(* Coercion terminal_category `{C : Category} `(_ : @Terminal C) := C. *)
(* Arguments terminal_category {_ } _ /. *)

Hint Resolve @one_unique : category_laws.

Corollary one_comp `{@Terminal C} {A B : C} {f : A ~> B} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.

Hint Rewrite @one_comp : categories.
