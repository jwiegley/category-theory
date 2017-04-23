Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Terminal.

Context `{C : Category}.

Class Terminal := {
  One : ob;
  one {A} : A ~> One;

  one_unique {A} (f g : A ~> One) : f ≈ g
}.

End Terminal.

(* Coercion terminal_category `{C : Category} `(_ : @Terminal C) := C. *)
(* Arguments terminal_category {_ } _ /. *)

Notation "X ~> 1" := (X ~> One) (at level 50) : category_scope.

Hint Resolve @one_unique : category_laws.

Corollary one_comp `{@Terminal C} {A B : C} {f : A ~> B} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.

Hint Rewrite @one_comp : categories.

Section TerminalFunctor.

Context `{F : C ⟶ D}.
Context `{@Terminal C}.
Context `{@Terminal D}.

Class TerminalFunctor := {
  map_one : One ~> F One;

  fmap_one {X : C} : fmap one ≈ map_one ∘ @one _ _ (F X)
}.

End TerminalFunctor.
