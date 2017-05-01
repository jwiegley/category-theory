Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Comma.
Require Export Category.Instance.One.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Instance Slice `(C : Category) `(c : C) : Category := {
  ob      := { a : C & a ~> c };
  hom     := fun x y => (`` x) ~> (`` y);
  homset  := fun _ _ => {| equiv := fun f g => f ≈ g |} ;
  id      := fun _ => id;
  compose := fun _ _ _ f g => f ∘ g
}.

Notation "C ̸ c" := (@Slice C c) (at level 90) : category_scope.

(* Although the encoding of Slice above is more convenient, theoretically it's
   the comma category (Id[C] ↓ Select c). *)

Program Instance Comma_Slice `(C : Category) `(c : C) :
  C ̸ c ≅[Cat] (Id ↓ Select c) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  exists (X, tt); simpl.
  assumption.
Defined.
Next Obligation.
  proper; simpl.
  exists o.
  assumption.
Defined.
Next Obligation.
  constructive; simpl.
  all:swap 2 3.
  - destruct X, x, u; simpl.
    split.
      exact id.
    exact tt.
  - destruct X, x, u; simpl.
    split.
      exact id.
    exact tt.
  - destruct X, Y, x, x0, u, u0, f; simpl; cat.
  - destruct X, Y, x, x0, u, u0, f; simpl; cat.
  - destruct A, x, u; simpl; cat.
  - destruct A, x, u; simpl; cat.
Qed.
Next Obligation.
  constructive; simpl.
  all:swap 2 3.
  - destruct X; simpl.
    exact id.
  - destruct X; simpl.
    exact id.
  - destruct X, Y; simpl; cat.
  - destruct X, Y; simpl; cat.
  - destruct A; simpl; cat.
  - destruct A; simpl; cat.
Qed.

Program Instance Coslice `(C : Category) `(c : C) : Category := {
  ob      := { a : C & c ~> a };
  hom     := fun x y => (`` x) ~> (`` y);
  homset  := fun _ _ => {| equiv := fun f g => f ≈ g |} ;
  id      := fun _ => id;
  compose := fun _ _ _ f g => f ∘ g
}.

Notation "C ̸co c" := (@Coslice C c) (at level 90) : category_scope.

Program Instance Comma_Coslice `(C : Category) `(c : C) :
  C ̸co c ≅[Cat] (Select c ↓ Id) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  exists (tt, X); simpl.
  assumption.
Defined.
Next Obligation.
  proper; simpl.
  exists o.
  assumption.
Defined.
Next Obligation.
  constructive; simpl.
  all:swap 2 3.
  - destruct X, x, u; simpl.
    split.
      exact tt.
    exact id.
  - destruct X, x, u; simpl.
    split.
      exact tt.
    exact id.
  - destruct X, Y, x, x0, u, u0, f; simpl; cat.
  - destruct X, Y, x, x0, u, u0, f; simpl; cat.
  - destruct A, x, u; simpl; cat.
  - destruct A, x, u; simpl; cat.
Qed.
Next Obligation.
  constructive; simpl.
  all:swap 2 3.
  - destruct X; simpl.
    exact id.
  - destruct X; simpl.
    exact id.
  - destruct X, Y; simpl; cat.
  - destruct X, Y; simpl; cat.
  - destruct A; simpl; cat.
  - destruct A; simpl; cat.
Qed.
