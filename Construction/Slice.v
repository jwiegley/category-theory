Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Comma.
Require Export Category.Instance.One.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Slice `(C : Category) `(c : C) : Category := {|
  ob      := { a : C & a ~> c };
  hom     := fun x y => (`` x) ~> (`` y);
  homset  := fun _ _ => {| equiv := fun f g => f ≈ g |} ;
  id      := fun _ => id;
  compose := fun _ _ _ f g => f ∘ g
|}.

Notation "C ̸ c" := (@Slice C c) (at level 90) : category_scope.

(* Although the encoding of Slice above is more convenient, theoretically it's
   the comma category (Id[C] ↓ Const c). *)

Program Definition Comma_Slice `(C : Category) `(c : C) :
  C ̸ c ≅[Cat] (Id ↓ Const c) := {|
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
|}.
Next Obligation. constructive; simplify; simpl in *; cat. Qed.
Next Obligation. constructive; simplify; simpl in *; cat. Qed.

Program Definition Coslice `(C : Category) `(c : C) : Category := {|
  ob      := { a : C & c ~> a };
  hom     := fun x y => (`` x) ~> (`` y);
  homset  := fun _ _ => {| equiv := fun f g => f ≈ g |} ;
  id      := fun _ => id;
  compose := fun _ _ _ f g => f ∘ g
|}.

Notation "C ̸co c" := (@Coslice C c) (at level 90) : category_scope.

Program Definition Comma_Coslice `(C : Category) `(c : C) :
  C ̸co c ≅[Cat] (Const c ↓ Id) := {|
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
|}.
Next Obligation. constructive; simplify; simpl in *; cat. Qed.
Next Obligation. constructive; simplify; simpl in *; cat. Qed.
