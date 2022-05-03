Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Comma.
Require Export Category.Functor.Diagonal.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Definition Slice `(C : Category) `(c : C) : Category := {|
  obj     := ∃ a : C, a ~> c;
  hom     := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ∘ f ≈ `2 x;
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |} ;
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. rewrite comp_assoc; rewrites; reflexivity. Defined.

Notation "C  ̸ c" := (@Slice C c) (at level 90) : category_scope.

(* Although the encoding of Slice above is more convenient, theoretically it's
   the comma category (Id[C] ↓ Δ(c)). *)

Program Instance Comma_Slice `(C : Category) `(c : C) :
  C ̸ c ≅[Cat] (Id ↓ =(c)) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  destruct u1, u0; simpl.
  exists h.
  rewrites; cat.
Defined.
Next Obligation. constructive; simplify; simpl in *; cat. Qed.
Next Obligation. constructive; simplify; simpl in *; cat. Qed.

Program Definition Coslice `(C : Category) `(c : C) : Category := {|
  obj     := ∃ a : C, c ~> a;
  hom     := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ≈ f ∘ `2 x;
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |} ;
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. rewrite <- comp_assoc; rewrites; reflexivity. Defined.

Notation "c  ̸co C" := (@Coslice C c) (at level 90) : category_scope.

Program Instance Comma_Coslice `(C : Category) `(c : C) :
  c ̸co C ≅[Cat] (=(c) ↓ Id) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  destruct u1, u0.
  exists h; simpl.
  rewrites; cat.
Defined.
Next Obligation. constructive; simplify; simpl in *; cat. Qed.
Next Obligation. constructive; simplify; simpl in *; cat. Qed.
