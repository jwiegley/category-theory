Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.
Require Export Category.Instance.Nat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Monoidal.

Context `{C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  tensor : C ⟶ [C, C]           (* uncurried = C ∏ C ⟶ C *)
    where "x ⨂ y" := (tensor x y);

  munit : C;

  unit_left  {X} : munit ⨂ X ≅ X;
  unit_right {X} : X ⨂ munit ≅ X;

  tensor_assoc {X Y Z} : (X ⨂ Y) ⨂ Z ≅ X ⨂ (Y ⨂ Z)
}.

End Monoidal.
