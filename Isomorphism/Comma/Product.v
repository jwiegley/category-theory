Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Construction.Comma.
Require Export Category.Construction.Product.
Require Export Category.Structure.Terminal.
Require Export Category.Instance.Cat.
Require Export Category.Instance.One.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductComma.

Theorem Comma_Product `{C : Category} `{D : Category}
        (F : C ⟶ 1) (G : D ⟶ 1) :
  (F ↓ G) ≅[Cat] C ∏ D.
Proof.
  isomorphism; simpl.
  - functor; cat.
  - functor; simpl; intros; cat; proper.
  - Time abstract (constructive; simpl; cat; simpl; cat).
  - Time abstract (constructive; simpl; cat; simpl; cat).
Qed.

Time End ProductComma.
