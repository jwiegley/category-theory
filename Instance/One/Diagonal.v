Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Diagonal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Lemma Diagonal_Unique `(C : Category) {D : Category} (d : D) :
  Diagonal C d ≈[Cat] Const d ∘[Cat] one.
Proof.
  constructive; simpl; intros.
  all:swap 2 4; try exact id; cat.
Qed.
