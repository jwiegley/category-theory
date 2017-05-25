Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Constant.
Require Import Category.Instance.One.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Lemma Constant_Unique `(C : Category) {D : Category} (d : D) :
  Constant C d ≈[Cat] Const d ∘[Cat] one.
Proof.
  constructive; simpl; intros.
  all:swap 2 4; try exact id; cat.
Qed.
