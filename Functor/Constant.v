Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Constant `(C : Category) {D : Category} (d : D) :
  C ⟶ D := {|
  fobj := fun _ => d;
  fmap := fun _ _ _ => id[d]
|}.

Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Lemma Constant_Unique `(C : Category) {D : Category} (d : D) :
  Constant C d ≈[Cat] Const d ∘[Cat] one.
Proof.
  constructive; simpl; intros.
  - exact id.
  - cat.
  - exact id.
  - cat.
  - cat.
  - cat.
Qed.
