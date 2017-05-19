Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition Constant `(C : Category) `{D : Category} (d : D) :
  C ⟶ D := {|
  fobj := fun _ => d;
  fmap := fun _ _ _ => id[d]
|}.

Require Export Category.Instance.One.

Program Definition Unique `{D : Category} (d : D) : 1 ⟶ D := {|
  fobj := fun _ => d;
  fmap := fun _ _ _ => id[d]
|}.

Require Export Category.Structure.Terminal.
Require Export Category.Instance.Cat.

Lemma Constant_Unique `(C : Category) `{D : Category} (d : D) :
  Constant C d ≈[Cat] Unique d ∘[Cat] one.
Proof.
  constructive; simpl; intros.
  - exact id.
  - cat.
  - exact id.
  - cat.
  - cat.
  - cat.
Qed.
