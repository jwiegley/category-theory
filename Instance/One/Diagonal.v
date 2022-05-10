Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Diagonal.
Require Export Category.Instance.Cat.
Require Export Category.Instance.One.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Corollary Diagonal_Unique (J C : Category) {D : Category} (d : D) :
  Δ[J](d) ≈[Cat] Δ(d) ∘[Cat] one.
Proof. exists (fun _ => iso_id); simpl; intros; cat. Qed.
