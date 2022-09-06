Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Corollary Diagonal_Unique (J C : Category) {D : Category} (d : D) :
  Δ[J](d) ≈[Cat] Δ(d) ∘[Cat] one.
Proof. exists (fun _ => iso_id); simpl; intros; cat. Qed.
