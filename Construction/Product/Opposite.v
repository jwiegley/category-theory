Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Corollary Product_Opposite {C D : Category} : (C ∏ D) ^op = (C^op ∏ D^op).
Proof. reflexivity. Qed.
