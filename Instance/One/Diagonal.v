Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Diagonal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Corollary Diagonal_Unique `(C : Category) {D : Category} (d : D) :
  Diagonal C d ≈[Cat] Const d ∘[Cat] one.
Proof. exists (fun _ => iso_id); simpl; intros; cat. Qed.
