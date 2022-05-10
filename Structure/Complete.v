Set Warnings "-notation-overridden".


Require Import Category.Lib.
Require Export Category.Structure.Limit.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Complete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Limit F.

Definition Cocomplete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Colimit F.
