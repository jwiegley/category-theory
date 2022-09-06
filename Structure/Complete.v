Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.

Generalizable All Variables.

Definition Complete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Limit F.

Definition Cocomplete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Colimit F.
