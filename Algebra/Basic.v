Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.BiCCC.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* This file repeats results from elsewhere, to show a direct correspondence
   between categorical constructions, and basic high-school algebra. *)

Section BasicAlgebra.

Context {C : Category}.
Context `{A : @Cartesian C}.
Context `{@Closed C A}.
Context `{@Terminal C}.
Context `{@Initial C}.
Context `{@Cocartesian C}.

#[local] Hint Resolve coprod_zero_r : core.
#[local] Hint Resolve coprod_zero_l : core.
#[local] Hint Resolve coprod_comm : core.
#[local] Hint Resolve coprod_assoc : core.
#[local] Hint Resolve prod_zero_r : core.
#[local] Hint Resolve prod_zero_l : core.
#[local] Hint Resolve prod_one_r : core.
#[local] Hint Resolve prod_one_l : core.
#[local] Hint Resolve prod_assoc : core.
#[local] Hint Resolve prod_comm : core.
#[local] Hint Resolve exp_zero : core.
#[local] Hint Resolve exp_one : core.
#[local] Hint Resolve one_exp : core.
#[local] Hint Resolve prod_coprod_l : core.
#[local] Hint Resolve prod_coprod_r : core.
#[local] Hint Resolve exp_swap : core.
#[local] Hint Resolve exp_prod_l : core.
#[local] Hint Resolve exp_prod_r : core.
#[local] Hint Resolve exp_coprod : core.

#[local] Hint Extern 4 => intros x y z; transitivity ((x^z)^y); auto : core.

Goal ∀ x : C,        x + 0 ≅ x.                          auto. Qed.
Goal ∀ x : C,        0 + x ≅ x.                          auto. Qed.
Goal ∀ x y : C,      x + y ≅ y + x.                      auto. Qed.
Goal ∀ x y z : C,    (x + y) + z ≅ x + (y + z).          auto. Qed.

Goal ∀ x : C,        x × 0 ≅ 0.                          auto. Qed.
Goal ∀ x : C,        0 × x ≅ 0.                          auto. Qed.
Goal ∀ x : C,        x × 1 ≅ x.                          auto. Qed.
Goal ∀ x : C,        1 × x ≅ x.                          auto. Qed.
Goal ∀ x y z : C,    (x × y) × z ≅ x × (y × z).          auto. Qed.
Goal ∀ x y : C,      x × y ≅ y × x.                      auto. Qed.

Goal ∀ x y z : C,    x × (y + z) ≅ (x × y) + (x × z).    auto. Qed.
Goal ∀ x y z : C,    (x + y) × z ≅ (x × z) + (y × z).    auto. Qed.

Goal ∀ x : C,        x^0 ≅ 1.                            auto. Qed.
Goal ∀ x : C,        x^1 ≅ x.                            auto. Qed.
Goal ∀ x : C,        1^x ≅ 1.                            auto. Qed.
Goal ∀ x y z : C,    x^(y + z) ≅ x^y × x^z.              auto. Qed.
Goal ∀ x y z : C,    (x × y)^z ≅ x^z × y^z.              auto. Qed.
Goal ∀ x y z : C,    x^(y × z) ≅ (x^y)^z.                auto. Qed.

End BasicAlgebra.
