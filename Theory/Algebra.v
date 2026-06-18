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

(** * Categorified high-school algebra in a bicartesian closed category *)

(* nLab: https://ncatlab.org/nlab/show/bicartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/rig+category
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_category

   This file collects results proven elsewhere (in Structure/Cartesian.v,
   Structure/Cocartesian.v, and Structure/Cartesian/Closed.v) to exhibit a
   direct correspondence between categorical constructions and basic
   high-school algebra. In a bicartesian closed category — one that is
   cartesian (×, with terminal object 1), cocartesian (+, with initial
   object 0) and cartesian closed (internal hom, written x^y) — the
   structural isomorphisms categorify the identities of a rig (a semiring,
   i.e. a ring without negatives): the coproduct + behaves like addition with
   unit 0, the product × like multiplication with unit 1 annihilated by 0,
   distributivity of × over + holds, and the internal hom x^y plays the role
   of exponentiation. Reading ≅ ("isomorphic") for the algebraist's = , each
   goal below is the categorified counterpart of a familiar arithmetic law,
   for example x × (y + z) ≅ (x × y) + (x × z), x^(y + z) ≅ x^y × x^z and
   x^(y × z) ≅ (x^y)^z (the last being the curry/uncurry adjunction). Every
   goal is discharged by [auto] from the local hint database of these
   pre-proven isomorphisms, so this section asserts no new content; it is a
   readable index of the algebra that the BiCCC structure already provides. *)

Section BasicAlgebra.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.
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
