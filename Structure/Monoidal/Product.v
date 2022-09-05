Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

#[local] Obligation Tactic := simpl; intros; simplify; simpl in *.

#[global]
Program Instance Product_Monoidal `{@Monoidal C} `{@Monoidal D} :
  @Monoidal (C ∏ D) := {
  tensor :=
    {| fobj := fun p => (fst (fst p) ⨂ fst (snd p),
                         snd (fst p) ⨂ snd (snd p))%object
     ; fmap := fun _ _ f => (fst (fst f) ⨂ fst (snd f),
                             snd (fst f) ⨂ snd (snd f)) |};
  I := (@I C _, @I D _)
}.
Next Obligation. exact H. Defined.
Next Obligation. exact H0. Defined.
Next Obligation.
  proper; simplify; simpl in *;
  rewrites; reflexivity.
Qed.
Next Obligation. all:normal; reflexivity. Qed.
Next Obligation. all:apply bimap_comp. Qed.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply unit_left.
  - apply unit_left.
  - apply (unit_left⁻¹).
  - apply (unit_left⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply unit_right.
  - apply unit_right.
  - apply (unit_right⁻¹).
  - apply (unit_right⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply tensor_assoc.
  - apply tensor_assoc.
  - apply (tensor_assoc⁻¹).
  - apply (tensor_assoc⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation. all:apply to_unit_left_natural. Qed.
Next Obligation. all:apply from_unit_left_natural. Qed.
Next Obligation. all:apply to_unit_right_natural. Qed.
Next Obligation. all:apply from_unit_right_natural. Qed.
Next Obligation. all:apply to_tensor_assoc_natural. Qed.
Next Obligation. all:apply from_tensor_assoc_natural. Qed.
Next Obligation. all:apply triangle_identity. Qed.
Next Obligation. all:apply pentagon_identity. Qed.
