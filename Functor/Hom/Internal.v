Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.
Require Import Category.Structure.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Definition InternalHomFunctor `(C : Category)
        {E : @Cartesian C} {O : @Closed C _} : C^op ∏ C ⟶ C := {|
  fobj := fun p => @Exp C E O (fst p) (snd p);
  fmap := fun X Y f => _
|}.
Next Obligation.
  exact (curry (h0 ∘ eval ∘ (second h))).
Defined.
Next Obligation.
  unfold InternalHomFunctor_obligation_1.
  proper; simpl.
  rewrite x0, y0.
  reflexivity.
Qed.
Next Obligation. unfold second; simpl; cat. Qed.
Next Obligation.
  unfold InternalHomFunctor_obligation_1; simpl.
  rewrite <- !comp_assoc.
  rewrite curry_comp.
  symmetry.
  rewrite curry_comp.
  rewrite <- comp_assoc.
  apply compose_respects.
    reflexivity.
  symmetry.
  rewrite curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- first_second.
  rewrite !comp_assoc.
  rewrite ump_exponents.
  rewrite <- !comp_assoc.
  rewrite second_comp.
  reflexivity.
Qed.

Notation "a ≈> b":= (InternalHomFunctor _ (a, b))
  (at level 89) : category_scope.
Notation "a ≈{ C }≈> b":= (InternalHomFunctor C (a, b))
  (at level 89) : category_scope.
