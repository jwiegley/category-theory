Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

Program Definition InternalHomFunctor `(C : Category)
        {E : @Cartesian C} {O : @Closed C _} : C^op ∏ C ⟶ C := {|
  fobj := fun p => @exponent_obj C E O (fst p) (snd p);
  fmap := fun x y '(f, g) => curry (g ∘ eval ∘ second (op f))
|}.
Next Obligation.
  proper; simpl.
  now rewrites.
Qed.
Next Obligation. unfork; cat. Qed.
Next Obligation.
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
  rewrite <- second_comp.
  reflexivity.
Qed.

Notation "a ≈> b":= (InternalHomFunctor _ (a, b))
  (at level 89) : category_scope.
Notation "a ≈{ C }≈> b":= (InternalHomFunctor C (a, b))
  (at level 89) : category_scope.
