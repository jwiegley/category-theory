Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.

Generalizable All Variables.
Set Transparent Obligations.

#[export]
Program Instance CoproductFunctor `(C : Category) `{@Cocartesian C} :
  C ∐ C ⟶ C := {
  fobj := fun p => sum_rect (λ _, C) (λ a, a) (λ b, b) p;
  fmap := fun x y p =>
            match x with
            | Datatypes.inl x =>
              match y with
              | Datatypes.inl y => _
              | Datatypes.inr _ => False_rect _ _
              end
            | Datatypes.inr x =>
              match y with
              | Datatypes.inl _ => False_rect _ _
              | Datatypes.inr y => _
              end
            end;
}.
Next Obligation. proper; destruct x, y; simpl; tauto. Qed.
Next Obligation. destruct x; simpl; reflexivity. Qed.
Next Obligation. destruct x, y, z; simpl; cat; tauto. Qed.
