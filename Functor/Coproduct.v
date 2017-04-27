Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Cocartesian.
Require Export Category.Construction.Coproduct.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Instance CoproductFunctor `(C : Category) `{@Cocartesian C} :
  C ∐ C ⟶ C := {
  fobj := fun p => sum_rect (λ _, C) (λ a, a) (λ b, b) p;
  fmap := fun X Y p =>
            match X with
            | Datatypes.inl X =>
              match Y with
              | Datatypes.inl Y => _
              | Datatypes.inr _ => False_rect _ _
              end
            | Datatypes.inr X =>
              match Y with
              | Datatypes.inl _ => False_rect _ _
              | Datatypes.inr Y => _
              end
            end;
}.
Next Obligation. proper; destruct X, Y; simpl; tauto. Qed.
Next Obligation. destruct X, Y, Z; simpl; cat; tauto. Qed.
