Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cocartesian.
Require Export Category.Construction.Coproduct.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Another way of reading this is that we're proving Cat^op is Cartesian. *)

Program Instance Cat_Cocartesian : @Cocartesian Cat := {
  Prod := @Coproduct;
  fork := fun _ _ _ F G =>
    {| fobj := fun x =>
                 match x with
                 | Datatypes.inl x => F x
                 | Datatypes.inr x => G x
                 end
     ; fmap := fun X Y f =>
                 match X with
                 | Datatypes.inl X =>
                   match Y with
                   | Datatypes.inl Y => _
                   | Datatypes.inr Y => False_rect _ _
                   end
                 | Datatypes.inr X =>
                   match Y with
                   | Datatypes.inl Y => False_rect _ _
                   | Datatypes.inr Y => _
                   end
                 end |};
  exl := fun _ _ =>
            {| fobj := Datatypes.inl
             ; fmap := fun _ _ => _ |};
  exr := fun _ _ =>
            {| fobj := Datatypes.inr
             ; fmap := fun _ _ => _ |};
}.
Next Obligation. exact (fmap f). Defined.
Next Obligation. exact (fmap f). Defined.
Next Obligation.
  proper.
  destruct X, Y; simpl in *;
  solve [ apply fmap_respects; auto | contradiction ].
Qed.
Next Obligation.
  destruct X; simpl in *; cat.
Qed.
Next Obligation.
  destruct X, Y, Z; simpl in *; try tauto;
  apply fmap_comp.
Qed.
Next Obligation.
  proper.
  destruct x3, y1; simpl; auto; tauto.
Qed.
Next Obligation.
  split; intros; simplify.
  - apply (e (Datatypes.inl x0) (Datatypes.inl y)).
  - apply (e (Datatypes.inr x0) (Datatypes.inr y)).
  - destruct x; auto.
  - destruct x, y.
    + apply e0; tauto.
    + tauto.
    + tauto.
    + apply e; tauto.
Qed.
