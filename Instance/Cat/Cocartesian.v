Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

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
  product_obj := @Coproduct;
  fork := fun _ _ _ F G =>
    {| fobj := fun x =>
                 match x with
                 | Datatypes.inl x => F x
                 | Datatypes.inr x => G x
                 end
     ; fmap := fun x y f =>
                 match x with
                 | Datatypes.inl x =>
                   match y with
                   | Datatypes.inl y => _
                   | Datatypes.inr y => False_rect _ _
                   end
                 | Datatypes.inr x =>
                   match y with
                   | Datatypes.inl y => False_rect _ _
                   | Datatypes.inr y => _
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
  destruct x, y; simpl in *;
  solve [ apply fmap_respects; auto | contradiction ].
Qed.
Next Obligation.
  destruct x; simpl in *; cat.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; try tauto;
  apply fmap_comp.
Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  proper.
  destruct x3, y1; simpl; auto; tauto.
Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  split; intros; simplify.
  - apply (e (Datatypes.inl x0) (Datatypes.inl y)).
  - apply (e (Datatypes.inr x0) (Datatypes.inr y)).
  - destruct x1; auto.
  - destruct x1, y.
    + apply e0; tauto.
    + tauto.
    + tauto.
    + apply e; tauto.
Qed.
