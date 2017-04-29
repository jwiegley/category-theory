Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cocartesian.
Require Export Category.Construction.Coproduct.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance Cat_Cocartesian : @Cocartesian Cat := {
  Coprod := @Coproduct;
  merge := fun _ _ _ F G =>
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
  inl := fun _ _ =>
            {| fobj := Datatypes.inl
             ; fmap := fun _ _ => _ |};
  inr := fun _ _ =>
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
  destruct X, Y, Z; simpl in *; try tauto;
  apply fmap_comp.
Qed.
Next Obligation.
  proper.
  constructive.
  all:swap 2 3.
  - simpl; intros.
    destruct X2.
      apply X0.
    apply X1.
  - simpl; intros.
    destruct X2.
      apply X0.
    apply X1.
  - simpl; intros.
    destruct X2, Y0; simpl;
    try contradiction;
    apply natural_transformation.
  - simpl; intros.
    destruct X2, Y0; simpl;
    try contradiction;
    apply natural_transformation.
  - simplify equiv; intros.
    destruct A; simpl.
      destruct X0, to, from; simpl.
      simplify equiv in iso_to_from.
      apply iso_to_from.
    destruct X1, to, from; simpl.
    simplify equiv in iso_to_from.
    apply iso_to_from.
  - simplify equiv; intros.
    destruct A; simpl.
      destruct X0, to, from; simpl.
      simplify equiv in iso_from_to.
      apply iso_from_to.
    destruct X1, to, from; simpl.
    simplify equiv in iso_from_to.
    apply iso_from_to.
Qed.
Next Obligation.
  simpl; split; intros.
  { destruct X0; simpl in *.
    split.
    { constructive.
      all:swap 2 3.
      - apply to.
      - destruct from; simpl in *.
        apply (transform (Datatypes.inl X0)).
      - simpl; intros.
        destruct to; simpl in *.
        apply (natural_transformation (Datatypes.inl X0) (Datatypes.inl Y0)).
      - simpl; intros.
        destruct from; simpl in *.
        apply (natural_transformation (Datatypes.inl X0) (Datatypes.inl Y0)).
      - simplify equiv in all; intros.
        apply (iso_to_from (Datatypes.inl A)).
      - simplify equiv in all; intros.
        apply (iso_from_to (Datatypes.inl A)).
    }
    { constructive.
      all:swap 2 3.
      - apply to.
      - destruct from; simpl in *.
        apply (transform (Datatypes.inr X0)).
      - simpl; intros.
        destruct to; simpl in *.
        apply (natural_transformation (Datatypes.inr X0) (Datatypes.inr Y0)).
      - simpl; intros.
        destruct from; simpl in *.
        apply (natural_transformation (Datatypes.inr X0) (Datatypes.inr Y0)).
      - simplify equiv in all; intros.
        apply (iso_to_from (Datatypes.inr A)).
      - simplify equiv in all; intros.
        apply (iso_from_to (Datatypes.inr A)).
    }
  }
  { destruct X0.
    destruct c, c0.
    simpl in *.
    constructive.
    all:swap 2 3.
    - destruct X0; simpl.
        apply to.
      apply to0.
    - destruct X0; simpl.
        apply from.
      apply from0.
    - simpl; intros.
      destruct X0, Y0; simpl;
      try contradiction;
      destruct to, to0; simpl in *.
        apply natural_transformation.
      apply natural_transformation0.
    - simpl; intros.
      destruct X0, Y0; simpl;
      try contradiction;
      destruct from, from0; simpl in *.
        apply natural_transformation.
      apply natural_transformation0.
    - simplify equiv in all; intros.
      destruct A; simpl.
        apply iso_to_from.
      apply iso_to_from0.
    - simplify equiv in all; intros.
      destruct A.
        apply iso_from_to.
      apply iso_from_to0.
  }
Qed.
