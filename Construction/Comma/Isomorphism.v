Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Comma.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance Comma_Iso {A : Category} {B : Category} {C : Category} :
  Proper (@Isomorphism Fun ==> @Isomorphism Fun ==> @Isomorphism Cat)
         (@Comma A B C).
Next Obligation.
  proper.
  transitivity (y ↓ x0). {
    destruct X; simpl in *.
    isomorphism; simpl; intros.
    - functor; simpl; intros.
      + destruct X.
        exists x1.
        exact (h ∘ transform[from] _).
      + destruct X, Y; auto.
      + abstract (destruct X, Y; auto).
      + abstract (destruct X; simpl; cat).
      + abstract (destruct X; simpl; cat).
    - functor; simpl; intros.
      + destruct X.
        exists x1.
        exact (h ∘ transform[to] _).
      + destruct X, Y; auto.
      + abstract (destruct X, Y; auto).
      + abstract (destruct X; simpl; cat).
      + abstract (destruct X; simpl; cat).
    - constructive; simpl; intros.
      + destruct X; simpl.
        exact (id, id).
      + abstract (destruct X, Y; simpl; split; cat).
      + destruct X; simpl; split; cat.
      + abstract (destruct X; simpl; split; cat).
      + abstract (destruct A0; simpl; split; cat).
      + abstract (destruct A0; simpl; split; cat).
    - constructive; simpl; intros.
      + destruct X; simpl.
        exact (id, id).
      + abstract (destruct X, Y; simpl; split; cat).
      + destruct X; simpl; split; cat.
      + abstract (destruct X; simpl; split; cat).
      + abstract (destruct A0; simpl; split; cat).
      + abstract (destruct A0; simpl; split; cat).
  }
  destruct X0; simpl in *.
  isomorphism; simpl; intros.
  - functor; simpl; intros.
    + destruct X0.
      exists x1.
      exact (transform[to] _ ∘ h).
    + destruct X0, Y; auto.
    + abstract (destruct X0, Y; auto).
    + abstract (destruct X0; simpl; cat).
    + abstract (destruct X0; simpl; cat).
  - functor; simpl; intros.
    + destruct X0.
      exists x1.
      exact (transform[from] _ ∘ h).
    + destruct X0, Y; auto.
    + abstract (destruct X0, Y; auto).
    + abstract (destruct X0; simpl; cat).
    + abstract (destruct X0; simpl; cat).
  - constructive; simpl; intros.
    + destruct X0; simpl.
      exact (id, id).
    + abstract (destruct X0, Y; simpl; split; cat).
    + destruct X0; simpl; split; cat.
    + abstract (destruct X0; simpl; split; cat).
    + abstract (destruct A0; simpl; split; cat).
    + abstract (destruct A0; simpl; split; cat).
  - constructive; simpl; intros.
    + destruct X0; simpl.
      exact (id, id).
    + abstract (destruct X0, Y; simpl; split; cat).
    + destruct X0; simpl; split; cat.
    + abstract (destruct X; simpl; split; cat).
    + abstract (destruct A0; simpl; split; cat).
    + abstract (destruct A0; simpl; split; cat).
Time Qed.
