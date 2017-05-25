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

Ltac reduce :=
  repeat match goal with
    | [ H : {p : _ & _ } |- _ ] => destruct H
    end;
  simpl; auto; try split; cat; simpl; cat.

(* At the moment this proof exhausts Coq's memory, bug #5551 *)

(*
Program Instance Comma_Iso {A : Category} {B : Category} {C : Category} :
  Proper (@Isomorphism Fun ==> @Isomorphism Fun ==> @Isomorphism Cat)
         (@Comma A B C).
Next Obligation.
  proper.
  transitivity (y ↓ x0). {
    destruct X; simpl in *.
    isomorphism.
    - functor; simpl; intros.
        reduce.
        exact (h ∘ transform[from] _).
      all:reduce.
    - functor; simpl; intros.
        reduce.
        exact (h ∘ transform[to] _).
      all:reduce.
    - constructive; reduce.
    - constructive; reduce.
  }
  destruct X0; simpl in *.
  isomorphism.
  - functor; simpl; intros.
      reduce.
      exact (transform[to] _ ∘ h).
    all:reduce.
  - functor; simpl; intros.
      reduce.
      exact (transform[from] _ ∘ h).
    all:reduce.
  - constructive; reduce.
  - constructive; reduce.
Qed.
*)
