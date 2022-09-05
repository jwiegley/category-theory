Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Initial.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

#[local] Obligation Tactic :=
  intros; try match goal with [ H : Empty_set |- _ ] => inversion H end.

Program Definition _0 : Category := {|
  obj    := Empty_set;
  hom    := fun _ _ => Empty_set;
  homset := Morphism_equality
|}.

Notation "0" := _0 : category_scope.

#[global]
Program Instance From_0 `(C : Category) : 0 ⟶ C.
Next Obligation. destruct H. Defined.
Next Obligation. destruct x. Defined.
Next Obligation. destruct x. Qed.
Next Obligation. destruct x. Qed.

#[global]
Program Instance Cat_Initial : @Initial Cat := {
  terminal_obj := _0;
  one := From_0
}.
Next Obligation.
  constructive; try contradiction.
Qed.
