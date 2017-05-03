Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

Local Obligation Tactic :=
  intros; try match goal with [ H : Empty_set |- _ ] => inversion H end.

Program Instance _0 : Category := {
  ob  := Empty_set;
  hom := fun _ _ => Empty_set;
  homset := fun _ _ => {| equiv := eq |}
}.

Program Instance From_0 `(C : Category) : _0 ⟶ C.
Next Obligation. destruct H. Qed.
Next Obligation. destruct X. Qed.
Next Obligation. destruct X. Qed.
Next Obligation. destruct X. Qed.

Program Instance Cat_Initial : @Initial Cat := {
  Zero := _0;
  zero := From_0
}.
Next Obligation.
  constructive; try contradiction;
  intros; contradiction.
Qed.
