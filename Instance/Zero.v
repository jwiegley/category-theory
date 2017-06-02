Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.Initial.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Local Obligation Tactic :=
  intros; try match goal with [ H : Empty_set |- _ ] => inversion H end.

Program Definition _0 : Category := {|
  ob  := Empty_set;
  hom := fun _ _ => Empty_set;
  homset := fun _ _ => {| equiv := eq |}
|}.

Notation "0" := _0 : category_scope.

Program Instance From_0 `(C : Category) : _0 ⟶ C.
Next Obligation. destruct H. Qed.
Next Obligation. destruct x. Qed.
Next Obligation. destruct x. Qed.
Next Obligation. destruct x. Qed.

Program Instance Cat_Initial : @Initial Cat := {
  One := _0;
  one := From_0
}.
Next Obligation.
  constructive; try contradiction.
Qed.
