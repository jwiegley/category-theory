Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Implicit Arguments.

Program Instance Termi : Category := {
  ob      := unit;
  hom     := fun _ _ => unit;
  homset  := fun _ _ => {| equiv := eq |};
  id      := fun _ => tt;
  compose := fun _ _ _ _ _ => tt
}.
Next Obligation. destruct f; reflexivity. Qed.
Next Obligation. destruct f; reflexivity. Qed.

Program Instance Fini `(C : Category) : C ⟶ Termi := {
  fobj := fun _ => tt;
  fmap := fun _ _ _ => id
}.

Require Import Category.Structure.Terminal.

Program Instance Cat_Terminal : @Terminal Cat := {
  One := Termi;
  one := Fini
}.
Next Obligation.
  econstructor; intros; cat.
  exists (@id Termi (f X)).
  eexists; split.
Qed.
