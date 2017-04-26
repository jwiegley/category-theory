Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Implicit Arguments.

Program Instance _1 : Category := {
  ob      := unit;
  hom     := fun _ _ => unit;
  homset  := fun _ _ => {| equiv := eq |};
  id      := fun _ => tt;
  compose := fun _ _ _ _ _ => tt
}.
Next Obligation. destruct f; reflexivity. Qed.
Next Obligation. destruct f; reflexivity. Qed.

Program Instance To_1 `(C : Category) : C ⟶ _1 := {
  fobj := fun _ => tt;
  fmap := fun _ _ _ => id
}.

Program Instance Cat_Terminal : @Terminal Cat := {
  One := _1;
  one := To_1
}.
Next Obligation.
  econstructor; intros; cat.
  exists (@id _1 (f X)).
  eexists; split.
Qed.

Program Instance Select `{C : Category} (c : C) : _1 ⟶ C := {|
  fobj := fun _ => c;
  fmap := fun _ _ _ => id
|}.
