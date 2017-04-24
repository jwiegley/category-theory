Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Implicit Arguments.

Program Instance Ini : Category := {
  ob  := Empty_set;
  hom := fun _ _ => Empty_set;
  homset := fun _ _ => {| equiv := eq |}
}.

Program Instance Init `(C : Category) : Ini ⟶ C.

Require Import Category.Structure.Initial.

Program Instance Cat_Initial : @Initial Cat := {
  Zero := Ini;
  zero := Init
}.
