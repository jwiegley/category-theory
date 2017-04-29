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

Program Instance _0 : Category := {
  ob  := Empty_set;
  hom := fun _ _ => Empty_set;
  homset := fun _ _ => {| cequiv := eq |}
}.

Program Instance From_0 `(C : Category) : _0 ⟶ C.

Program Instance Cat_Initial : @Initial Cat := {
  Zero := _0;
  zero := From_0
}.
Next Obligation.
  refine {| to   := _; from := _ |}; simpl.
  Unshelve.
  all:swap 1 3. refine {| transform := _ |}; simpl.
  all:swap 1 4. refine {| transform := _ |}; simpl.
  Unshelve.
  all:swap 1 5.
  all:swap 2 6.
  all:intros; try contradiction.
  all:simplify equiv; intros; contradiction.
Qed.
