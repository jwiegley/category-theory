Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

Program Definition _1 : Category := {|
  ob      := unit;
  hom     := fun _ _ => unit;
  homset  := fun _ _ => {| equiv := eq |};
  id      := fun _ => tt;
  compose := fun _ _ _ _ _ => tt
|}.

Notation "1" := _1 : category_scope.

Program Instance To_1 `(C : Category) : C ⟶ _1 := {
  fobj := fun _ => tt;
  fmap := fun _ _ _ => id
}.

Program Instance Cat_Terminal : @Terminal Cat := {
  One := _1;
  one := To_1
}.
Next Obligation.
  constructive; simplify; auto;
  destruct f, g; simpl;
  rewrite ?fmap_id, ?fmap_id0;
  reflexivity.
Qed.

Program Instance Select `{C : Category} (c : C) : _1 ⟶ C := {|
  fobj := fun _ => c;
  fmap := fun _ _ _ => id
|}.

Notation "one[ C ]" := (@one Cat _ C)
  (at level 9, format "one[ C ]") : object_scope.
