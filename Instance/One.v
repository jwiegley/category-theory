Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.

Generalizable All Variables.

Program Definition _1@{o h p} : Category@{o h p} := {|
  obj     := poly_unit@{o};
  hom     := fun _ _ => poly_unit@{h};
  homset  := Morphism_equality@{o h p};
  id      := fun _ => ttt;
  compose := fun _ _ _ _ _ => ttt
|}.
Next Obligation.
  now destruct f.
Qed.
Next Obligation.
  now destruct f.
Qed.

Notation "1" := _1 : category_scope.

Notation "one[ C ]" := (@one Cat _ C)
  (at level 9, format "one[ C ]") : object_scope.

#[export]
Program Instance Erase `(C : Category) : C ⟶ 1 := {
  fobj := fun _ => ttt;
  fmap := fun _ _ _ => id
}.

#[export]
Program Instance Cat_Terminal : @Terminal Cat := {
  terminal_obj := _1;
  one := Erase
}.
Next Obligation.
  constructive; auto; try exact ttt.
  destruct (fmap[f] f0); auto.
Qed.
