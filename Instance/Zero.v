Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cat.

Generalizable All Variables.

#[local] Obligation Tactic :=
  intros; try match goal with [ H : Empty_set |- _ ] => inversion H end.

Program Definition _0 : Category := {|
  obj    := Empty_set;
  hom    := fun _ _ => Empty_set;
  homset := Morphism_equality
|}.

Notation "0" := _0 : category_scope.

#[export]
Program Instance From_0 `(C : Category) : 0 ⟶ C.
Next Obligation. destruct H. Defined.
Next Obligation. destruct x. Defined.
Next Obligation. destruct x. Qed.
Next Obligation. destruct x. Qed.

#[export]
Program Instance Cat_Initial : @Initial Cat := {
  terminal_obj := _0;
  one := From_0
}.
Next Obligation.
  constructive; try contradiction.
Qed.
