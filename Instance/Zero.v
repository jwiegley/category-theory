Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** The initial (empty) category 0. *)

(* nLab:      https://ncatlab.org/nlab/show/empty+category
   nLab:      https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_small_categories
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   0 is the empty category: no objects and hence no morphisms.  Here the object
   type and every hom are [Empty_set], so the identity, composition, and all
   category laws hold vacuously (each obligation is discharged by [inversion] on
   the empty hypothesis); the hom-setoid is strict equality.

   0 is the initial object of Cat: for every category C there is a unique
   functor `¡ : 0 ⟶ C` ([From_0]), defined vacuously since there is nothing to
   map.  Dually, [_1] is the terminal/point category 1 (Instance/One.v). *)

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
Next Obligation. destruct X. Defined.
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
