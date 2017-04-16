Require Import Category.Lib.
Require Export Category.Theory.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.
Set Implicit Arguments.

Program Instance Cat : Category := {
  hom     := @Functor;
  id      := @Identity;
  compose := @functor_comp
}.
Next Obligation.
  unfold functor_comp.
  (* jww (2017-04-13): Need to define functor equivalence. *)
Admitted.
Next Obligation.
  unfold functor_comp.
Admitted.
Next Obligation.
  unfold functor_comp.
Admitted.
Next Obligation.
  unfold functor_comp.
Admitted.
Next Obligation.
  unfold functor_comp.
Admitted.

Lemma fun_id_left `{C : Category} `{D : Category} `(F : C ⟶ D) :
  functor_comp Identity F = F.
Proof.
  destruct F.
  unfold functor_comp.
  simpl.
Admitted.

Lemma fun_id_right `(F : @Functor C D) : functor_comp F Identity = F.
Proof.
  destruct F.
  unfold functor_comp.
  simpl.
Admitted.

Program Instance Termi : Category := {
  ob      := unit;
  hom     := fun _ _ => unit;
  id      := fun _ => tt;
  compose := fun _ _ _ _ _ => tt
}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

(*
Program Instance Fini `(C : Category) : C ⟶ Termi := {
  fobj := fun _ => tt;
  fmap := fun _ _ _ => id
}.

Program Instance Ini : Category := {
  ob  := Empty_set;
  hom := fun _ _ => Empty_set
}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Instance Init `(C : Category) : Ini ⟶ C.
Next Obligation. destruct H. Defined.
Next Obligation. destruct f. Defined.
Next Obligation. destruct X. Qed.
Next Obligation. destruct f. Qed.

Require Import Category.Structure.Terminal.

Program Instance Cat_Terminal : @Terminal Cat := {
  One := Termi;
  one := Fini
}.
Next Obligation.
  destruct f as [F].
  destruct g as [G].
Admitted.

Require Import Category.Structure.Initial.

Program Instance Cat_Initial : @Initial Cat := {
  Zero := Ini;
  zero := Init
}.
Next Obligation.
  induction f as [F].
  induction g as [G].
Admitted.
*)
