Require Import Lib.
Require Export Category.
Require Export Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.
Set Implicit Arguments.

Program Definition functor_comp
  `{C : Category} `{D : Category} `{E : Category}
  (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E :=
  {| fobj := fun x => fobj (fobj x)
   ; fmap := fun _ _ f => fmap (fmap f) |}.
Next Obligation.
  intros ?? HA.
  rewrite HA; reflexivity.
Defined.
Next Obligation.
  intros.
  rewrite !fmap_id.
  reflexivity.
Qed.
Next Obligation.
  intros.
  rewrite !fmap_comp.
  reflexivity.
Qed.

Program Instance Cat : Category := {
  hom     := @Functor;
  id      := @Identity;
  compose := @functor_comp
}.
Obligation 1.
  unfold functor_comp.
  destruct f.
  (* jww (2017-04-13): Need to define functor equivalence. *)
Admitted.
Obligation 2.
  unfold functor_comp.
  destruct f; simpl.
Admitted.
Obligation 3.
  unfold functor_comp.
  destruct f; simpl.
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
Obligation 1. destruct f. reflexivity. Qed.
Obligation 2. destruct f. reflexivity. Qed.

Program Instance Fini `(C : Category) : C ⟶ Termi := {
  fobj := fun _ => tt;
  fmap := fun _ _ _ => id
}.

Program Instance Ini : Category := {
  ob  := Empty_set;
  hom := fun _ _ => Empty_set
}.
Obligation 4.
  destruct f.
Defined.

Program Instance Init `(C : Category) : Ini ⟶ C.

Obligation 1. destruct H. Defined.
Obligation 2. destruct f. Defined.
Obligation 3. destruct X. Qed.
Obligation 4. destruct f. Qed.

Require Import Terminal.

Program Instance Cat_Terminal : @Terminal Cat := {
  One := Termi;
  one := Fini
}.
Obligation 1.
  destruct f as [F].
  destruct g as [G].
Admitted.

Require Import Initial.

Program Instance Cat_Initial : @Initial Cat := {
  Zero := Ini;
  zero := Init
}.
Obligation 1.
  induction f as [F].
  induction g as [G].
Admitted.
