Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.
Set Implicit Arguments.

Program Instance Cat : Category := {
  ob      := Category;
  hom     := @Functor;
  homset  := @functor_setoid;
  id      := @Identity;
  compose := @functor_comp
}.
Next Obligation.
  unfold functor_comp.
  intros ?? HA ?? HB ?; simpl.
  unfold functor_equiv in *.
  destruct (HA (x0 X0)) as [to [from [to_from from_to]]].
  destruct (HB X0) as [to0 [from0 [to_from0 from_to0]]].
  exists (fmap to0 ∘ to), (from ∘ fmap from0).
  rewrite <- comp_assoc.
  rewrite (comp_assoc to).
  rewrite to_from; cat.
  rewrite <- fmap_comp.
  rewrite to_from0; cat.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (fmap from0)).
  rewrite <- fmap_comp.
  rewrite from_to0; cat.
Qed.
Next Obligation.
  unfold functor_equiv; intros.
  unfold functor_comp; cat.
Qed.
Next Obligation.
  unfold functor_equiv; intros.
  unfold functor_comp; cat.
Qed.
Next Obligation.
  unfold functor_equiv; intros.
  unfold functor_comp; cat.
Qed.

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

Program Instance Ini : Category := {
  ob  := Empty_set;
  hom := fun _ _ => Empty_set;
  homset := fun _ _ => {| equiv := eq |}
}.
Next Obligation. destruct f. Qed.

Program Instance Init `(C : Category) : Ini ⟶ C.
Next Obligation. destruct H. Qed.
Next Obligation. destruct X. Qed.
Next Obligation. destruct X. Qed.
Next Obligation. destruct X. Qed.

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

Require Import Category.Structure.Initial.

Program Instance Cat_Initial : @Initial Cat := {
  Zero := Ini;
  zero := Init
}.
Next Obligation.
  unfold functor_equiv; intros; destruct X.
Qed.
