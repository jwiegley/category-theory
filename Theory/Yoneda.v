Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.
Require Import Category.Theory.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Definition Presheaves   (C : Category) := [C^op, Sets].
Definition Copresheaves (C : Category) := [C, Sets].

(** This is the Yoneda embedding. *)
Instance Yoneda `{C : Category} : C ⟶ [C^op, Sets] := CoHomFunctor C.

Program Instance YonedaLemma `(C : Category) `(F : C^op ⟶ Sets) {A : C} :

  [C^op, Sets] Hom(─,A) F ≅ F A

:= {
  to   := {| morphism := fun X => X A id |};
  from := {| morphism := fun Y : F A =>
             {| transform := fun X : C =>
                {| morphism := fun phi : A ~{ C^op }~> X =>
                     @fmap (C^op) Sets F A X phi Y |} |} |}
}.
Next Obligation.
  proper.
  destruct x, y; simpl in *.
  unfold nat_equiv in H.
  simpl in H.
  rewrite H; reflexivity.
Qed.
Next Obligation.
  proper.
  destruct F; simpl in *.
  apply fmap_respects, H.
Qed.
Next Obligation.
  autounfold.
  destruct F; simpl in *.
  symmetry.
  apply fmap_comp.
Qed.
Next Obligation.
  proper.
  destruct F; simpl in *.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  autounfold; simpl.
  destruct F; simpl in *.
  rewrite fmap_id; reflexivity.
Qed.
Next Obligation.
  autounfold.
  destruct F; simpl in *.
  unfold nat_equiv; simpl; intros.
  destruct x; simpl in *.
  autounfold in *.
  rewrite natural_transformation.
  apply transform; cat.
Qed.

Program Instance CovariantYonedaLemma `(C : Category) `(F : C ⟶ Sets) {A : C} :

  [C, Sets] Hom(A,─) F ≅ F A

:= {
  to   := {| morphism := fun X => X A id |};
  from := {| morphism := fun Y : F A =>
             {| transform := fun X : C =>
                {| morphism := fun phi : A ~{ C }~> X =>
                     @fmap C Sets F A X phi Y |} |} |}
}.
Next Obligation.
  proper.
  destruct x, y; simpl in *.
  unfold nat_equiv in H.
  simpl in H.
  rewrite H; reflexivity.
Qed.
Next Obligation.
  proper.
  destruct F; simpl in *.
  apply fmap_respects, H.
Qed.
Next Obligation.
  autounfold.
  destruct F; simpl in *.
  symmetry.
  apply fmap_comp.
Qed.
Next Obligation.
  proper.
  destruct F; simpl in *.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  autounfold; simpl.
  destruct F; simpl in *.
  rewrite fmap_id; reflexivity.
Qed.
Next Obligation.
  autounfold.
  destruct F; simpl in *.
  unfold nat_equiv; simpl; intros.
  destruct x; simpl in *.
  autounfold in *.
  rewrite natural_transformation.
  apply transform; cat.
Qed.
