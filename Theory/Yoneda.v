Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.
Require Import Category.Theory.Bifunctor.
Require Import Category.Construct.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Definition Presheaves   (C : Category) := [C^op, Sets].
Definition Copresheaves (C : Category) := [C, Sets].

Program Instance fobj_setoid `{C : Category} `{F : C ⟶ Sets} {A : C} :
  Setoid (F A).

(** This is the Yoneda embedding. *)
Instance Yoneda `{C : Category} : C ⟶ [C^op, Sets] := CoHomFunctor C.

Program Instance YonedaLemma `(C : Category) `(F : C ⟶ Sets) {A : C} :

  [C, Sets] Hom(A,─) F ≅ F A

:= {
  to   := {| morphism := fun X => X A id |};
  from := {| morphism := fun Y : F A =>
             {| transform := fun X : C =>
                {| morphism := fun phi : A ~{ C }~> X =>
                     @fmap C Sets F A X phi Y |} |} |}
}.
Next Obligation.
  repeat intro.
  destruct x, y; simpl in *.
  unfold nat_equiv in X; simpl in X.
  rewrite X; reflexivity.
Defined.
Next Obligation.
  repeat intro.
  destruct F; simpl in *.
  apply fmap_respects.
  apply X0.
Defined.
Next Obligation.
  destruct F; simpl in *.
  unfold Basics.compose in *.
  rewrite <- fmap_comp.
  reflexivity.
Defined.
Next Obligation.
  repeat intro; simpl in *.
  destruct F; simpl in *.
  destruct (fmap A A0 x0); simpl.
  apply proper_morphism.
  assumption.
Defined.
Next Obligation.
  unfold Basics.compose; simpl.
  destruct F; simpl in *.
  rewrite fmap_id.
  reflexivity.
Defined.
Next Obligation.
  unfold Basics.compose; simpl.
  destruct F; simpl in *.
  unfold nat_equiv; simpl; intros.
  destruct x; simpl in *.
  unfold Basics.compose in *; simpl.
  rewrite natural_transformation.
  apply transform; cat.
Defined.

Program Instance CoonedaLemma `(C : Category) `(F : C^op ⟶ Sets) {A : C} :

  [C^op, Sets] Hom(─,A) F ≅ F A

:= {
  to   := {| morphism := fun X => X A id |};
  from := {| morphism := fun Y : F A =>
             {| transform := fun X : C =>
                {| morphism := fun phi : A ~{ C^op }~> X =>
                     @fmap (C^op) Sets F A X phi Y |} |} |}
}.
Next Obligation.
  repeat intro.
  destruct x, y; simpl in *.
  unfold nat_equiv in X; simpl in X.
  rewrite X; reflexivity.
Defined.
Next Obligation.
  repeat intro.
  destruct F; simpl in *.
  apply fmap_respects.
  apply X0.
Defined.
Next Obligation.
  destruct F; simpl in *.
  unfold Basics.compose in *.
  rewrite <- fmap_comp.
  reflexivity.
Defined.
Next Obligation.
  repeat intro; simpl in *.
  destruct F; simpl in *.
  destruct (fmap A A0 x0); simpl.
  apply proper_morphism.
  assumption.
Defined.
Next Obligation.
  unfold Basics.compose; simpl.
  destruct F; simpl in *.
  rewrite fmap_id.
  reflexivity.
Defined.
Next Obligation.
  unfold Basics.compose; simpl.
  destruct F; simpl in *.
  unfold nat_equiv; simpl; intros.
  destruct x; simpl in *.
  unfold Basics.compose in *; simpl.
  rewrite natural_transformation.
  apply transform; cat.
Defined.
