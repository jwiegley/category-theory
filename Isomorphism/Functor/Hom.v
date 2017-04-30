Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Natural.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Nat.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Presheaves   (C : Category) := [C^op, Sets].
Definition Copresheaves (C : Category) := [C, Sets].

(** This is the Yoneda embedding. *)
Instance Yoneda `{C : Category} : C ⟶ [C^op, Sets] := CoHomFunctor C.

Program Instance Yoneda_Lemma `(C : Category) `(F : C^op ⟶ Sets) {A : C} :
  [C^op, Sets] Hom(─,A) F ≅ F A := {
  to   := {| morphism := fun X => X A id |};
  from := {| morphism := fun Y : F A =>
             {| transform := fun X : C =>
                {| morphism := fun phi : A ~{ C^op }~> X =>
                     @fmap (C^op) Sets F A X phi Y |} |} |}
}.
Next Obligation.
  (* [to] preserves morphism equivalences. *)
  proper.
  destruct x, y; simpl in *.
  simplify equiv in X.
  apply X.
Qed.
Next Obligation.
  (* [transform] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply fmap_respects, X0.
Qed.
Next Obligation.
  (* The action of [transform] is natural. *)
  autounfold.
  destruct F; simpl in *.
  symmetry.
  simplify equiv; intros.
  apply fmap_comp.
Qed.
Next Obligation.
  (* [from] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  simplify equiv; intros.
  simplify equiv; intros.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  (* The result of [from] respects the laws of the functor category. *)
  autounfold; simpl.
  destruct F; simpl in *.
  simplify equiv; intros.
  apply fmap_id.
Qed.
Next Obligation.
  (* The result of [from] preserves morphism equivalences. *)
  autounfold.
  simplify equiv; intros.
  destruct F, x; simpl in *; intros.
  autounfold in *.
  simplify equiv in all; intros.
  simplify equiv; intros.
  rewrite natural_transformation.
  apply transform; cat.
Qed.

Program Instance Covariant_Yoneda_Lemma `(C : Category) `(F : C ⟶ Sets) {A : C} :
  [C, Sets] Hom(A,─) F ≅ F A := {
  to   := {| morphism := fun X => X A id |};
  from := {| morphism := fun Y : F A =>
             {| transform := fun X : C =>
                {| morphism := fun phi : A ~{ C }~> X =>
                     @fmap C Sets F A X phi Y |} |} |}
}.
Next Obligation.
  (* [to] preserves morphism equivalences. *)
  proper.
  destruct x, y; simpl in *.
  simplify equiv in X.
  apply X.
Qed.
Next Obligation.
  (* [transform] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply fmap_respects, X0.
Qed.
Next Obligation.
  (* The action of [transform] is natural. *)
  autounfold.
  destruct F; simpl in *.
  symmetry.
  simplify equiv; intros.
  apply fmap_comp.
Qed.
Next Obligation.
  (* [from] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  simplify equiv; intros.
  simplify equiv; intros.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  (* The result of [from] respects the laws of the functor category. *)
  autounfold; simpl.
  destruct F; simpl in *.
  simplify equiv; intros.
  apply fmap_id.
Qed.
Next Obligation.
  (* The result of [from] preserves morphism equivalences. *)
  autounfold.
  simplify equiv; intros.
  destruct F, x; simpl in *; intros.
  autounfold in *.
  simplify equiv in all; intros.
  simplify equiv; intros.
  rewrite natural_transformation.
  apply transform; cat.
Qed.
