Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Closed.
Require Export Category.Structure.Initial.
Require Export Category.Structure.Terminal.
Require Export Category.Instance.Coq.
Require Export Coq.Sets.Ensembles.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The category of heterogenous relations on Coq objects. *)

Program Definition Rel : Category := {|
  obj     := @obj Coq;
  hom     := fun A B => A ~> Ensemble B;
  homset  := fun P Q =>
               {| equiv := fun f g => forall x y, f x y ↔ g x y |};
  id      := Singleton;
  compose := fun x y z f g a b =>
               (exists e : y, In y (g a) e ∧ In z (f e) b)%type
|}.
Next Obligation.
  equivalence.
  - apply X; assumption.
  - apply X; assumption.
  - apply X0, X; assumption.
  - apply X, X0; assumption.
Qed.
Next Obligation.
  proper;
  destruct H as [w [H1 H2]];
  exists w; firstorder.
Qed.
Next Obligation.
  split; intros.
    destruct H as [? [? H2]].
    destruct H2; assumption.
  exists y0.
  intuition.
Qed.
Next Obligation.
  split; intros.
    destruct H as [? [H1 ?]].
    destruct H1; assumption.
  exists x0.
  intuition.
Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

Program Instance Rel_Initial : @Initial Rel := {
  One := False;
  one := fun _ _ => False_rect _ _
}.

(*
Program Instance Rel_Cartesian : @Cartesian Rel := {
  Prod := @Prod Coq _;
  fork := fun _ _ _ f g x y => f x (fst y) ∧ g x (snd y);
  exl  := fun _ _ p x => In _ (Singleton _ (fst p)) x;
  exr  := fun _ _ p x => In _ (Singleton _ (snd p)) x
}.
Next Obligation.
  proper.
  split; intros.
    destruct H.
    split; intros.
      apply X0; assumption.
    apply X1; assumption.
  destruct H.
  split; intros.
    apply X0; assumption.
  apply X1; assumption.
Qed.
Next Obligation.
  firstorder.
  - destruct H1.
    apply H, H0.
  - eexists (y, _).
    split.
      apply H; simpl.
      split.
        assumption.
      apply H.
Qed.

Program Instance Rel_Cocartesian : @Cocartesian Rel := {
  Coprod := or;
  merge := fun _ _ _ f g x =>
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  inl  := fun _ _ p => or_introl p;
  inr  := fun _ _ p => or_intror p
}.
Obligation 1. proper; autounfold in *; apply proof_irrelevance. Qed.
Obligation 2.
  autounfold in *.
  split; intros.
    split; intros;
    apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

Program Instance Rel_Closed : @Closed Rel _ := {
  Exp := Basics.impl;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.
Next Obligation. proper; autounfold in *; apply proof_irrelevance. Qed.
Next Obligation. proper; autounfold in *; apply proof_irrelevance. Qed.
Next Obligation. autounfold in *; apply proof_irrelevance. Qed.
Next Obligation. autounfold in *; apply proof_irrelevance. Qed.
Next Obligation. autounfold in *; apply proof_irrelevance. Qed.
*)

Definition some_number : nat ~{Rel}~> nat := fun x y => (x < y)%nat.

Program Instance Relation_Functor : Coq ⟶ Rel := {
  fobj := fun x => x;
  fmap := fun x y (f : x ~{Coq}~> y) x y => In _ (Singleton _ (f x)) y
}.
Next Obligation. proper; congruence. Qed.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  simplify; firstorder.
  destruct a, b; constructor.
Qed.
