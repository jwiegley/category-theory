Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.
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
Set Implicit Arguments.

(* The category of heterogenous relations on Coq objects. *)

(*
jww (2017-04-28): TODO
Program Instance Rel : Category := {
  ob      := @ob Coq;
  hom     := fun A B => A ~> Ensemble B;
  homset  := fun P Q =>
               {| equiv := fun f g => forall x y, f x y <-> g x y |};
  id      := Singleton;
  compose := fun X Y Z f g x z =>
               (exists y : Y, In Y (g x) y /\ In Z (f y) z)%type
}.
Next Obligation.
  equivalence.
  - apply H; assumption.
  - apply H; assumption.
  - apply H0, H; assumption.
  - apply H, H0; assumption.
Qed.
Next Obligation.
  proper;
  destruct H1 as [z [H1 H2]];
  exists z; firstorder.
Qed.
Next Obligation. all: firstorder; destruct H0; intuition. Qed.
Next Obligation. all: firstorder; destruct H; intuition. Qed.
Next Obligation. all: firstorder. Qed.

Program Instance Rel_Initial : @Initial Rel := {
  Zero := False;
  zero := fun _ _ => False_rect _ _
}.

(*
Program Instance Rel_Cartesian : @Cartesian Rel := {
  Prod := prod;
  fork := fun _ _ _ f g x => conj (f x) (g x);
  exl  := fun _ _ p => proj1 p;
  exr  := fun _ _ p => proj2 p
}.
Obligation 1. proper; autounfold in *; congruence. Qed.
Obligation 2.
  autounfold in *.
  split; intros.
    split; intros;
    apply proof_irrelevance.
  apply proof_irrelevance.
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
  fobj := fun X => X;
  fmap := fun X Y (f : X ~{Coq}~> Y) x y => In _ (Singleton _ (f x)) y
}.
Next Obligation.
  proper;
  destruct H0;
  rewrite <- H;
  constructor.
Qed.
Next Obligation.
  firstorder.
  destruct H, H0.
  constructor.
Qed.
*)
