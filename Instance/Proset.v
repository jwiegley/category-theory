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

Require Import Coq.Logic.ProofIrrelevance.

(* Proof irrelevant equality. *)
Definition proof_eq {P : Prop} (x y : P) := (x = y)%type.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

(* Any pre-ordered set forms a category. See also [Ord], for the category of
   pre-ordered sets (where the sets are the objects, and morphisms are
   monotonic mappings.

   Wikipedia: "A category with at most one morphism from any object X to any
   other object Y is a preorder. Such categories are called thin. In this
   sense, categories 'generalize' preorders by allowing more than one relation
   between objects: each morphism is a distinct (named) preorder relation." *)

Program Definition Proset `{A : Type}
        `{R : relation A} `(P : PreOrder A R) :
  Category := {|
  ob      := A;
  hom     := R;
  homset  := fun A B => {| Setoid.equiv := proof_eq |};
  id      := fun X => @reflexivity A R (@PreOrder_Reflexive A R P) X;
  compose := fun X Y Z f g =>
               @transitivity A R (@PreOrder_Transitive A R P) X Y Z g f
|}.
Next Obligation. apply proof_irrelevance. Qed.
Next Obligation. apply proof_irrelevance. Qed.
Next Obligation. apply proof_irrelevance. Qed.
Next Obligation. apply proof_irrelevance. Qed.

(* The typical example found in Category Theory theories and lectures is ≤. *)

Definition LessThanEqualTo_Category : Category :=
  @Proset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder.
