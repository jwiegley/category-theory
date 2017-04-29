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

Program Instance Proset `{C : Category} `{R : relation C} `(P : PreOrder C R) :
  Category := {
  ob      := C;
  hom     := R;
  homset  := fun A B => {| cequiv := proof_eq |};
  id      := fun X => @reflexivity C R (@PreOrder_Reflexive C R P) X;
  compose := fun X Y Z f g =>
               @transitivity C R (@PreOrder_Transitive C R P) X Y Z g f
}.
Next Obligation. apply proof_irrelevance. Qed.
Next Obligation. apply proof_irrelevance. Qed.
Next Obligation. apply proof_irrelevance. Qed.
