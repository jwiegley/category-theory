Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The thin category of a preorder (proset) *)

(* nLab: https://ncatlab.org/nlab/show/preorder
   nLab: https://ncatlab.org/nlab/show/thin+category
   Wikipedia: https://en.wikipedia.org/wiki/Preorder

   Any preordered set (a "proset": a set [A] with a reflexive and transitive
   relation [R], not necessarily antisymmetric) forms a category. Its objects
   are the elements of [A], and there is a (unique) morphism [x ~> y] exactly
   when [R x y] holds: identities come from reflexivity and composition from
   transitivity. See also [Ord], for the category of preordered sets (where
   the prosets are the objects, and morphisms are monotone mappings).

   Because antisymmetry is not required, distinct objects [x] and [y] may be
   isomorphic (when both [R x y] and [R y x] hold) without being equal; this
   is precisely what distinguishes a proset from a poset (see Instance/Poset.v,
   which adds antisymmetry). The resulting category is "thin": any two parallel
   morphisms are equal, so each hom-set has at most one element.

   Wikipedia: "A category with at most one morphism from any object X to any
   other object Y is a preorder. Such categories are called thin. In this
   sense, categories 'generalize' preorders by allowing more than one relation
   between objects: each morphism is a distinct (named) preorder relation." *)

Program Definition Proset {A : Type} {R : relation A} (P : PreOrder R) :
  Category := {|
  obj     := A;
  hom     := R;
  (* Since there can be at most one arrow between any two objects, multiple
     arrows of the same type are equal. *)
  homset  := fun A B => {| Setoid.equiv := fun _ _ => True |};
  id      := fun x => @reflexivity A R (@PreOrder_Reflexive A R P) x;
  compose := fun x y z f g =>
    @transitivity A R (@PreOrder_Transitive A R P) x y z g f
|}.

(* The typical example found in Category Theory theories and lectures is ≤. *)

Definition LessThanEqualTo_Category : Category :=
  @Proset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder.
