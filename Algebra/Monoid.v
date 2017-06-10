Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Export Category.Structure.Monoidal.Internal.Product.
Require Export Category.Structure.Monoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* ncatlab: "Classical monoids are of course just monoids in Set with the
   cartesian product." *)

(* jww (2017-06-02): Move this into an Algebra directory *)

Class Monoid (A : Type) `{Setoid A} := {
  mempty : A;
  mappend : A -> A -> A;

  mappend_respects : Proper (equiv ==> equiv ==> equiv) mappend;

  mempty_left  (x : A) : mappend mempty x === x;
  mempty_right (x : A) : mappend x mempty === x;

  mon_assoc (x y z : A) : mappend (mappend x y) z === mappend x (mappend y z)
}.

Program Instance Classical_Monoid (A : Type) `{Setoid A} `{Monoid A} :
  @MonoidObject Sets InternalProduct_Monoidal {| carrier := A |} := {
  mempty  := {| morphism := fun _ => mempty |};
  mappend := {| morphism := fun p => mappend (fst p) (snd p) |}
}.
Next Obligation.
  proper; simpl in *.
  destruct H1.
  rewrite X, H2.
  reflexivity.
Qed.
Next Obligation. rewrite mempty_left; reflexivity. Qed.
Next Obligation. rewrite mempty_right; reflexivity. Qed.
Next Obligation. rewrite mon_assoc; reflexivity. Qed.
