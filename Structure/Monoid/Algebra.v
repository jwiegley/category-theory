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

Class MonoidAlg (A : Type) `{Setoid A} := {
  mon_zero : A;
  mon_mult : A -> A -> A;
  mon_mult_respects : Proper (equiv ==> equiv ==> equiv) mon_mult;
  mon_zero_left  (x : A) : mon_mult mon_zero x = x;
  mon_zero_right (x : A) : mon_mult x mon_zero = x;
  mon_assoc (x y z : A) : mon_mult (mon_mult x y) z = mon_mult x (mon_mult y z)
}.

Program Instance Classical_Monoid (A : Type) `{Setoid A} `{MonoidAlg A} :
  @Monoid Sets InternalProduct_Monoidal {| carrier := A |} := {
  mempty  := {| morphism := fun _ => mon_zero |};
  mappend := {| morphism := fun p => mon_mult (fst p) (snd p) |}
}.
Next Obligation.
  proper; simpl in *.
  destruct H1.
  rewrite X, H2.
  reflexivity.
Qed.
Next Obligation. rewrite mon_zero_left; reflexivity. Qed.
Next Obligation. rewrite mon_zero_right; reflexivity. Qed.
Next Obligation. rewrite mon_assoc; reflexivity. Qed.
