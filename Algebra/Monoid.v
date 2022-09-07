Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

(* ncatlab: "Classical monoids are of course just monoids in Set with the
   cartesian product." *)

Class Monoid (A : Type) `{Setoid A} := {
  mempty : A;
  mappend : A → A → A;

  mappend_respects : Proper (equiv ==> equiv ==> equiv) mappend;

  mempty_left  (x : A) : mappend mempty x ≈ x;
  mempty_right (x : A) : mappend x mempty ≈ x;

  mon_assoc (x y z : A) : mappend (mappend x y) z ≈ mappend x (mappend y z)
}.

#[export]
Program Instance Classical_Monoid (A : Type) `{Setoid A} `{Monoid A} :
  @MonoidObject Sets CC_Monoidal {| carrier := A |} := {
  mempty  := {| morphism := fun _ => mempty |};
  mappend := {| morphism := fun p => mappend (fst p) (snd p) |}
}.
Next Obligation.
  proper; simpl in *.
  destruct H1.
  now rewrites.
Qed.
Next Obligation. rewrite mempty_left; reflexivity. Qed.
Next Obligation. rewrite mempty_right; reflexivity. Qed.
Next Obligation. rewrite mon_assoc; reflexivity. Qed.
