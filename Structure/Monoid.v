Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoid.

Context `{C : Category}.
Context `{@Monoidal C}.

Class Monoid (mon : C) := {
  mempty : I ~> mon;
  mappend : mon ⨂ mon ~> mon;

  (* I ⨂ mon ≈ mon, mon ⨂ I ≈ mon *)
  mempty_left : mappend ∘ bimap mempty id ≈ to (@unit_left C _ mon);
  mempty_right : mappend ∘ bimap id mempty ≈ to (@unit_right C _ mon);

  (* (mon ⨂ mon) ⨂ mon ≈ mon ⨂ (mon ⨂ mon) *)
  mappend_assoc :
    mappend ∘ bimap mappend id ≈ mappend ∘ bimap id mappend ∘ to tensor_assoc
}.

End Monoid.

Notation "mempty[ M ]" := (@mempty _ _ _ M)
  (at level 9, format "mempty[ M ]") : category_scope.
Notation "mappend[ M ]" := (@mappend _ _ _ M)
  (at level 9, format "mappend[ M ]") : category_scope.

(* ncatlab: "Classical monoids are of course just monoids in Set with the
   cartesian product." *)

Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Class MonoidAlg (A : Type) `{Setoid A} := {
  mon_zero : A;
  mon_mult : A -> A -> A;
  mon_mult_respects : Proper (equiv ==> equiv ==> equiv) mon_mult;
  mon_zero_left  (x : A) : mon_mult mon_zero x = x;
  mon_zero_right (x : A) : mon_mult x mon_zero = x;
  mon_assoc (x y z : A) : mon_mult (mon_mult x y) z = mon_mult x (mon_mult y z)
}.

(* jww (2017-05-13): TODO
Program Instance Classical_Monoid (A : Type) `{Setoid A} `{MonoidAlg A} :
  @Monoid Sets InternalProduct_Monoidal {| carrier := A |} := {
  mempty  := {| morphism := fun _ => mon_zero |};
  mappend := {| morphism := fun p => mon_mult (fst p) (snd p) |}
}.
Next Obligation.
  proper; simpl in *.
  destruct H1.
  rewrite x0, y0.
  reflexivity.
Qed.
Next Obligation. rewrite mon_zero_left; reflexivity. Qed.
Next Obligation. rewrite mon_zero_right; reflexivity. Qed.
Next Obligation. rewrite mon_assoc; reflexivity. Qed.
*)
