Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.Relevance.
Require Export Category.Structure.Monoidal.Braided.
Require Export Category.Structure.Monoidal.Symmetric.
Require Export Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section CartesianMonoidal.

Context {C : Category}.
Context `{@Monoidal C}.

(* Wikipedia: "Cartesian monoidal categories have a number of special and
   important properties, such as the existence of diagonal maps (Δ) x : x → x
   ⨂ x and augmentations (e) x : x → I for any object x. In applications to
   computer science we can think of (Δ) as 'duplicating data' and (e) as
   'deleting' data. These maps make any object into a comonoid. In fact, any
   object in a cartesian monoidal category becomes a comonoid in a unique way.

   Moreover, one can show (e.g. Heunen-Vicary 12, p. 84) that any symmetric
   monoidal category equipped with suitably well-behaved diagonals and
   augmentations must in fact be cartesian monoidal." *)

Class CartesianMonoidal := {
  cartesian_is_semicartesian : SemicartesianMonoidal;
  cartesian_is_relevance     : RelevanceMonoidal;

  proj_left_diagonal  {x} : proj_left  ∘ diagonal ≈ id[x];
  proj_right_diagonal {x} : proj_right ∘ diagonal ≈ id[x];

  unit_left_braid  {x} : unit_left  ∘ @braid _ _ _ x I ≈ unit_right;
  unit_right_braid {x} : unit_right ∘ @braid _ _ _ I x ≈ unit_left
}.
#[export] Existing Instance cartesian_is_semicartesian.
#[export] Existing Instance cartesian_is_relevance.

Context `{CartesianMonoidal}.

Definition first  {x y z : C} (f : x ~> y) : x ⨂ z ~> y ⨂ z :=
  (f ∘ proj_left) △ proj_right.

Definition second  {x y z : C} (f : x ~> y) : z ⨂ x ~> z ⨂ y :=
  proj_left △ (f ∘ proj_right).

Definition split  {x y z w : C} (f : x ~> y) (g : z ~> w) :
  x ⨂ z ~> y ⨂ w :=
  (f ∘ proj_left) △ (g ∘ proj_right).

#[global] Program Instance first_respects {a b c : C} :
  Proper (equiv ==> equiv) (@first a b c).
Next Obligation.
  proper.
  unfold first.
  rewrites.
  reflexivity.
Qed.

#[global] Program Instance second_respects {a b c : C} :
  Proper (equiv ==> equiv) (@second a b c).
Next Obligation.
  proper.
  unfold second.
  rewrites.
  reflexivity.
Qed.

#[global] Program Instance split_respects {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@split a b c d).
Next Obligation.
  proper.
  unfold split.
  rewrites.
  reflexivity.
Qed.

End CartesianMonoidal.
