Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.Semicartesian.
Require Export Category.Structure.Monoidal.Relevance.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section CartesianMonoidal.

Context {C : Category}.

(* Wikipedia: "Cartesian monoidal categories have a number of special and
   important properties, such as the existence of diagonal maps (Δ) x : x → x
   ⨂ x and augmentations (e) x : x → I for any object x. In applications to
   computer science we can think of (Δ) as 'duplicating data' and (e) as
   'deleting' data. These maps make any object into a comonoid. In fact, any
   object in a cartesian monoidal category becomes a comonoid in a unique way.

   Moreover, one can show (e.g. Heunen-Vicary 12, p. 84) that any symmetric
   monoidal category equipped with suitably well-behaved diagonals and
   augmentations must in fact be cartesian monoidal." *)

Class CartesianMonoidal `{@Monoidal C} := {
  is_semicartesian :> @SemicartesianMonoidal C _;
  is_relevance     :> @RelevanceMonoidal C _;

  proj_left_diagonal  {X} : proj_left  ∘ diagonal ≈ id[X];
  proj_right_diagonal {X} : proj_right ∘ diagonal ≈ id[X];

  unit_left_twist  {X} : unit_left  ∘ @twist _ _ _ X I ≈ unit_right;
  unit_right_twist {X} : unit_right ∘ @twist _ _ _ I X ≈ unit_left
}.

End CartesianMonoidal.
