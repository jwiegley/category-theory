Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.Semicartesian.
Require Export Category.Structure.Monoidal.Relevant.

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
  is_semicartesian : @SemicartesianMonoidal C _;
  is_relevance     : @RelevantMonoidal C _;

  proj_left_diagonal  {x} : proj_left  ∘ diagonal ≈ id[x];
  proj_right_diagonal {x} : proj_right ∘ diagonal ≈ id[x];

  unit_left_twist  {x} : unit_left  ∘ @twist _ _ _ x I ≈ unit_right;
  unit_right_twist {x} : unit_right ∘ @twist _ _ _ I x ≈ unit_left
}.
#[export] Existing Instance is_semicartesian.
#[export] Existing Instance is_relevance.

End CartesianMonoidal.
