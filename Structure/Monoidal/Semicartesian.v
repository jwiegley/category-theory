Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoidal.

Context {C : Category}.

(* A semi-cartesian monoidal category is basically an assertion that the unit
   is terminal. *)

Class SemicartesianMonoidal `{@Monoidal C} := {
  eliminate {X} : X ~> I;

  unit_terminal {X} (f g : X ~> I) : f ≈ g;

  proj_left  {X Y} : X ⨂ Y ~> X := unit_right ∘ id ⨂ eliminate;
  proj_right {X Y} : X ⨂ Y ~> Y := unit_left  ∘ eliminate ⨂ id
}.

Corollary eliminate_comp `{@Monoidal C} `{@SemicartesianMonoidal _} `{f : A ~> B} :
  eliminate ∘ f ≈ eliminate.
Proof. intros; apply unit_terminal. Qed.

End Monoidal.

Require Import Category.Structure.Terminal.

(* Wikipedia: "In any cartesian monoidal category, the terminal object is the
   tensor unit." *)

Program Definition SemicartesianMonoidal_Terminal `{@Monoidal C}
        `{@SemicartesianMonoidal C _} : @Terminal C := {|
  One := I;
  one := @eliminate _ _ _;
  one_unique := @unit_terminal _ _ _
|}.
