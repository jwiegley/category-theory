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

Section SemicartesianMonoidal.

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

End SemicartesianMonoidal.

Require Import Category.Structure.Terminal.

(* Wikipedia: "In any cartesian monoidal category, the terminal object is the
   tensor unit." *)

Program Definition SemicartesianMonoidal_Terminal `{@Monoidal C}
        `{@SemicartesianMonoidal C _} : @Terminal C := {|
  One := I;
  one := @eliminate _ _ _;
  one_unique := @unit_terminal _ _ _
|}.

Import EqNotations.

(* Likewise, any monoidal category whose terminal object is the unit object,
   is semicartesian monoidal. *)

Program Definition Terminal_SemicartesianMonoidal `{M : @Monoidal C}
        `{T : @Terminal C} (Heq : One = @I C M) :
  @SemicartesianMonoidal C _ := {|
  eliminate := fun X => rew Heq in one;
  unit_terminal := fun X f g =>
    _ (one_unique (rew <- Heq in f) (rew <- Heq in g))
|}.
Next Obligation.
  unfold eq_rect_r, eq_rect, eq_sym in x.
  destruct Heq.
  assumption.
Defined.
