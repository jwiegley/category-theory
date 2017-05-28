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

Section SemicocartesianMonoidal.

Context {C : Category}.

(* A semi-cartesian monoidal category is basically an assertion that the unit
   is terminal. *)

Class SemicocartesianMonoidal `{@Monoidal C} := {
  generate {X} : I ~> X;

  unit_initial {X} (f g : I ~> X) : f ≈ g;

  embed_left  {X Y} : X ~> X ⨂ Y := id ⨂ generate ∘ unit_right⁻¹;
  embed_right {X Y} : Y ~> X ⨂ Y := generate ⨂ id ∘ unit_left⁻¹
}.

Corollary generate_comp `{@Monoidal C} `{@SemicocartesianMonoidal _} `{f : A ~> B} :
  f ∘ generate ≈ generate.
Proof. intros; apply unit_initial. Qed.

End SemicocartesianMonoidal.

Require Import Category.Structure.Initial.

(* Wikipedia: "In any cocartesian monoidal category, the initial object is the
   tensor unit." *)

Program Definition SemicocartesianMonoidal_Initial `{@Monoidal C}
        `{@SemicocartesianMonoidal C _} : @Initial C := {|
  One := @I C _;
  one := @generate _ _ _;
  one_unique := @unit_initial _ _ _
|}.

Import EqNotations.

(* Likewise, any monoidal category whose initial object is the unit object, is
   semicocartesian monoidal. *)

Program Definition Initial_SemicocartesianMonoidal `{M : @Monoidal C}
        `{T : @Initial C} (Heq : @Zero C T = @I C M) :
  @SemicocartesianMonoidal C _ := {|
  generate := fun X => _ (@zero C T X);
  unit_initial := fun X f g => _ (@zero_unique C T X) f g
|}.
Next Obligation. rewrite Heq in x; apply x. Defined.
