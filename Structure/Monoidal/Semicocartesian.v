Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

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

(* jww (2017-06-02): Define this using the dual construction. *)

Class SemicocartesianMonoidal `{@Monoidal C} := {
  generate {x} : I ~> x;

  unit_initial {x} (f g : I ~> x) : f ≈ g;

  embed_left  {x y} : x ~> x ⨂ y := id ⨂ generate ∘ unit_right⁻¹;
  embed_right {x y} : y ~> x ⨂ y := generate ⨂ id ∘ unit_left⁻¹
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
  terminal_obj := @I C _;
  one := @generate _ _ _;
  one_unique := @unit_initial _ _ _
|}.

Import EqNotations.

(* Likewise, any monoidal category whose initial object is the unit object, is
   semicocartesian monoidal. *)

Program Definition Initial_SemicocartesianMonoidal `{M : @Monoidal C}
        `{T : @Initial C} (Heq : @initial_obj C T = @I C M) :
  @SemicocartesianMonoidal C _ := {|
  generate := fun x => _ (@zero C T x);
  unit_initial := fun x f g => _ (@zero_unique C T x) f g
|}.
Next Obligation. rewrite Heq in x0; apply x0. Defined.
