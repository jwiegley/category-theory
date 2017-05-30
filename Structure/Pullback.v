Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Unique.

Record Pullback_Universal {C : Category}
       {X Y Z : C} (f : X ~> Z) (g : Y ~> Z) := {
  pullback_obj : C;
  pullback_fst : pullback_obj ~> X;
  pullback_snd : pullback_obj ~> Y;

  pullback_commutes : f ∘ pullback_fst ≈ g ∘ pullback_snd;

  ump_pullbacks {Q} (q1 : Q ~> X) (q2 : Q ~> Y) :
    f ∘ q1 ≈ g ∘ q2 ->
    Unique (fun h : Q ~> pullback_obj =>
              (pullback_fst ∘ h ≈ q1) * (pullback_snd ∘ h ≈ q2))
}.
