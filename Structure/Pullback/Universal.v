Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Record Pullback_Universal {C : Category}
       {X Y Z : C} (f : X ~> Z) (g : Y ~> Z) := {
  pullback_obj : C;
  pullback_fst : pullback_obj ~> X;
  pullback_snd : pullback_obj ~> Y;

  pullback_commutes : f ∘ pullback_fst ≈ g ∘ pullback_snd;

  pullback_ump : ∀ Q (q1 : Q ~> X) (q2 : Q ~> Y),
    f ∘ q1 ≈ g ∘ q2 ->
      { h : Q ~> pullback_obj
      & (pullback_fst ∘ h ≈ q1) * (pullback_snd ∘ h ≈ q2)
      & ∀ (v : Q ~> pullback_obj),
          pullback_fst ∘ v ≈ q1 ->
          pullback_snd ∘ v ≈ q2 -> v ≈ h }
}.
