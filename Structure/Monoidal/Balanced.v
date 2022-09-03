Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section BalancedMonoidal.

Context {C : Category}.

Class BalancedMonoidal := {
  balanced_is_braided : @BraidedMonoidal C;

  twist {x} : x ≅ x;
  twist_natural : natural (@twist);

  balanced_to : to (@twist I) ≈ id;
  balanced_from : from (@twist I) ≈ id;

  balanced_to_commutes {x y} :
    braid ∘ twist ⨂ twist ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist;

  balanced_from_commutes {x y} :
    braid⁻¹ ∘ twist⁻¹ ⨂ twist⁻¹ ∘ braid⁻¹
      << x ⨂ y ~~> x ⨂ y >>
    twist⁻¹;
}.
#[export] Existing Instance balanced_is_braided.

End BalancedMonoidal.
