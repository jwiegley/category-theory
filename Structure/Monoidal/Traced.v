Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section TracedMonoidal.

Context {C : Category}.

Class TracedMonoidal := {
  traced_is_symmetric : @SymmetricMonoidal C;

  trace {x y u} : x ⨂ u ~> y ⨂ u → x ~> y;

  trace_natural_in_x {x x' y u} {f : x ⨂ u ~> y ⨂ u} {g : x' ~> x} :
    trace (f ∘ g ⨂ id) ≈ trace f ∘ g;
  trace_natural_in_y {x y y' u} {f : x ⨂ u ~> y ⨂ u} {g : y ~> y'} :
    trace (g ⨂ id ∘ f) ≈ g ∘ trace f;
  trace_natural_in_u {x y u u'} {f : x ⨂ u ~> y ⨂ u'} {g : u' ~> u} :
    trace (id ⨂ g ∘ f) ≈ trace (f ∘ id ⨂ g);

  vanishing_unit {x y} {f : x ~> y} :
    trace (unit_right⁻¹ ∘ f ∘ unit_right) ≈ f;
  vanishing_tensor {x y u v} {f : x ⨂ (u ⨂ v) ~> y ⨂ (u ⨂ v)} :
    trace f ≈ trace (trace (tensor_assoc⁻¹ ∘ f ∘ tensor_assoc));

  superposing {a b c u} {f : a ⨂ u ~> b ⨂ u} :
    trace (tensor_assoc⁻¹ ∘ id[c] ⨂ f ∘ tensor_assoc)
      ≈ id[c] ⨂ trace f;

  yanking {x} : trace braid ≈ id[x];
}.
#[export] Existing Instance traced_is_symmetric.

Context `{TracedMonoidal}.

End TracedMonoidal.
