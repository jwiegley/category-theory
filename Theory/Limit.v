Require Import Category.Lib.
Require Export Category.Theory.Cone.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Limit.

Context `{J : Category}.
Context `{C : Category}.
Context `{F : J ⟶ C}.

Class Limit := {
  lim : Cone;

  ump_limits : ∀ N : Cone,
    exists! u : N ~> lim, vertex_map[lim] ∘ u ≈ @vertex_map _ _ _ N lim
}.

End Limit.
