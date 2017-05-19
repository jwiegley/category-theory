Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Cone.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Limit.

Context `{J : Category}.
Context `{C : Category}.
Context `{F : J ⟶ C}.

(* Wikipedia:

   "Let F : J ⟶ C be a diagram of shape J in a category C. A cone to F is an
   object N of C together with a family ψX : N ⟶ F(X) of morphisms indexed by
   the objects X of J, such that for every morphism f : X ⟶ Y in J, we have
   F(f) ∘ ψX = ψY.

   "A limit of the diagram F : J ⟶ C is a cone (L, φ) to F such that for any
   other cone (N, ψ) to F there exists a unique morphism u : N ⟶ L such that
   φX ∘ u = ψX for all X in J.

   "One says that the cone (N, ψ) factors through the cone (L, φ) with the
   unique factorization u. The morphism u is sometimes called the mediating
   morphism."

   In this presentation, L = Lim, u = limit, and N is a universally quantified
   argument of the uniqueness and universal properties. *)

Class HasLimit := {
  Lim : Cone F;

  (* This just restates the fact that limits are terminal objects in the
     category of cones to F (which in turn is the comma category (Δ ↓ F)). *)
  limit {N : Cone F} : N ~> Lim;
  limit_unique {N : Cone F} (f g : N ~> Lim) : f ≈ g;

  ump_limits {N : Cone F} {X : J} :
    vertex_map[Lim] ∘ limit ≈ @vertex_map _ _ _ N X
}.

Set Transparent Obligations.

Global Program Definition Limit `{HasLimit} `{D : Category} : D ⟶ C := {|
  fobj := fun _ => @vertex  _ _ _ Lim
|}.

End Limit.

Arguments Limit {_ _} F {_ _}.
Arguments HasLimit {_ _} F.
