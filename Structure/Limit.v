Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cone.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Wikipedia: "Let F : J ⟶ C be a diagram of shape J in a category C. A cone
   to F is an object N of C together with a family ψX : N ⟶ F(X) of morphisms
   indexed by the objects X of J, such that for every morphism f : X ⟶ Y in J,
   we have F(f) ∘ ψX = ψY.

   "A limit of the diagram F : J ⟶ C is a cone (L, φ) to F such that for any
   other cone (N, ψ) to F there exists a unique morphism u : N ⟶ L such that
   φX ∘ u = ψX for all X in J.

   "One says that the cone (N, ψ) factors through the cone (L, φ) with the
   unique factorization u. The morphism u is sometimes called the mediating
   morphism." *)

Class Limit `(F : J ⟶ C) := {
  Lim : Cone F;

  (* This restates the fact that limits are terminal objects in the category
     of cones to F (which in turn is the comma category (Δ ↓ F)). *)
  limit_terminal {N : Cone F} : N ~> Lim;
  limit_unique {N : Cone F} (f : N ~> Lim) : limit_terminal ≈ f;

  ump_limits {N : Cone F} {X : J} :
    vertex_map[Lim] ∘ limit_terminal ≈ @vertex_map _ _ _ N X
}.

Arguments Limit {_ _} F%functor.
Arguments Lim {_ _} F%functor {_}.

Require Import Category.Construction.Opposite.

Definition Colimit `(F : J ⟶ C) := Limit (F^op).

Definition Colim `(F : J ⟶ C) `{C : Colimit F} := @Lim _ _ _ C.
