Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Unique.
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
  Lim :> Cone F;

  ump_limits : ∀ N : Cone F, ∃! u : N ~> Lim, ∀ X : J,
    vertex_map[Lim] ∘ u ≈ @vertex_map _ _ _ N X
}.

Arguments Limit {_ _} F%functor.
Arguments Lim {_ _} F%functor {_}.

Coercion limit_ob `(F : J ⟶ C) (L : Limit F) := @Lim _ _ _ L.

Require Import Category.Construction.Opposite.

Definition Colimit `(F : J ⟶ C) := Limit (F^op).

Definition Colim `(F : J ⟶ C) `{C : Colimit F} := @Lim _ _ _ C.
