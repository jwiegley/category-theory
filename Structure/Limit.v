Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.

Generalizable All Variables.

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
  limit_cone : Cone F;

  ump_limits : ∀ N : Cone F, ∃! u : N ~> limit_cone, ∀ x : J,
    vertex_map[limit_cone] ∘ u ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x
}.

Coercion limit_cone : Limit >-> Cone.

Require Import Category.Functor.Opposite.

Definition Colimit `(F : J ⟶ C) := Limit (F^op).
