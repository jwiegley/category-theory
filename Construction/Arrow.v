Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.

Generalizable All Variables.

(** The arrow category C^→ (also written Arr(C), C², or [2, C]). *)

(* nLab: https://ncatlab.org/nlab/show/arrow+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   The arrow category of C has as objects the morphisms of C and as morphisms
   the commuting squares of C: a morphism from (f : a₀ ~> a₁) to (g : b₀ ~> b₁)
   is a pair (u : a₀ ~> b₀, v : a₁ ~> b₁) with g ∘ u ≈ v ∘ f, i.e. the square

       a₀  --u-->  b₀
        |           |
       f            g           commute, i.e.  g ∘ u ≈ v ∘ f.
        v           v
       a₁  --v-->  b₁

   It is here defined as the comma category (Id[C] ↓ Id[C]) of the identity
   functor against itself (see Construction/Comma.v); taking S = T = Id[C] in
   the comma construction collapses its objects (a, b, h : S a ~> T b) to plain
   morphisms a ~> b of C and its morphisms to commuting squares as above.

   Equivalently the arrow category is the functor category [2, C], where 2 is
   the interval (walking-arrow) category {0 → 1}; the standard notations C^→,
   Arr(C), C², and [2, C] all denote this category. The domain and codomain
   functors C^→ ⟶ C are the comma projections comma_proj1 and comma_proj2 of
   Construction/Comma.v specialized to S = T = Id[C]. *)

Definition Arrow {C : Category} : Category := (Id[C] ↓ Id[C]).

Notation "C ⃗" := (@Arrow C) (at level 90) : category_scope.
