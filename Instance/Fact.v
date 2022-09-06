Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(* The factorization category (also called the interval category) Fact(f) of a
   morphism f in a category C is a way of organizing its binary factorizations
   f=p∘q into a category.

   The objects of Fact(f) are factorizations:

      X   →f   Y
      p1↘   ↗p2
          D

   so that f = p2∘p1, and a morphism from (p1,D,p2) to (q1,E,q2) is a morphism
   h:D→E making everything in sight commute. There’s an obvious projection
   functor P(f) : Fact(f) ⟶ C

   which maps (p1,D,p2) to D and (p1,D,p2)→(q1,E,q2) to h.
*)

Program Definition Fact `(f : x ~{C}~> y) : Category := {|
  obj := ∃ d (p1 : x ~> d) (p2 : d ~> y), f ≈ p2 ∘ p1;
  hom := fun x y => `1 x ~> `1 y;
  id  := fun x => id[`1 x];
  compose := fun _ _ _ => compose
|}.

Program Definition Fact_Proj `(f : x ~{C}~> y) : Fact f ⟶ C := {|
  fobj := fun x => `1 x
|}.
