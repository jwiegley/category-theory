Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Unique.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Given a cospan in C:

           A         B
            \       /
           f \     / g
              \   /
                v
                C

   This can be thought of, set-theoretically, as the equation:

      ∀ a ∈ A, b ∈ B, f(b) = g(a)

   Which is a strong statement, requiring that every element of A agree with
   an element of B, through f and g. A pullback is a subset of the cartesian
   product of A and B, X ⊆ A × B, such that (a, b) ∈ X, where the following
   diagram commutes:

                 X
               /   \
           pA /     \ pB
             /       \
            A         B
             \       /
            f \     / g
               \   /
                 v
                 C

   An example of this is an INNER JOIN of two SQL tables, where f projects a
   primary key from A, and g a foreign key referencing A, so that X contains
   exactly those pairs of rows from A and B where id(A) = fkey(B).

   Wikipedia: "In fact, the pullback is the universal solution to finding a
   commutative square like this. In other words, given any commutative square
   [replacing in the above X with Y, and pA and pB with qA and qB] there is a
   unique function h : Y → X such that pA ∘ h ≈ qA and pB ∘ h ≈ qB." *)

(* Definition, in terms of morphisms and universal properties:

   Wikipedia: "A pullback of the morphisms f and g consists of an object P
   [Pull] and two morphisms p1 : P → X [pullback_fst] and p2 : P → Y
   [pullback_snd] for which the diagram

       P ---p2---> Y
       |           |
     p1|           |g
       |           |
       X ---f----> Z

   commutes. Moreover, the pullback (P, p1, p2) must be universal with respect
   to this diagram. That is, for any other such triple (Q, q1, q2) for which
   the following diagram commutes, there must exist a unique u : Q → P (called
   a mediating morphism) such that

    p1 ∘ u = q1,    p2 ∘ u = q2

   jww (2017-06-01): TODO
   As with all universal constructions, a pullback, if it exists, is unique up
   to isomorphism. In fact, given two pullbacks (A, a1, a2) and (B, b1, b2) of
   the same cospan X → Z ← Y, there is a unique isomorphism between A and B
   respecting the pullback structure." *)

Record Pullback {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) := {
  Pull : C;
  pullback_fst : Pull ~> x;
  pullback_snd : Pull ~> y;

  pullback_commutes : f ∘ pullback_fst ≈ g ∘ pullback_snd;

  ump_pullbacks : ∀ Q (q1 : Q ~> x) (q2 : Q ~> y), f ∘ q1 ≈ g ∘ q2
    -> ∃! u : Q ~> Pull, pullback_fst ∘ u ≈ q1 ∧ pullback_snd ∘ u ≈ q2
}.

Coercion pullback_ob {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z)
         (L : Pullback f g) := @Pull _ _ _ _ _ _ L.

Require Import Category.Construction.Opposite.

Definition Pushout {C : Category} {x y z : C^op} (f : x ~> z) (g : y ~> z) :=
  Pullback f g.

(* jww (2017-06-01): TODO *)
(* Wikipedia: "A weak pullback of a cospan X → Z ← Y is a cone over the cospan
   that is only weakly universal, that is, the mediating morphism u : Q → P
   above is not required to be unique." *)

(* jww (2017-06-01): TODO *)
(* Wikipedia: "The pullback is similar to the product, but not the same. One
   may obtain the product by "forgetting" that the morphisms f and g exist,
   and forgetting that the object Z exists. One is then left with a discrete
   category containing only the two objects X and Y, and no arrows between
   them. This discrete category may be used as the index set to construct the
   ordinary binary product. Thus, the pullback can be thought of as the
   ordinary (Cartesian) product, but with additional structure. Instead of
   "forgetting" Z, f, and g, one can also "trivialize" them by specializing Z
   to be the terminal object (assuming it exists). f and g are then uniquely
   determined and thus carry no information, and the pullback of this cospan
   can be seen to be the product of X and Y." *)

(* jww (2017-06-02): *)
(* Wikipedia: "... another way of characterizing the pullback: as the
   equalizer of the morphisms f ∘ p1, g ∘ p2 : X × Y → Z where X × Y is the
   binary product of X and Y and p1 and p2 are the natural projections. This
   shows that pullbacks exist in any category with binary products and
   equalizers. In fact, by the existence theorem for limits, all finite limits
   exist in a category with a terminal object, binary products and
   equalizers." *)
