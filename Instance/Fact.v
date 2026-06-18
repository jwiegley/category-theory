Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The factorization category Fact(f) of a morphism. *)

(* nLab:      https://ncatlab.org/nlab/show/factorization+category
   Wikipedia: https://en.wikipedia.org/wiki/Twisted_arrow_category

   The factorization category (also called the interval category) Fact(f) of a
   morphism f : x ~> y in a category C organizes the binary factorizations of f
   into a category.

   An object of Fact(f) is a factorization f = p2 ∘ p1 of f through an
   intermediate object d:

      x   --f-->   y
       p1↘       ↗p2
            d

   encoded as the dependent tuple (∃ d (p1 : x ~> d) (p2 : d ~> y), f ≈ p2 ∘ p1).
   A morphism from (p1, d, p2) to (q1, e, q2) is a morphism h : d ~> e of C
   making everything in sight commute, i.e. h ∘ p1 ≈ q1 and q2 ∘ h ≈ p2:

      x --p1--> d --p2--> y
                |
                h         h ∘ p1 ≈ q1   and   q2 ∘ h ≈ p2.
                v
      x --q1--> e --q2--> y

   Two such morphisms are equal exactly when their underlying C-morphisms are
   ≈, the two commuting proofs being irrelevant; identity is id (with the
   triangles holding by the unit laws) and composition is composition in C (the
   triangles for h ∘ h' following by associativity).

   Fact(f) always has an initial object, the factorization f = f ∘ id through x,
   and a terminal object, the factorization f = id ∘ f through y. There is an
   obvious projection functor P(f) : Fact(f) ⟶ C sending (p1, d, p2) to the
   intermediate object d and a mediating morphism h to itself in C. *)

Program Definition Fact `(f : x ~{C}~> y) : Category := {|
  obj := ∃ d (p1 : x ~> d) (p2 : d ~> y), f ≈ p2 ∘ p1;
  hom := fun x y =>
    ∃ h : `1 x ~> `1 y, h ∘ `1 (`2 x) ≈ `1 (`2 y)
                    ∧ `1 (`2 (`2 y)) ∘ h ≈ `1 (`2 (`2 x));
  homset := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id  := fun x => (id[`1 x]; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation.
  intros; simpl in *.
  split.
  - rewrite <- comp_assoc, e, e1; reflexivity.
  - rewrite comp_assoc, e2, e0; reflexivity.
Defined.

Program Definition Fact_Proj `(f : x ~{C}~> y) : Fact f ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ h => `1 h
|}.
