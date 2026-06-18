Require Import Category.Lib.
Require Import Category.Theory.Coq.Semigroup.

Generalizable All Variables.

(** The Monoid type class (mempty/mappend), with its categorical reading *)

(* nLab: https://ncatlab.org/nlab/show/monoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid

   FP reading.  A monoid (in the Haskell sense) is a type [m] with an
   associative binary operation [mappend] (Haskell's [(<>)], here written
   [⊗] and inherited from the [Semigroup] superclass) together with a unit
   element [mempty] (Haskell's [mempty]).  It is lawful when [⊗] is
   associative and [mempty] is a two-sided identity:
   [mempty ⊗ x ≈ x] and [x ⊗ mempty ≈ x].  A [Monoid] is thus exactly a
   [Semigroup] (see Semigroup.v) that additionally provides the unit; like
   [Semigroup], [Functor], and [Foldable] in this directory this class is
   ops-only, carrying [mempty] but not the laws, so any [m : Type] with an
   associative [⊗] and a unit is an instance and the monoid laws are stated
   in prose rather than enforced.

   Categorical reading.  A monoid is a set with an associative binary
   operation and a unit, i.e. the hom-set of a one-object category:
   composition is [⊗], the identity arrow is [mempty], and the category laws
   are exactly associativity and the unit laws.  Equivalently it is a monoid
   object in the cartesian monoidal category of sets — internalizing the same
   data and laws in any monoidal category V yields a monoid object in V.

   This is the FP/Haskell-style monoid type class on a Coq type, and is
   DISTINCT from Theory/Algebra/Monoid.v, which defines the monoid OBJECT
   internal to an arbitrary monoidal category (an object X with morphisms
   mu : X ⨂ X ~> X and eta : I ~> X).  The present file is the special case
   of that notion in (Set, ×): a monoid object in Set is an ordinary monoid,
   and that ordinary monoid is what this class describes. *)

Class Monoid `{Semigroup m} := {
  mempty : m                   (* the unit element, Haskell's [mempty] *)
}.

Arguments Monoid m {_}.
