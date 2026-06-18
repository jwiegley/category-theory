Require Import Category.Lib.

Generalizable All Variables.

(** The Semigroup type class (mappend/⊗), with its categorical reading *)

(* nLab: https://ncatlab.org/nlab/show/semigroup
   Wikipedia: https://en.wikipedia.org/wiki/Semigroup

   FP reading.  A semigroup (in the Haskell sense) is a type [m] equipped with
   a binary operation [mappend : m → m → m] (Haskell's [(<>)], here written
   [⊗]).  It is lawful when [⊗] is associative: [(x ⊗ y) ⊗ z ≈ x ⊗ (y ⊗ z)].
   Unlike a monoid there is no unit element; a [Monoid] (see Monoid.v) is a
   semigroup that additionally provides [mempty].  This class is ops-only:
   like [Functor] and [Foldable] in this directory, it carries the operation
   but not the law, so any [m : Type] with an associative [⊗] is an instance,
   and the associativity law is stated in prose rather than enforced.

   Categorical reading.  A semigroup is a set with an associative binary
   operation, i.e. an associative magma (a magma being a set with an arbitrary
   binary operation, not necessarily associative).  Equivalently it is a
   semigroup object in the cartesian monoidal category of sets — internalizing
   the same data and law in any monoidal category V yields a semigroup object
   in V.  It is also the hom-set of a one-object semicategory (semigroupoid):
   composition there is exactly [⊗] and associativity is its sole law, with no
   identity required.  Adding a unit recovers a monoid (a one-object
   category). *)

Class Semigroup (m : Type) := {
  mappend : m -> m -> m       (* the associative binary operation, written [⊗] *)
}.

Arguments mappend {m _ } _ _.

Infix "⊗" := mappend (at level 40).
