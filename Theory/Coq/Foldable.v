Require Import Category.Lib.

Generalizable All Variables.

(** The Foldable type class (foldr), with its categorical reading *)

(* Wikipedia: https://en.wikipedia.org/wiki/Fold_(higher-order_function)
   nLab: https://ncatlab.org/nlab/show/monoid

   No dedicated nLab or Wikipedia page exists for "Foldable": the Wikipedia
   "fold" page above covers the underlying right fold, and the monoid page is
   the closest categorical reference (see the categorical reading below).  The
   Haskell-level account of the class lives on the HaskellWiki / Wikibooks
   rather than in the Wikipedia main namespace
   (https://wiki.haskell.org/Foldable_and_Traversable).

   FP reading.  A foldable container (in the Haskell sense) is a type
   constructor [F : Type → Type] whose elements can be collapsed left-to-right
   into a single summary value.  The defining operation recorded here is the
   right fold
     [foldr : (x → y → y) → y → F x → y],
   which threads a combining function [x → y → y] and an initial value [y]
   through the contents of [F x] — exactly Haskell's
   [foldr :: (a → b → b) → b → t a → b], with the element supplied first to
   the combining step.  The other members of the Haskell class ([foldMap],
   [fold], [toList], [length], …) are all derivable from this one operation;
   in particular [foldMap f] is [foldr (mappend ∘ f) mempty] and [fold] is
   [foldMap id], mapping each element into a monoid and combining.

   Categorical reading.  Folding is the universal property of the free monoid.
   The canonical foldable container is the list functor [L : Type → Type],
   which is the free-monoid (free-monad) functor on the category of types:
   [L x = ∐ₙ xⁿ].  A right fold [foldr (⊗) e] over a list is precisely the
   unique monoid homomorphism out of the free monoid [L x] determined, by that
   universal property, by the choice of where to send generators together with
   a target monoid structure ([⊗], [e]); equivalently it is the structure map
   of an [L]-algebra, so [foldr] is the catamorphism (fold) for the list (or,
   in general, the underlying container) functor.  More precisely, the
   category of foldable functors is the slice over the free-monoid functor
   [L]: a [Foldable F] is a functor [F] equipped with a natural way to send
   each [F x] into the free monoid [L x] (its [toList]), after which any fold
   factors through that map into an arbitrary monoid.  The monoid page above
   gives the target structure; [mempty]/[mappend] (see Monoid.v, Semigroup.v)
   supply the [e]/[⊗] that a fold consumes.

   As is usual for these Coq/Haskell-style classes, this class is ops-only,
   like [Functor], [Semigroup], and [Monoid] in this directory: it carries the
   [foldr] operation but records no laws, so any [F] with such an operation is
   an instance, and any laws (e.g. agreement of [foldr]/[foldMap], or that
   [toList] is a monoid action) are stated in prose rather than enforced. *)

Class Foldable@{d c} {F : Type@{d} → Type@{c}} :=
  foldr : ∀ {x y : Type@{d}}, (x -> y -> y) -> y -> F x -> y.
                              (* combining step, seed, container, summary *)

Arguments Foldable : clear implicits.
