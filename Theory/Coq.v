Require Import Category.Lib.

(** Aggregator for the applied functional-programming layer over Coq types *)

(* This module re-exports the [Theory/Coq/] cluster, which develops the
   familiar Haskell-style type classes directly over Coq types (the "category
   of types") and connects each one to its categorical counterpart.  Importing
   this single module brings the whole applied-FP layer into scope.

   The exported modules fall into two groups.  The functor/applicative/monad
   tower, with traversals over it:

     - Functor       (fmap)            ↔ endofunctor on the category of types
     - Applicative   (pure/ap)         ↔ lax monoidal endofunctor
     - Monad         (ret/bind)        ↔ monad (endofunctor with unit/mult)
     - Foldable      (foldr/foldMap)
     - Traversable   (traverse)        ↔ traversal through an applicative

   And the algebraic structures and concrete instances those classes act on:

     - Semigroup     (associative <>)
     - Monoid        (Semigroup with unit)
     - Maybe, Either, Tuple, List, Map  (concrete functor/monad instances)

   The per-module [Proofs] submodules under [Theory/Coq/] are auxiliary and
   are deliberately not re-exported here. *)

(* Why the tower exists, and what a categorical footing buys

   nLab:  https://ncatlab.org/nlab/show/monad+(in+computer+science)
   nLab:  https://ncatlab.org/nlab/show/applicative+functor
   Paper: Moggi, "Notions of Computation and Monads", Information and
          Computation 93(1):55-92, 1991
   Paper: McBride, Paterson, "Applicative programming with effects",
          Journal of Functional Programming 18(1):1-13, 2008
   Paper: Jaskelioff, Rypáček, "An Investigation of the Laws of
          Traversals", MSFP 2012, EPTCS 76 (arXiv 1202.2919)

   Each class re-exported here was discovered as the programming shadow of
   a categorical structure that predates it.  The aggregator deliberately
   records those correspondences, so that the informal type-class laws
   acquire a precise categorical meaning rather than living only in
   documentation.

   The monad layer is the oldest.  Moggi recognized that the common
   computational effects — state, exceptions, nondeterminism,
   continuations, reader and writer — are modelled uniformly by a strong
   monad on a cartesian closed category: T x is the type of computations
   returning x, the unit is the effect-free computation, and the
   multiplication is sequential composition (Moggi, "Computational
   Lambda-Calculus and Monads", LICS 1989; "Notions of Computation and
   Monads", 1991).  Wadler carried this into program structure and made
   the Kleisli-triple presentation familiar, whence the return and bind
   that [Monad] presents as [ret] and [bind] (Wadler, "The Essence of
   Functional Programming", POPL 1992; "Monads for Functional
   Programming", Marktoberdorf 1992).

   Applicative functors arrived later and from the other direction.
   McBride and Paterson coined the "idiom" — an abstraction weaker than a
   monad, and for that reason more widely applicable — gave it [pure] and
   [ap], and closed their paper by naming the structure: an applicative is
   a lax monoidal functor equipped with a tensorial strength (McBride,
   Paterson, 2008; nLab).  Over a closed symmetric monoidal base [pure] is
   the unit and [liftA2] the laxator, so the four applicative laws are
   lax-monoidal coherence.  Structure/Monoidal.v is the semantic anchor,
   Functor/Applicative.v the law-bearing counterpart, and Functor/Strong.v
   the strength that recovers [ap] from the laxator.

   Traversals were named in the same paper — a [Traversable] functor
   distributes over every applicative — but stated no laws.  Gibbons and
   Oliveira read [traverse] as the Iterator pattern, one combinator that
   maps and accumulates at once, gave the first axioms, and exposed bad
   traversals that skip or duplicate elements (Gibbons, Oliveira, "The
   Essence of the Iterator Pattern", JFP 2009).  Jaskelioff and Rypáček
   then settled the account with three laws — naturality in the
   applicative, unitarity, linearity — that hold for the finitary
   containers, the largest known class of traversable functors, and that
   rule out the bad traversals (Jaskelioff, Rypáček, 2012).  Those three
   laws are what Functor/Traversable.v carries and [traverse] here states
   without proof.

   That the three classes even form a tower was itself settled late.
   [Functor] before [Applicative] before [Monad] became a superclass
   requirement only in GHC 7.10, with the Applicative-Monad Proposal of
   2015; before it the identities relating the layers — [fmap] with liftM,
   [pure] with return, [ap] with the monad's own ap — went unstated, and
   this cluster is organized along that same settled chain (HaskellWiki,
   "Functor-Applicative-Monad Proposal").

   The categorical footing is what makes the correspondences carry weight.
   Because the language can neither state nor enforce the laws, a lawless
   [Applicative] or [Traversable] allows nonsense instances, the bad
   traversals among them; routing each class through its monoidal or
   distributive-law semantics is what forbids those instances, and the
   law-bearing modules under Functor/ carry the coherence proofs the
   classes here only assert.  The remaining exports supply the base and
   the witnesses.  [Semigroup] and [Monoid] are the monoid object of
   Theory/Algebra/Monoid.v specialized to (Set, ×), over which
   [Foldable]'s [foldr] is the list catamorphism — the unique monoid
   homomorphism out of the free monoid — realized through
   Instance/Coq/Lists.v and Theory/Recursion.v, while
   Instance/Coq/Applicative.v and Instance/Coq/Monad.v exhibit the bridge
   as honest categorical instances over the Coq-types category. *)

Require Export Category.Theory.Coq.Applicative.
Require Export Category.Theory.Coq.Either.
Require Export Category.Theory.Coq.Foldable.
Require Export Category.Theory.Coq.Functor.
Require Export Category.Theory.Coq.List.
Require Export Category.Theory.Coq.Map.
Require Export Category.Theory.Coq.Maybe.
Require Export Category.Theory.Coq.Monad.
Require Export Category.Theory.Coq.Monoid.
Require Export Category.Theory.Coq.Semigroup.
Require Export Category.Theory.Coq.Traversable.
Require Export Category.Theory.Coq.Tuple.
