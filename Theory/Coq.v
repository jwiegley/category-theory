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
