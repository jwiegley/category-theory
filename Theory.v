(** * Convenience umbrella: the core theory and basic structures.

   Re-exports a curated subset of the development — the foundational
   theory modules (categories, isomorphisms, functors, natural
   transformations, adjunctions) together with the elementary universal
   structures (cartesian/cocartesian/bicartesian, terminal, initial) —
   so that downstream files can [Require Import Category.Theory] for the
   common essentials rather than naming each module.  This is a
   hand-picked starting bundle, not an exhaustive export of [Theory/]. *)

Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Theory.Adjunction.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Bicartesian.
Require Export Category.Structure.Terminal.
Require Export Category.Structure.Initial.
