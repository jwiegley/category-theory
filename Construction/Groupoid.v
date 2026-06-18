Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** The core groupoid of a category C: its maximal sub-groupoid. *)

(* nLab: https://ncatlab.org/nlab/show/core
   nLab: https://ncatlab.org/nlab/show/groupoid
   Wikipedia: https://en.wikipedia.org/wiki/Groupoid

   A groupoid is a category in which every morphism is an isomorphism
   (invertible). Given a category C, its core is the maximal sub-groupoid:
   the same objects as C, but with only the isomorphisms of C as morphisms.
   Here [Groupoid C] realises that core. Its objects are @obj C; a morphism
   x ~> y is an isomorphism x ≅ y in C (hom := @Isomorphism C); the identity
   is iso_id and composition is iso_compose. Morphism equivalence is equivalence
   of isomorphisms (homset := @iso_setoid C), i.e. two isos agree when their
   `to` and `from` components agree under `≈` (see Theory.Isomorphism).

   The core construction is the underlying-groupoid functor and is right adjoint
   to the inclusion Grpd ↪ Cat: a functor out of a groupoid into C must send
   every morphism to an isomorphism, so it factors through the core. *)

Program Definition Groupoid (C : Category) : Category := {|
  obj     := @obj C;
  hom     := @Isomorphism C;
  homset  := @iso_setoid C;
  id      := @iso_id C;
  compose := @iso_compose C
|}.
