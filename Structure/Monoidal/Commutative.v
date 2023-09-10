Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section CommutativeMonoidal.

Context {C : Category}.
Context `{@SymmetricMonoidal C}.

Class CommutativeMonoidal := {
  commutative {x} : @braid _ _ x x ≈ id
}.

End CommutativeMonoidal.
