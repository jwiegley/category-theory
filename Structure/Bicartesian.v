Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

Section Bicartesian.

(* nLab: https://ncatlab.org/nlab/show/bicartesian+category
   Wikipedia: none-exists (the term appears only within related articles such
   as "Distributive category" and "Cartesian closed category")

   A bicartesian category is a category that is both cartesian and cocartesian:
   it has finite products (× with terminal unit 1) and finite coproducts (+ with
   initial unit 0), where the two structures need not coincide. (When they do
   coincide as biproducts the category is semiadditive: every semiadditive
   category is bicartesian, but not conversely.)

   This file does not introduce a [Bicartesian] class; the structure is simply
   the conjunction of [Cartesian] and [Cocartesian] in context, declared below.
   What it adds is [fork_merge], an interchange law relating the product pairing
   △ ([fork]) to the coproduct copairing ▽ ([merge]) — a fact available only
   when both structures are present. *)

Context {C : Category}.
Context `{@Cartesian C}.     (* finite products:   x × y, terminal 1 *)
Context `{@Cocartesian C}.   (* finite coproducts: x + y, initial  0 *)

(* Interchange of fork (△) and merge (▽): copairing two pairings equals pairing
   two copairings. Reading the four morphisms as the entries of a 2×2 matrix,
   both sides assemble the same morphism (x + w) ~> (y × z), so this is the
   "matrix transpose" / middle-four interchange of the bicartesian structure.
   The proof reduces the merge of forks to a fork of merges using [fork_comp]
   and [merge_comp], appealing to [fork_respects] both in C and dually in C^op. *)
Corollary fork_merge {x y z w : C}
          (f : x ~> y) (g : x ~> z) (h : w ~> y) (i : w ~> z) :
  (f △ g) ▽ (h △ i) ≈ (f ▽ h) △ (g ▽ i).
Proof.
  rewrite <- id_left.
  rewrite <- fork_exl_exr.
  rewrite <- fork_comp.
  apply fork_respects;
  rewrite <- merge_comp; cat;
  apply (@fork_respects (C^op)); cat.
Qed.

End Bicartesian.
