Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Import EqNotations.

(** * Discrete category *)

(* nLab: https://ncatlab.org/nlab/show/discrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Discrete_category

   A category is discrete when its only morphisms are the identity morphisms;
   equivalently, the hom-set `x ~> y` is a singleton when `x = y` and empty
   otherwise. The predicate [Discrete] expresses this directly: every morphism
   `f : x ~> y` forces its source and target to be equal (the witness `H : x =
   y`) and is then equal under `≈` to the identity transported along `H` (using
   the [EqNotations] `rew` for the dependent rewrite). This is the discrete
   *and* skeletal characterization. nLab notes that asking for object equality
   `x = y` rather than isomorphism violates the principle of equivalence — the
   caveat recorded in the [jww] note below; the equivalence-respecting variant
   would replace `x = y` with an isomorphism `x ≅ y`. A discrete category is
   the image of a set under the left adjoint, and the dual (codiscrete /
   indiscrete) construction is the further right adjoint; both adjunctions
   are now proved -- [Disc_Objects_Adjunction] (Instance/Cat/Objects.v) and
   [Objects_Indisc_Adjunction] (Instance/Indiscrete.v), composing as
   [adjoint_string]. The ambient is [Coq]/[StrictCat], NOT `Set ⟶ Cat`:
   [objects_not_functorial_over_Cat] refutes an objects functor on [Cat],
   and [disc_carrier_not_Sets_functor] refutes the [Sets] target. *)

(* A discrete category has no arrows except for identity morphisms. *)

Definition Discrete (C : Category) :=
  (* jww (2017-06-02): Equality is too much here. *)
  ∀ x y (f : x ~> y), ∃ H : x = y, f ≈ rew H in id.
