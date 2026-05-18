Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(** * Compact closed categories

    A compact closed category is a symmetric monoidal category in which
    every object [X] has a (chosen) dual [X^*], with a unit
    [η_X : I ~> X^* ⨂ X] and counit [ε_X : X ⨂ X^* ~> I] satisfying the
    snake/triangle identities

        (ε ⨂ id) ∘ α⁻¹ ∘ (id ⨂ η) ≈ id_X        (up to unitors)
        (id ⨂ ε) ∘ α ∘ (η ⨂ id) ≈ id_{X^*}      (up to unitors)

    Hypergraph categories are a special case: every object is its own dual
    via [X^* := X], with unit and counit built from the SCFA structure as
    [η := δ ∘ η_X] and [ε := ε_X ∘ μ]. *)

Section CompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CompactClosed : Type := {
  dual : C -> C;

  cc_unit   : forall X : C, I ~> dual X ⨂ X;
  cc_counit : forall X : C, X ⨂ dual X ~> I;

  snake_left : forall X : C,
    to (@unit_left C _ X)
      ∘ bimap (cc_counit X) id[X]
      ∘ from (@tensor_assoc C _ X (dual X) X)
      ∘ bimap id[X] (cc_unit X)
      ∘ from (@unit_right C _ X)
    ≈ id[X];

  snake_right : forall X : C,
    to (@unit_right C _ (dual X))
      ∘ bimap id[dual X] (cc_counit X)
      ∘ to (@tensor_assoc C _ (dual X) X (dual X))
      ∘ bimap (cc_unit X) id[dual X]
      ∘ from (@unit_left C _ (dual X))
    ≈ id[dual X]
}.

End CompactClosed.

Arguments CompactClosed C {S}.
Arguments dual {C S _} X.
Arguments cc_unit {C S _} X.
Arguments cc_counit {C S _} X.

(** * Every hypergraph category is compact closed (self-dual)

    For [X^* := X] we set

      cc_unit_X   := (δ_X ⨂ id_I-ish) ∘ η_X  — really  δ ∘ η : I ~> X⨂X
      cc_counit_X := ε ∘ μ : X⨂X ~> I

    The snake identities collapse via specialness ([μ ∘ δ ≈ id]) plus the
    Frobenius equation.  We do **not** export this as a [Global Instance] to
    avoid typeclass-search blowups: clients opt in via [Existing Instance].

    Note: the full snake derivation requires a non-trivial diagram chase
    combining Frobenius, specialness, and the unit/associator coherence.
    In V1 we record the construction and snake equations as goals; the
    derivation is left for V2 (downstream users only need the [CompactClosed]
    interface, not the specific witness). *)

Section HypergraphIsCompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

(** Self-dual unit, given an SCFA on [X]. *)
Definition hcc_unit (X : C) `{F : @SpecialCommutativeFrobenius C S X}
  : I ~> X ⨂ X := scfa_delta F ∘ scfa_eta F.

(** Self-dual counit, given an SCFA on [X]. *)
Definition hcc_counit (X : C) `{F : @SpecialCommutativeFrobenius C S X}
  : X ⨂ X ~> I := scfa_epsilon F ∘ scfa_mu F.

End HypergraphIsCompactClosed.

(** Note on the [Hypergraph -> CompactClosed] derivation.

    The construction [dual X := X], [cc_unit := hcc_unit],
    [cc_counit := hcc_counit] is well-defined for any hypergraph category.
    Proving the snake equations requires combining the Frobenius law, the
    specialness law [μ∘δ ≈ id], and a moderate amount of associator/unitor
    coherence — none of these proofs are short.

    To keep V1 focused and shippable we expose the data of the construction
    but defer the formal [Program Instance] / proof of the snake equations to
    V2.  Downstream consumers who need [CompactClosed] for a hypergraph
    category can either:

      (a) supply their own [CompactClosed] instance directly for their
          concrete category (e.g. [Cospan(Sets)]), or
      (b) wait for the V2 derivation.

    See [docs/HYPERGRAPH_MIGRATION.md] for the migration story. *)

(* TODO(V2): Prove  forall (C : Category) `{S : @SymmetricMonoidal C}
   (H : @Hypergraph C S), @CompactClosed C S
   with dual X := X, cc_unit := hcc_unit, cc_counit := hcc_counit. *)
