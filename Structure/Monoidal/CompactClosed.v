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

(** ** The derivation [Hypergraph C -> CompactClosed C]

    Self-dual: [dual X := X], [cc_unit X := scfa_delta ∘ scfa_eta],
    [cc_counit X := scfa_epsilon ∘ scfa_mu].

    Both snake equations reduce by the same pattern:
      1. Distribute [bimap (ε∘μ) id ≈ bimap ε id ∘ bimap μ id] and dually
         [bimap id (δ∘η) ≈ bimap id δ ∘ bimap id η].
      2. Apply the Frobenius law [frob_law_left] (resp. [frob_law_right])
         to collapse [bimap μ id ∘ α⁻¹ ∘ bimap id δ] to [δ ∘ μ].
      3. Apply the monoid unit law [mu_unit_right] to collapse
         [μ ∘ bimap id η] to [unit_right], cancelling with [unit_right⁻¹].
      4. Apply the comonoid counit law [delta_counit_left] to collapse
         [bimap ε id ∘ δ] to [unit_left⁻¹], cancelling with [unit_left].

    Not exported as a [Global Instance] to avoid typeclass-search blowups;
    clients opt in with [Existing Instance Hypergraph_CompactClosed.]. *)

Section HypergraphToCompactClosed.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C S}.

(** Re-expose the unfoldings of [cc_unit] / [cc_counit] for the self-dual
    construction; these isolate the [scfa_*] form for rewriting. *)
Lemma cc_unit_unfold (X : C) :
  hcc_unit X (F := scfa X) = scfa_delta (scfa X) ∘ scfa_eta (scfa X).
Proof. reflexivity. Qed.

Lemma cc_counit_unfold (X : C) :
  hcc_counit X (F := scfa X) = scfa_epsilon (scfa X) ∘ scfa_mu (scfa X).
Proof. reflexivity. Qed.

(** The snake-left calculation, abstracted away from the iso unfoldings. *)
Lemma hypergraph_snake_left (X : C) :
  to (@unit_left C _ X)
    ∘ bimap (hcc_counit X (F := scfa X)) id[X]
    ∘ from (@tensor_assoc C _ X X X)
    ∘ bimap id[X] (hcc_unit X (F := scfa X))
    ∘ from (@unit_right C _ X)
  ≈ id[X].
Proof.
  unfold hcc_unit, hcc_counit.
  (* Distribute bimap over the SCFA composites. *)
  rewrite (bimap_comp_id_right (scfa_epsilon _) (scfa_mu _)).
  rewrite (bimap_comp_id_left (scfa_delta _) (scfa_eta _)).
  (* Bring frob_law_left into focus: bimap μ id ∘ α⁻¹ ∘ bimap id δ ≈ δ ∘ μ. *)
  (* Currently: unit_left ∘ (bimap ε id ∘ bimap μ id) ∘ α⁻¹
                 ∘ (bimap id δ ∘ bimap id η) ∘ unit_right⁻¹. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap (scfa_mu _) id)).
  rewrite (comp_assoc (bimap (scfa_mu _) id ∘ from tensor_assoc)).
  unfold scfa_mu, scfa_delta, scfa_epsilon, scfa_eta.
  rewrite (frob_law_left (Frobenius := scfa X)).
  (* Now: unit_left ∘ bimap ε id ∘ (δ ∘ μ) ∘ bimap id η ∘ unit_right⁻¹. *)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc mu (bimap id eta)).
  rewrite (mu_unit_right (Monoid := scfa X)).
  rewrite iso_to_from, id_right.
  (* Now: unit_left ∘ (bimap ε id ∘ δ) ≈ id. *)
  rewrite (delta_counit_left (Comonoid := scfa X)).
  rewrite iso_to_from.
  reflexivity.
Qed.

(** The snake-right calculation, symmetric to [snake_left] under [paws]. *)
Lemma hypergraph_snake_right (X : C) :
  to (@unit_right C _ X)
    ∘ bimap id[X] (hcc_counit X (F := scfa X))
    ∘ to (@tensor_assoc C _ X X X)
    ∘ bimap (hcc_unit X (F := scfa X)) id[X]
    ∘ from (@unit_left C _ X)
  ≈ id[X].
Proof.
  unfold hcc_unit, hcc_counit.
  rewrite (bimap_comp_id_left  (scfa_epsilon _) (scfa_mu _)).
  rewrite (bimap_comp_id_right (scfa_delta _) (scfa_eta _)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap id (scfa_mu _))).
  rewrite (comp_assoc (bimap id (scfa_mu _) ∘ to tensor_assoc)).
  unfold scfa_mu, scfa_delta, scfa_epsilon, scfa_eta.
  rewrite (frob_law_right (Frobenius := scfa X)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc mu (bimap eta id)).
  rewrite (mu_unit_left (Monoid := scfa X)).
  rewrite iso_to_from, id_right.
  rewrite (delta_counit_right (Comonoid := scfa X)).
  rewrite iso_to_from.
  reflexivity.
Qed.

(** The derived compact-closed structure on a hypergraph category.

    [dual X := X] (self-dual), and [cc_unit] / [cc_counit] are the
    SCFA-derived morphisms [hcc_unit] / [hcc_counit].

    The snake identities follow from [hypergraph_snake_left] and
    [hypergraph_snake_right]. *)
Program Instance Hypergraph_CompactClosed : @CompactClosed C S := {|
  dual      := fun X => X;
  cc_unit   := fun X => hcc_unit X (F := scfa X);
  cc_counit := fun X => hcc_counit X (F := scfa X);

  snake_left  := hypergraph_snake_left;
  snake_right := hypergraph_snake_right
|}.

End HypergraphToCompactClosed.
