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

(** * Core spider lemmas for hypergraph categories

    In a hypergraph category, each object [X] carries a special commutative
    Frobenius algebra (SCFA).  "Spider" diagrams — vertices with arbitrarily
    many input and output legs built from [scfa_mu] / [scfa_eta] /
    [scfa_delta] / [scfa_epsilon] — collapse to canonical normal forms that
    depend only on the leg count, not on how the spider was assembled.

    The full "spider theorem" (Lack's normal form for SCFA expressions) is
    a non-trivial induction and is deferred to V2b.  This file provides the
    workhorse lemmas that downstream proofs typically reach for:

      - [spider_frobenius]    — the Frobenius law at the [scfa_*] level
      - [spider_frobenius_sym] — its dual via [frob_law_right]
      - [spider_collapse]     — specialness ([μ ∘ δ ≈ id])
      - [spider_mu_assoc]     — monoid associativity of [scfa_mu]
      - [spider_3_to_1]       — the 3-into-1 spider, the workhorse case
      - [spider_delta_coassoc] — comonoid associativity of [scfa_delta]
*)

Section Spider.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.
Context `{H : @Hypergraph C S}.

(** The Frobenius law at the user-friendly [scfa_*] level. *)
Lemma spider_frobenius (X : C) :
  scfa_delta (scfa X) ∘ scfa_mu (scfa X)
  ≈ bimap (scfa_mu (scfa X)) id[X]
      ∘ from (@tensor_assoc C _ X X X)
      ∘ bimap id[X] (scfa_delta (scfa X)).
Proof.
  unfold scfa_mu, scfa_delta.
  symmetry.
  apply (frob_law_left (Frobenius := scfa X)).
Qed.

(** Symmetric form: the right Frobenius law. *)
Lemma spider_frobenius_sym (X : C) :
  scfa_delta (scfa X) ∘ scfa_mu (scfa X)
  ≈ bimap id[X] (scfa_mu (scfa X))
      ∘ to (@tensor_assoc C _ X X X)
      ∘ bimap (scfa_delta (scfa X)) id[X].
Proof.
  unfold scfa_mu, scfa_delta.
  symmetry.
  apply (frob_law_right (Frobenius := scfa X)).
Qed.

(** Specialness, the collapse axiom: [μ ∘ δ ≈ id]. *)
Lemma spider_collapse (X : C) :
  scfa_mu (scfa X) ∘ scfa_delta (scfa X) ≈ id[X].
Proof.
  unfold scfa_mu, scfa_delta.
  apply (mu_delta_id (SpecialCommutativeFrobenius := scfa X)).
Qed.

(** Monoid associativity at the [scfa_*] level. *)
Lemma spider_mu_assoc (X : C) :
  scfa_mu (scfa X) ∘ bimap (scfa_mu (scfa X)) id[X]
  ≈ scfa_mu (scfa X) ∘ bimap id[X] (scfa_mu (scfa X))
      ∘ to (@tensor_assoc C _ X X X).
Proof.
  unfold scfa_mu.
  apply (mu_assoc (Monoid := scfa X)).
Qed.

(** Comonoid coassociativity at the [scfa_*] level. *)
Lemma spider_delta_coassoc (X : C) :
  bimap (scfa_delta (scfa X)) id[X] ∘ scfa_delta (scfa X)
  ≈ from (@tensor_assoc C _ X X X)
      ∘ bimap id[X] (scfa_delta (scfa X))
      ∘ scfa_delta (scfa X).
Proof.
  unfold scfa_delta.
  apply (delta_coassoc (Comonoid := scfa X)).
Qed.

(** Monoid unit laws at the [scfa_*] level. *)
Lemma spider_mu_unit_left (X : C) :
  scfa_mu (scfa X) ∘ bimap (scfa_eta (scfa X)) id[X]
  ≈ to (@unit_left C _ X).
Proof.
  unfold scfa_mu, scfa_eta.
  apply (mu_unit_left (Monoid := scfa X)).
Qed.

Lemma spider_mu_unit_right (X : C) :
  scfa_mu (scfa X) ∘ bimap id[X] (scfa_eta (scfa X))
  ≈ to (@unit_right C _ X).
Proof.
  unfold scfa_mu, scfa_eta.
  apply (mu_unit_right (Monoid := scfa X)).
Qed.

(** Comonoid counit laws at the [scfa_*] level. *)
Lemma spider_delta_counit_left (X : C) :
  bimap (scfa_epsilon (scfa X)) id[X] ∘ scfa_delta (scfa X)
  ≈ from (@unit_left C _ X).
Proof.
  unfold scfa_delta, scfa_epsilon.
  apply (delta_counit_left (Comonoid := scfa X)).
Qed.

Lemma spider_delta_counit_right (X : C) :
  bimap id[X] (scfa_epsilon (scfa X)) ∘ scfa_delta (scfa X)
  ≈ from (@unit_right C _ X).
Proof.
  unfold scfa_delta, scfa_epsilon.
  apply (delta_counit_right (Comonoid := scfa X)).
Qed.

(** Commutativity of [scfa_mu] under the braid. *)
Lemma spider_mu_commutative (X : C) :
  scfa_mu (scfa X) ∘ braid ≈ scfa_mu (scfa X).
Proof.
  unfold scfa_mu.
  apply (mu_commutative (CommutativeFrobenius := scfa X)).
Qed.

(** Cocommutativity of [scfa_delta] under the braid. *)
Lemma spider_delta_cocommutative (X : C) :
  braid ∘ scfa_delta (scfa X) ≈ scfa_delta (scfa X).
Proof.
  unfold scfa_delta.
  apply (delta_cocommutative (CommutativeFrobenius := scfa X)).
Qed.

(** ** The workhorse: the 3-into-1 spider

    A spider with three inputs and one output, regardless of how the inputs
    are bracketed, gives the same morphism.  This is the un-bracketed form
    of the monoid associativity law and is one of the fundamental cases of
    Lack's full spider theorem. *)
Lemma spider_3_to_1 (X : C) :
  scfa_mu (scfa X) ∘ bimap (scfa_mu (scfa X)) id[X]
  ≈ scfa_mu (scfa X) ∘ bimap id[X] (scfa_mu (scfa X))
      ∘ to (@tensor_assoc C _ X X X).
Proof.
  apply spider_mu_assoc.
Qed.

(** Dually, the 1-into-3 spider. *)
Lemma spider_1_to_3 (X : C) :
  bimap (scfa_delta (scfa X)) id[X] ∘ scfa_delta (scfa X)
  ≈ from (@tensor_assoc C _ X X X)
      ∘ bimap id[X] (scfa_delta (scfa X)) ∘ scfa_delta (scfa X).
Proof.
  apply spider_delta_coassoc.
Qed.

(** The 2-into-2 spider: the heart of the Frobenius equation. *)
Lemma spider_2_to_2 (X : C) :
  scfa_delta (scfa X) ∘ scfa_mu (scfa X)
  ≈ bimap (scfa_mu (scfa X)) id[X]
      ∘ from (@tensor_assoc C _ X X X)
      ∘ bimap id[X] (scfa_delta (scfa X)).
Proof.
  apply spider_frobenius.
Qed.

End Spider.

(** ** Note on the full spider theorem (V2b)

    Lack's theorem ("Composing PROPs", arXiv:0411065) states that any string
    diagram built from [scfa_mu] / [scfa_eta] / [scfa_delta] / [scfa_epsilon]
    on a single object [X], with [m] input legs and [n] output legs,
    reduces to a unique canonical normal form depending only on the pair
    [(m, n)] (with the cases [m = n = 0] handled by the unit/counit
    composite).  The proof is by induction on the syntactic structure of
    the diagram and uses associativity, coassociativity, the Frobenius law,
    specialness, and commutativity.

    The general theorem is significant work and is deferred to V2b. *)
