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
Require Import Category.Structure.Monoidal.Hypergraph.Spider.

Generalizable All Variables.

(** * Hint database for hypergraph-level rewrites

    Bundles the simplification-direction (LHS more complex than RHS)
    spider lemmas into a single [hypergraph] hint database.

    Downstream code can write

      autorewrite with hypergraph.

    to apply all of these rewrites until fixpoint.  Combined with
    [autorewrite with categories] and the library's [cat] tactic, this
    gives a fast path for closing routine SCFA-algebra goals.

    Bidirectional lemmas — [spider_mu_assoc], [spider_delta_coassoc],
    [spider_frobenius], [spider_frobenius_sym], [spider_2_to_2],
    [spider_3_to_1], [spider_1_to_3] — are NOT in this database because
    [autorewrite] would loop on them.  Use them manually with
    [rewrite].

    The lemmas registered here are exactly:

      spider_collapse              μ ∘ δ ≈ id
      spider_mu_unit_left          μ ∘ bimap η id ≈ to unit_left
      spider_mu_unit_right         μ ∘ bimap id η ≈ to unit_right
      spider_delta_counit_left     bimap ε id ∘ δ ≈ from unit_left
      spider_delta_counit_right    bimap id ε ∘ δ ≈ from unit_right
      spider_mu_commutative        μ ∘ braid ≈ μ
      spider_delta_cocommutative   braid ∘ δ ≈ δ
*)

#[export] Hint Rewrite
  @spider_collapse
  @spider_mu_unit_left
  @spider_mu_unit_right
  @spider_delta_counit_left
  @spider_delta_counit_right
  @spider_mu_commutative
  @spider_delta_cocommutative
  : hypergraph.

(** * [solve_hypergraph]: an automation tactic for SCFA-algebra goals

    Composes:
      1. [autorewrite with hypergraph]   simplify via the spider rules
                                          registered above
      2. [autorewrite with categories]    simplify via the library's
                                          category laws ([id_left],
                                          [id_right], [comp_assoc])
      3. [auto with category_laws]        close any remaining setoid
                                          reflexivity / [Proper] goals

    The tactic loops on its own simplification pass until fixpoint, so
    composite goals that decompose into a sequence of spider rewrites
    interleaved with category-law cleanups close in one call.

    Goals it does NOT close:

      - Anything requiring the BIDIRECTIONAL Frobenius / associativity
        rules ([spider_frobenius], [spider_mu_assoc], [spider_3_to_1]).
        Use [rewrite] manually for those.
      - Anything requiring monoidal-coherence (associator / unitor)
        manipulation beyond what's in the [categories] hint database.
        Combine with the future [strict_collapse] tactic for the
        strict-monoidal case.

    Typical use:

      Lemma foo : forall (X : C) (f : X ~> X),
        scfa_mu (scfa X) ∘ scfa_delta (scfa X) ∘ f ≈ f.
      Proof. intros; solve_hypergraph. Qed. *)

Ltac solve_hypergraph :=
  repeat (autorewrite with hypergraph in *;
          autorewrite with categories in *);
  try (auto with category_laws);
  try reflexivity.

