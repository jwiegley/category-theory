Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Construction.PROP.

Generalizable All Variables.

(** * End-to-end typeclass-resolution smoke tests for HypergraphPROP

    nLab:      https://ncatlab.org/nlab/show/PROP
    nLab:      https://ncatlab.org/nlab/show/hypergraph+category
    Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

    A [HypergraphPROP] (see [Construction/PROP.v]) bundles a [PROP] — a
    strict symmetric monoidal category whose object monoid is [(ℕ, +, 0)] —
    with a [Hypergraph] instance, i.e. a chosen special commutative
    Frobenius algebra (SCFA) on every object.  This file is a compile-time
    smoke test: each [Definition] below type-checks only if the coercion /
    [#[export] Existing Instance] chain actually delivers the structure
    named in its type, so a successful build IS the assertion.

    These tests verify that, given just [Variable P : HypergraphPROP],
    Coq's typeclass resolution finds the structural instances downstream
    callers will need:

      - PROP                            -- via the [hpprop] coercion
      - prop_cat P : Category           -- via the [prop_cat] coercion
      - SymmetricMonoidal (prop_cat P)  -- via prop_symmetric
      - StrictMonoidal (prop_cat P)     -- via prop_strict
      - Hypergraph (prop_cat P) ...     -- via hpprop_hyper
      - SpecialCommutativeFrobenius X   -- via scfa : forall X, ...

    If this file compiles, the [#[export] Existing Instance] / Coercion
    chain is working as advertised. *)

Open Scope nat_scope.

Section HypergraphPROPResolutionTests.

Context (P : HypergraphPROP).

(** The "tensor wire" — the canonical 1-arity PROP-object. *)
Notation T := (@prop_of_nat P 1).

(** [T] is an object of [P]. *)
Definition test_obj_resolves : @obj P := T.

(** Identity morphisms at [T] type-check. *)
Definition test_id : T ~> T := id.

(** Composition is found via the Category resolution. *)
Definition test_compose (f g : T ~> T) : T ~> T := g ∘ f.

(** Equivalence is found between two morphisms of the same hom-set. *)
Definition test_equiv (f g : T ~> T) : Type := f ≈ g.

(** The SCFA on T is found via the Hypergraph instance, and its flat
    [scfa_*] projections work. *)
Definition test_scfa_mu      := scfa_mu      (scfa T).
Definition test_scfa_eta     := scfa_eta     (scfa T).
Definition test_scfa_delta   := scfa_delta   (scfa T).
Definition test_scfa_epsilon := scfa_epsilon (scfa T).

(** The SCFA-projected morphisms have the expected hom-set shape.
    We avoid explicit [@I _ _] annotations because the [I] notation
    picks a Monoidal instance and may pick a different one than the
    SymmetricMonoidal-induced one used by [scfa].  Instead, we just
    confirm the bare projections compose with themselves. *)
Definition test_scfa_eta_compose := compose test_scfa_epsilon test_scfa_eta.

End HypergraphPROPResolutionTests.

Close Scope nat_scope.

(** ** KNOWN LIMITATION: ambiguous [Monoidal (prop_cat P)] instance

    The [PROP] class supplies TWO fields that each induce a
    [Monoidal (prop_cat P)]:

      - [prop_strict   : StrictMonoidal     (prop_cat P)] with coercion
        [strict_is_monoidal : StrictMonoidal -> Monoidal]
      - [prop_symmetric : SymmetricMonoidal (prop_cat P)] with coercion
        [braided_is_monoidal . symmetric_is_braided : SymmetricMonoidal
                                                      -> Monoidal]

    The class DOES relate these two paths, via the field

      [prop_monoidal_coherence :
         strict_is_monoidal prop_strict
         = braided_is_monoidal (symmetric_is_braided prop_symmetric)]

    but only as a PROPOSITIONAL (Leibniz) equality, not a definitional
    one.  In consequence, an expression like

      braid : (T ⨂ T) ~> (T ⨂ T)

    still fails to type-check inside a [HypergraphPROP] context (verified
    empirically): the [⨂] notation resolves [T ⨂ T] through
    [strict_is_monoidal] (the StrictMonoidal path) while [braid] expects
    the [SymmetricMonoidal]-induced [Monoidal], and Coq will not unify the
    two records up to a propositional equality on its own.

    Similarly, [scfa_mu (scfa T) : T ⨂ T ~> T] resolves through the
    [Hypergraph]'s [SymmetricMonoidal] path (confirmed by [Check]), while
    [prop_tensor_plus : ⟦m⟧ ⨂ ⟦n⟧ = ⟦m+n⟧] uses the strict path; they
    are interchangeable mathematically but not as bare Coq terms.

    The workaround for downstream code is to bridge the two paths with an
    explicit [rewrite prop_monoidal_coherence] (or [subst]) at the use
    site, or to PIN the [Monoidal] path: write
    [(T ⨂[strict_is_monoidal] T)] when proving against [prop_tensor_plus],
    and let inference pick the [SymmetricMonoidal] path when using [braid]
    / [scfa_*].

    The DEFINITIONAL fix — which would make [prop_monoidal_coherence]
    reduce to [eq_refl] and let [braid] / [scfa_*] / [prop_tensor_plus]
    inter-operate without any [rewrite] — is to re-parameterise the
    library's [BraidedMonoidal] / [SymmetricMonoidal] classes to take an
    [@Monoidal C] as an explicit parameter, so [prop_symmetric] can
    inherit [strict_is_monoidal prop_strict] verbatim.  That is a
    multi-file refactor deferred to a separate PR and tracked in the
    [prop_monoidal_coherence] discussion in [Construction/PROP.v]; the
    tests requiring it (e.g. a typed [braid] on [T ⨂ T]) are omitted from
    this file until then. *)
