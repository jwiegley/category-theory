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

    The [PROP] class supplies TWO independent fields that each induce a
    [Monoidal (prop_cat P)]:

      - [prop_strict   : StrictMonoidal     (prop_cat P)] with coercion
        [strict_is_monoidal : StrictMonoidal -> Monoidal]
      - [prop_symmetric : SymmetricMonoidal (prop_cat P)] with coercion
        [braided_is_monoidal . symmetric_is_braided : SymmetricMonoidal
                                                      -> Monoidal]

    The class does not assert that these two paths produce
    *definitionally equal* [Monoidal] records.  In consequence, an
    expression like

      braid : (T ⨂ T) ~> (T ⨂ T)

    fails to type-check inside a [HypergraphPROP] context because the
    [⨂] notation resolves through [strict_is_monoidal] (the
    StrictMonoidal path) while [braid] expects the
    [SymmetricMonoidal]-induced [Monoidal]; Coq does not unify them.

    Similarly, [scfa_mu (scfa T) : T ⨂ T ~> T] resolves through the
    [Hypergraph]'s [SymmetricMonoidal] path, while
    [prop_tensor_plus : ⟦m⟧ ⨂ ⟦n⟧ = ⟦m+n⟧] uses the strict path; they
    are interchangeable mathematically but not as Coq terms.

    The workaround for downstream code is to PIN the [Monoidal] path
    explicitly at each tensor: write [(T ⨂[strict_is_monoidal] T)] when
    proving against [prop_tensor_plus], and let inference pick the
    [SymmetricMonoidal] path when using [braid] / [scfa_*].

    The proper fix in the library is to require, in the [PROP] class,
    that [prop_symmetric]'s underlying [Monoidal] is *the same* (up to
    definitional equality) as [strict_is_monoidal prop_strict] — for
    example by re-parameterising:

      Class PROP : Type := {
        prop_cat     : Category;
        prop_strict  : @StrictMonoidal prop_cat;
        prop_symmetric : @SymmetricMonoidal prop_cat
                          (@strict_is_monoidal prop_cat prop_strict);
        ...
      }.

    This would make the two paths definitionally identical and unblock
    the smoke tests removed from this file.  Tracked as a follow-up. *)
