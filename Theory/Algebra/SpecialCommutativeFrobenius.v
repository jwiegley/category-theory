Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.

Generalizable All Variables.

(** * Special commutative Frobenius algebras (SCFAs) *)

(* A commutative Frobenius algebra (Theory/Algebra/CommutativeFrobenius.v) is
   "special" when the round trip [mu ∘ delta] is the identity.  In our library
   notation the special law is

       mu ∘ delta ≈ id[X]            (the special / "isometric" law)

   Equivalently the Frobenius pair has no redundancy: every "spider" with the
   same number of legs collapses to a single canonical form (this is the
   normal-form / "spider theorem").  Both nLab and Wikipedia state the law as
   [prod ∘ coprod = id] (Wikipedia writes [μ ∘ δ = Id_A]); some authors only
   require [mu ∘ delta = β·id] for a nonzero scalar [β], in which case ours is
   the strict (β = 1) version.

   Note on neighbouring conditions.  "Special" constrains only [mu ∘ delta]; it
   does NOT impose the dual unit/counit law [epsilon ∘ eta ≈ id].  That extra
   law is the separate "extraspecial" (a.k.a. "bone" / "irredundancy") axiom,
   and we deliberately do not require it here.

   ZX-calculus.  Dagger special commutative Frobenius algebras are exactly the
   "classical structures" / "observable structures" of categorical quantum
   mechanics: their morphisms are the ZX-calculus green/red spiders, and the
   special law is what powers the spider fusion rule.  (Our setting is a plain
   symmetric monoidal category, without the dagger.)

   Special commutative Frobenius algebras are also the central algebraic object
   of hypergraph categories: a hypergraph category is a symmetric monoidal
   category equipped with an SCFA on every object, compatible with the tensor
   in a canonical way.

   nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
   nLab:      https://ncatlab.org/nlab/show/classical+structure
   Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra *)

Section SpecialCommutativeFrobenius.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class SpecialCommutativeFrobenius (X : C) : Type := {
  (* underlying commutative Frobenius algebra ([mu], [eta], [delta], [epsilon]) *)
  scfa_commutative : @CommutativeFrobenius C _ X;

  (* the special law: [mu ∘ delta ≈ id[X]] *)
  mu_delta_id :
    (@mu _ _ _ (@frob_monoid _ _ _ (@cfrob_frobenius _ _ _ scfa_commutative)))
      ∘ (@delta _ _ _ (@frob_comonoid _ _ _ (@cfrob_frobenius _ _ _ scfa_commutative)))
    ≈ id[X]
}.
#[export] Existing Instance scfa_commutative.

Coercion scfa_commutative : SpecialCommutativeFrobenius >-> CommutativeFrobenius.

End SpecialCommutativeFrobenius.

Arguments scfa_commutative {C S X _}.

(** ** SCFA projection shortcuts

    These collapse the nested projection chain
    [mu (frob_monoid (cfrob_frobenius (scfa_commutative F)))]
    down to a single [scfa_mu F]. *)

Section SCFAProjections.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Definition scfa_mu {X : C} (F : SpecialCommutativeFrobenius X)
  : X ⨂ X ~> X :=
  @mu _ _ _ (@frob_monoid _ _ _ (@cfrob_frobenius _ _ _ F)).

Definition scfa_eta {X : C} (F : SpecialCommutativeFrobenius X)
  : I ~> X :=
  @eta _ _ _ (@frob_monoid _ _ _ (@cfrob_frobenius _ _ _ F)).

Definition scfa_delta {X : C} (F : SpecialCommutativeFrobenius X)
  : X ~> X ⨂ X :=
  @delta _ _ _ (@frob_comonoid _ _ _ (@cfrob_frobenius _ _ _ F)).

Definition scfa_epsilon {X : C} (F : SpecialCommutativeFrobenius X)
  : X ~> I :=
  @epsilon _ _ _ (@frob_comonoid _ _ _ (@cfrob_frobenius _ _ _ F)).

End SCFAProjections.

Arguments scfa_mu      {C S X} F.
Arguments scfa_eta     {C S X} F.
Arguments scfa_delta   {C S X} F.
Arguments scfa_epsilon {C S X} F.
