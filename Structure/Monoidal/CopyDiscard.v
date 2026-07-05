Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(** * Copy-discard (gs-monoidal) categories

    A copy-discard category — also called a gs-monoidal category ("garbage
    and sharing") — is a symmetric monoidal category [(C, ⨂, I, σ)] equipped
    with a chosen commutative comonoid

      copy[X]    : X ~> X ⨂ X      (comultiplication, "duplicate the wire")
      discard[X] : X ~> I          (counit, "delete the wire")

    on every object, such that the comonoid on [X ⨂ Y] is canonically
    assembled from those on [X] and [Y] (via the middle-interchange
    isomorphism), and the comonoid on [I] is the trivial one.

    THE defining negative space of this class: there is deliberately NO
    naturality condition on [copy] or [discard].  A morphism [f] need not
    satisfy [copy ∘ f ≈ (f ⨂ f) ∘ copy] nor [discard ∘ f ≈ discard]; the
    two squares together are precisely what single out the DETERMINISTIC
    morphisms (Cho–Jacobs; see CopyDiscard/Deterministic.v).  The two
    omissions carry different weight.  Imposing the discard square on ALL
    morphisms is exactly semicartesianness — it says any map into [I]
    agrees with [discard], i.e. [I] is terminal — which is the Markov case,
    not a degeneracy: Structure/Monoidal/Markov.v derives [discard_natural]
    for every morphism as a corollary of [unit_terminal].  Imposing the
    copy square on ALL morphisms makes [copy] a natural diagonal, yielding
    [RelevanceMonoidal]'s naturality together with the counits that class
    lacks; imposing both squares globally is Fox's theorem territory: the
    structure collapses to cartesian monoidal (see Heunen_Vicary.v and
    Markov/Fox.v).  This class is therefore INCOMPARABLE with
    [RelevanceMonoidal], not below it: [CopyDiscard] carries counits that
    [RelevanceMonoidal] lacks, while [RelevanceMonoidal] carries the
    naturality that [CopyDiscard] deliberately drops.  What both strengthen
    is the bare per-object [CommutativeComonoid] supply with no coherence
    at all.

    Accordingly [RelevanceMonoidal] is NOT a source of instances for this
    class: its diagonal comes with no counit whatsoever, so the comonoid
    counit laws [(ε ⨂ id) ∘ δ ≈ λ⁻¹] are underivable there.  The sound
    generic instances — from [CartesianMonoidal] (Fox's projection laws
    supply the counits) and from [Hypergraph] (forget the monoid half of
    each SCFA) — live in Structure/Monoidal/CopyDiscard/Proofs.v.

    The class shape mirrors Hypergraph.v's SCFA supply verbatim: a
    per-object structure field, canonical-tensor coherence, and unit
    coherence, reusing [canonical_tensor_delta] / [canonical_tensor_epsilon]
    (stated there for plain [Comonoid] arguments; [CommutativeComonoid]
    coerces).

    nLab:      https://ncatlab.org/nlab/show/copy-discard+category
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
               string diagrams", MSCS 29(7):938–971, 2019 (arXiv:1709.00322)
    Reference: Fritz, "A synthetic approach to Markov kernels, conditional
               independence and theorems on sufficient statistics",
               Adv. Math. 370:107239, 2020 (arXiv:1908.07021), §2
    Reference: Corradini & Gadducci, "An algebraic presentation of term
               graphs, via gs-monoidal categories", Appl. Categ. Structures
               7(4):299–331, 1999 *)

Section CopyDiscard.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class CopyDiscard : Type := {
  cd_comonoid (X : C) : CommutativeComonoid X;

  (* Tensor coherence: the comonoid on [X ⨂ Y] agrees with the canonical
     one assembled from those on [X] and [Y] through [mid_swap_inv]
     (Hypergraph.v):  δ_{X⨂Y} ≈ mid_swap_inv ∘ (δ_X ⨂ δ_Y). *)
  cd_tensor_delta (X Y : C) :
    ccomon_delta (cd_comonoid (X ⨂ Y))
      ≈ canonical_tensor_delta (cd_comonoid X) (cd_comonoid Y);

  (* ε_{X⨂Y} ≈ unit_left ∘ (ε_X ⨂ ε_Y). *)
  cd_tensor_epsilon (X Y : C) :
    ccomon_epsilon (cd_comonoid (X ⨂ Y))
      ≈ canonical_tensor_epsilon (cd_comonoid X) (cd_comonoid Y);

  (* Unit coherence: the comonoid on [I] is the trivial one,
     δ_I ≈ unit_left⁻¹ and ε_I ≈ id (cf. scfa_unit_delta/epsilon). *)
  cd_unit_delta   : ccomon_delta   (cd_comonoid I) ≈ from (@unit_left C _ I);
  cd_unit_epsilon : ccomon_epsilon (cd_comonoid I) ≈ id[I]
}.

(* [cd_comonoid] is deliberately NOT an [Existing Instance] (mirroring
   [scfa] in Hypergraph.v): typeclass resolution must never invent a
   comonoid structure on an object; access it via the projections below. *)

Definition copy `{CopyDiscard} (X : C) : X ~> (X ⨂ X)%object :=
  ccomon_delta (cd_comonoid X).

Definition discard `{CopyDiscard} (X : C) : X ~> I :=
  ccomon_epsilon (cd_comonoid X).

End CopyDiscard.

Arguments cd_comonoid {C S _} X.
Arguments copy {C S _} X.
Arguments discard {C S _} X.
Arguments CopyDiscard C {S}.

Notation "copy[ X ]" := (copy X)
  (at level 9, format "copy[ X ]") : morphism_scope.
Notation "discard[ X ]" := (discard X)
  (at level 9, format "discard[ X ]") : morphism_scope.
