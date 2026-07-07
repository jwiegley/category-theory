Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Structure.Monoidal.Markov.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(** * Fox's theorem: Markov categories with all morphisms deterministic

    Fox's theorem (Fox 1976; Heunen–Vicary 2012, p. 84) delimits the
    boundary between synthetic probability and ordinary (cartesian)
    computation:

    - a Markov category in which EVERY morphism is deterministic — i.e.
      copying commutes with every morphism — is cartesian monoidal
      ([all_deterministic_cartesian]); and, conversely,
    - in a cartesian monoidal category every morphism is deterministic
      with respect to the canonical diagonal/discard supply
      ([cartesian_all_deterministic]).

    Both directions together say that the copy-discard structure of a
    Markov category carries genuine probabilistic content exactly when
    copy-naturality breaks down somewhere; demanding it globally collapses the
    tensor to a categorical product.  This grounds the "cartesianization
    obstruction": no interesting Markov category factors through a
    cartesian one without killing its nondeterminism.

    The forward direction assembles a [RelevanceMonoidal] from the copy
    supply — naturality of the diagonal being exactly the determinism
    hypothesis — and discharges [CartesianMonoidal]'s remaining fields:

      proj_left_diagonal / proj_right_diagonal
        — the comonoid counit laws traded across terminality of [I]
          ([proj_left_copy] / [proj_right_copy], Markov.v);
      unit_left_braid / unit_right_braid
        — the derived braid–unitor coherences [braid_unit_left] /
          [braid_unit_right] of Structure/Monoidal/Braided/Proofs.v
          (Joyal–Street Prop. 2.1), the load-bearing import.

    Since in a Markov category the ε-triangle [discard ∘ f ≈ discard]
    holds for free (terminality of [I]), determinism there is equivalent
    to the copy square alone ([markov_deterministic_iff_copy]); this is
    why the forward direction needs nothing beyond copy-naturality.

    The packaging corollary [markov_all_deterministic_iff_cartesian]
    states the equivalence in existential form: a category carries a
    Markov structure whose morphisms are all deterministic iff it carries
    a cartesian monoidal structure.  The two roundtrip corollaries pin
    down that the forward construction preserves the supply: the copy
    and discard induced by the produced cartesian structure agree with
    the original ones.

    nLab:      https://ncatlab.org/nlab/show/Markov+category
    Reference: Fox, "Coalgebras and cartesian categories",
               Comm. Algebra 4(7):665–667, 1976
    Reference: Heunen & Vicary, "Categories for Quantum Theory",
               Oxford UP, 2019, §4.3 (Fox's theorem, p. 84 of the 2012
               lecture notes)
    Reference: Fritz, "A synthetic approach to Markov kernels ..."
               (arXiv:1908.07021), §10 *)

Section Fox.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Section AllDeterministicCartesian.

Context `{M : @MarkovCategory C S}.

(** ** Determinism in a Markov category is the copy square alone

    The ε-triangle of a comonoid homomorphism is automatic when the unit
    is terminal, so a morphism of a Markov category is deterministic as
    soon as it commutes with copying (Fritz, Definition 10.1). *)

Lemma markov_deterministic_of_copy {x y : C} (f : x ~> y) :
  copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x] → deterministic f.
Proof.
  intro Hcopy.
  split.
  - exact Hcopy.
  - apply (@unit_terminal C _ markov_semicartesian).
Qed.

Corollary markov_deterministic_iff_copy {x y : C} (f : x ~> y) :
  deterministic f ↔ (copy[y] ∘ f ≈ (f ⨂ f) ∘ copy[x]).
Proof.
  split.
  - exact (copy_natural_on_deterministic f).
  - exact (markov_deterministic_of_copy f).
Qed.

(** ** All morphisms deterministic ⇒ cartesian monoidal *)

Context (D : ∀ x y (f : x ~> y), deterministic f).

(* The copy supply becomes a natural diagonal: naturality is the
   determinism hypothesis, and the remaining coherence fields are the
   comonoid laws of the supply re-oriented. *)
Program Definition Relevance_of_deterministic : @RelevanceMonoidal C := {|
  relevance_is_symmetric := S;
  diagonal := fun x => copy[x]
|}.
Next Obligation.
  (* diagonal_natural: exactly the δ-square of the determinism
     hypothesis, read right-to-left. *)
  symmetry.
  apply (copy_natural_on_deterministic _ (D _ _ _)).
Qed.
Next Obligation.
  (* diagonal_unit: the unit-coherence field of the supply. *)
  apply copy_unit.
Qed.
Next Obligation.
  (* diagonal_tensor_assoc: coassociativity of the comonoid on x,
     solved for the forward associator. *)
  unfold copy, ccomon_delta.
  rewrite <- comp_assoc.
  rewrite delta_coassoc.
  rewrite !comp_assoc.
  rewrite iso_to_from.
  rewrite id_left.
  reflexivity.
Qed.
Next Obligation.
  (* braid_diagonal: cocommutativity of the supply. *)
  unfold copy, ccomon_delta.
  apply delta_cocommutative_of_ccomon.
Qed.
Next Obligation.
  (* diagonal_braid2: the tensor-coherence field, with [braid2]
     recognized as [mid_swap_inv] (cf. braid2_mid_swap_inv). *)
  rewrite copy_tensor.
  comp_right.
  unfold mid_swap_inv.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  reflexivity.
Qed.

Program Definition all_deterministic_cartesian : @CartesianMonoidal C := {|
  cartesian_is_relevance     := Relevance_of_deterministic;
  cartesian_is_semicartesian := markov_semicartesian
|}.
Next Obligation.
  (* proj_left_diagonal: the right counit law across terminality. *)
  apply proj_left_copy.
Qed.
Next Obligation.
  (* proj_right_diagonal: the left counit law across terminality. *)
  apply proj_right_copy.
Qed.
Next Obligation.
  (* unit_left_braid: Joyal–Street ρ ≈ λ ∘ β (Braided/Proofs.v). *)
  apply braid_unit_left.
Qed.
Next Obligation.
  (* unit_right_braid: the mirror coherence λ ≈ ρ ∘ β. *)
  apply braid_unit_right.
Qed.

(** ** Roundtrip: the produced cartesian structure carries the original
    supply

    The copy-discard structure induced by [all_deterministic_cartesian]
    (via [CD_of_Cartesian]) has the same copy — definitionally — and the
    same discard — by terminality — as the Markov category we started
    from.  Fox's construction loses nothing. *)

Corollary all_deterministic_cartesian_copy {x : C} :
  @copy C S (@CD_of_Cartesian C all_deterministic_cartesian) x ≈ copy[x].
Proof. reflexivity. Qed.

Corollary all_deterministic_cartesian_discard {x : C} :
  @discard C S (@CD_of_Cartesian C all_deterministic_cartesian) x
    ≈ discard[x].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

End AllDeterministicCartesian.

(** ** Cartesian monoidal ⇒ all morphisms deterministic *)

Section CartesianDeterministic.

Context `{H : @CartesianMonoidal C}.

(* Every morphism of a cartesian monoidal category is a comonoid
   homomorphism for the canonical diagonal/discard supply: the δ-square
   is naturality of the diagonal, and the ε-triangle is terminality of
   the unit.  "All kernels are deterministic": the degenerate,
   probability-free reading of a cartesian category as a Markov one. *)
Theorem cartesian_all_deterministic :
  ∀ x y (f : x ~> y), @deterministic C _ (@CD_of_Cartesian C H) x y f.
Proof.
  intros x y f.
  split.
  - symmetry; apply diagonal_natural.
  - apply unit_terminal.
Qed.

End CartesianDeterministic.

End Fox.

(** ** Packaging: Fox's theorem as an equivalence

    A category carries a Markov structure in which every morphism is
    deterministic precisely when it carries a cartesian monoidal
    structure.  The forward direction is [all_deterministic_cartesian];
    the backward direction equips the category with the canonical Markov
    structure of its cartesian one ([Markov_of_Cartesian]) and observes
    that all morphisms are deterministic there. *)

Section FoxPackaging.

Context {C : Category}.

Corollary markov_all_deterministic_iff_cartesian :
  (∃ (S : @SymmetricMonoidal C) (M : @MarkovCategory C S),
     ∀ x y (f : x ~> y), @deterministic C S (@markov_is_cd C S M) x y f)
    ↔ @CartesianMonoidal C.
Proof.
  split.
  - intros [S' [M' D]].
    exact (@all_deterministic_cartesian C S' M' D).
  - intro H.
    exists (@relevance_is_symmetric C (@cartesian_is_relevance C H)).
    exists (@Markov_of_Cartesian C H).
    intros x y f.
    exact (@cartesian_all_deterministic C H x y f).
Qed.

End FoxPackaging.
