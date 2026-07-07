Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Proofs.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.

Generalizable All Variables.

(** * Markov categories

    A Markov category (Fritz, arXiv:1908.07021, §2) is a copy-discard
    (gs-monoidal) category whose monoidal unit [I] is terminal: a symmetric
    monoidal category equipped with a coherent commutative-comonoid supply
    [copy]/[discard] on every object ([CopyDiscard]) together with a
    [SemicartesianMonoidal] structure — a morphism [eliminate : x ~> I] for
    every [x], any two such morphisms agreeing ([unit_terminal]).

    Reading: a morphism [x ~> y] is a synthetic Markov kernel (a "channel")
    from [x] to [y]; a morphism [I ~> x] is a state (a "distribution") on
    [x]; [copy] duplicates and [discard] deletes an input.

    The class is redundancy-free, following Fritz's formulation: it carries
    NO axiom identifying [discard] with [eliminate] and NO naturality axiom
    for [discard].  In a semicartesian category ANY two morphisms into [I]
    agree, so both facts are corollaries ([markov_discard_eliminate],
    [discard_natural]), not axioms.

    What is deliberately absent is naturality of [copy]: a morphism [f]
    satisfying [copy ∘ f ≈ (f ⨂ f) ∘ copy] is precisely a DETERMINISTIC
    morphism (Cho–Jacobs; see CopyDiscard/Deterministic.v), and by Fox's
    theorem demanding this of every morphism collapses the category to a
    cartesian monoidal one (see Markov/Fox.v).  Conversely every cartesian
    monoidal category is a Markov category — [Markov_of_Cartesian] below —
    in which "all kernels are deterministic": the degenerate, probability-
    free case.

    nLab:      https://ncatlab.org/nlab/show/Markov+category
    Reference: Fritz, "A synthetic approach to Markov kernels, conditional
               independence and theorems on sufficient statistics",
               Adv. Math. 370:107239, 2020 (arXiv:1908.07021), §2
    Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
               string diagrams", MSCS 29(7):938–971, 2019
               (arXiv:1709.00322) *)

Section Markov.

Context {C : Category}.
Context `{S : @SymmetricMonoidal C}.

Class MarkovCategory : Type := {
  (* The copy-discard structure: a commutative comonoid on every object,
     coherent with the tensor and the unit (but NOT natural). *)
  markov_is_cd : @CopyDiscard C S;

  (* The unit [I] is terminal (the category is semicartesian / affine):
     synthetically, "probability distributions are normalized". *)
  markov_semicartesian :
    @SemicartesianMonoidal C
      (@braided_is_monoidal C (@symmetric_is_braided C S))
}.
#[export] Existing Instance markov_is_cd.

Coercion markov_is_cd : MarkovCategory >-> CopyDiscard.

(* [markov_semicartesian] is deliberately NOT an [Existing Instance]:
   downstream files select it explicitly (mirroring how [cd_comonoid] is
   accessed by projection), keeping typeclass resolution from picking a
   semicartesian structure the caller did not ask for. *)

Context `{M : MarkovCategory}.

(* Discarding IS eliminating: both are morphisms into the terminal [I].
   Some presentations of Markov categories take this identification as an
   axiom; in Fritz's redundancy-free formulation it is a corollary of
   terminality. *)
Corollary markov_discard_eliminate {x : C} :
  discard[x] ≈ @eliminate C _ markov_semicartesian x.
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

(* Naturality of discard — "delete after doing anything is delete" — is
   likewise a corollary of terminality, never an axiom. *)
Corollary discard_natural {x y : C} (f : x ~> y) :
  discard[y] ∘ f ≈ discard[x].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

(** ** States and marginals

    Vocabulary for the probability track: a [state] on [x] is a morphism
    out of the unit, and the marginals of a joint state are obtained by
    discarding one factor of the tensor (the projections of
    Semicartesian.v).  The lemmas below are phrased through [state]. *)

Definition state (x : C) : Type := I ~> x.

(* Normalization: every state has total mass one. *)
Lemma state_discard {x : C} (s : state x) :
  discard[x] ∘ s ≈ id[I].
Proof. apply (@unit_terminal C _ markov_semicartesian). Qed.

Definition marginal_left {x y : C} (s : state (x ⨂ y)%object) : state x :=
  @proj_left C _ markov_semicartesian x y ∘ s.

Definition marginal_right {x y : C} (s : state (x ⨂ y)%object) : state y :=
  @proj_right C _ markov_semicartesian x y ∘ s.

#[export] Program Instance marginal_left_respects {x y : C} :
  Proper (equiv ==> equiv) (@marginal_left x y).
Next Obligation.
  proper.
  unfold marginal_left.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance marginal_right_respects {x y : C} :
  Proper (equiv ==> equiv) (@marginal_right x y).
Next Obligation.
  proper.
  unfold marginal_right.
  rewrites.
  reflexivity.
Qed.

(* Copying then discarding one of the two copies is the identity: the
   comonoid counit laws, with [eliminate] traded for [discard] by
   terminality of [I]. *)

Lemma proj_left_copy {x : C} :
  @proj_left C _ markov_semicartesian x x ∘ copy[x] ≈ id[x].
Proof.
  unfold proj_left.
  rewrite <- markov_discard_eliminate.
  rewrite <- comp_assoc.
  unfold copy, discard, ccomon_delta, ccomon_epsilon.
  rewrite delta_counit_right.
  apply iso_to_from.
Qed.

Lemma proj_right_copy {x : C} :
  @proj_right C _ markov_semicartesian x x ∘ copy[x] ≈ id[x].
Proof.
  unfold proj_right.
  rewrite <- markov_discard_eliminate.
  rewrite <- comp_assoc.
  unfold copy, discard, ccomon_delta, ccomon_epsilon.
  rewrite delta_counit_left.
  apply iso_to_from.
Qed.

(* Both marginals of a copied state recover the state: copying is a
   (synthetic) diagonal coupling. *)

Lemma marginal_left_copy {x : C} (s : state x) :
  marginal_left (copy[x] ∘ s) ≈ s.
Proof.
  unfold marginal_left.
  rewrite comp_assoc.
  rewrite proj_left_copy.
  apply id_left.
Qed.

Lemma marginal_right_copy {x : C} (s : state x) :
  marginal_right (copy[x] ∘ s) ≈ s.
Proof.
  unfold marginal_right.
  rewrite comp_assoc.
  rewrite proj_right_copy.
  apply id_left.
Qed.

End Markov.

Arguments MarkovCategory C {S}.

Section MarkovCartesian.

Context {C : Category}.
Context `{H : @CartesianMonoidal C}.

(* Every cartesian monoidal category is a Markov category: Fox's
   projection laws make the diagonal and [eliminate] a coherent comonoid
   supply ([CD_of_Cartesian]), and the unit is terminal by definition. *)
Program Definition Markov_of_Cartesian :
  @MarkovCategory C
    (@relevance_is_symmetric C (@cartesian_is_relevance C H)) := {|
  markov_is_cd := @CD_of_Cartesian C H;
  markov_semicartesian := @cartesian_is_semicartesian C H
|}.

End MarkovCartesian.
