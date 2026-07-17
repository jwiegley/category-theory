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

(* Where Markov categories come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/Stoch
   nLab:  https://ncatlab.org/nlab/show/Giry+monad

   The category that gives the subject its name is Stoch: objects are
   measurable spaces, morphisms are Markov kernels, identities are Dirac
   kernels, and composition is Chapman–Kolmogorov integration.  It precedes
   the axiomatics by decades: Lawvere circulated "The category of
   probabilistic mappings" as a manuscript in 1962, and Chentsov built the
   same category independently for statistics (Chentsov, "The categories of
   mathematical statistics", Dokl. Akad. Nauk SSSR 164, 1965).  Stoch is
   the Kleisli category of the Giry monad (Giry, 1982, following Lawvere),
   and Kleisli categories of probability monads remain the standard source
   of models, alongside FinStoch for discrete probability and Gauss for
   Gaussian maps.  None of these is formalized in this library; the sole
   in-tree instance route is [Markov_of_Cartesian], so Stoch stands here as
   the intended model rather than a constructed one.

   The axiomatics was discovered twice before it was named, for unrelated
   ends.  Golubtsov axiomatized "categories of information transformers" —
   monoidal categories containing a deterministic subcategory with finite
   products — for informativeness comparison and decision problems
   (Golubtsov, "Axiomatic description of categories of information
   transformers", Problemy Peredachi Informatsii 35(3):80–98, 1999), while
   Corradini and Gadducci reached the same copy/discard structure from
   term-graph rewriting, with no probabilistic intent (the gs-monoidal
   citation in Structure/Monoidal/CopyDiscard.v).  Cho and Jacobs then made
   the structure carry probability proper, expressing disintegration and
   Bayesian inversion as string diagrams (their paper cited above, first
   posted 2017), and Fritz's paper coined the name and set the program; its
   abstract presents the framework as following work of Golubtsov as well
   as Cho and Jacobs.  The boundary theorem predates the field: Fox proved
   in 1976 that natural coherent copying forces cartesianness (Fox,
   "Coalgebras and cartesian categories", Comm. Algebra 4(7):665–667, 1976;
   Structure/Monoidal/Markov/Fox.v), which is why the absent naturality of
   [copy] noted above is the load-bearing design decision.

   The program the name announces is synthetic probability: a theorem
   proved once from the axioms holds in every model — discrete,
   measure-theoretic, Gaussian — with the measure theory quarantined inside
   the model construction.  Fritz's founding paper derives the
   Fisher–Neyman factorization theorem and the theorems of Basu and Bahadur
   on sufficient statistics; later work recovers the Kolmogorov and
   Hewitt–Savage zero-one laws (Fritz & Rischel, "Infinite products and
   zero-one laws in categorical probability", Compositionality 2:3, 2020),
   de Finetti's theorem on exchangeable sequences (Fritz, Gonda & Perrone,
   "De Finetti's theorem in categorical probability", J. Stochastic
   Analysis 2(4):6, 2021), and the ergodic decomposition theorem (Moss &
   Perrone, "A category-theoretic proof of the ergodic decomposition
   theorem", Ergodic Theory Dynam. Systems 2023).  Beyond probability
   itself, an abstract form of the d-separation criterion of graphical
   causal models is proved at this generality, for possibilistic and
   deterministic networks alongside probabilistic ones (Fritz & Klingler,
   "The d-separation criterion in categorical probability", JMLR
   24(46):1–49, 2023); a probabilistic language with exact conditioning
   takes its denotational semantics in categories built from the Markov
   categories Gauss and FinStoch (Stein & Staton, "Compositional semantics
   for probabilistic programs with exact conditioning", LICS 2021); and
   Shannon and Rényi entropy are characterized as measures of how far a
   morphism is from being deterministic (Perrone, "Markov categories and
   entropy", IEEE Trans. Inf. Theory 70(3), 2024).

   Computationally, a morphism is a call to a randomized procedure, and
   the two halves of the structure say what may be reordered around the
   call.  The discard half — running a computation and ignoring its result
   is the same as not running it — holds for every morphism by
   [discard_natural] and is the discard square of thunkability in
   Monad/Thunkable.v.  The copy half separates let x = f a in (x, x) from
   (f a, f a): one sample shared between two uses against two samples
   drawn independently.  Morphisms for which the two agree are exactly the
   deterministic ones ([deterministic] in
   Structure/Monoidal/CopyDiscard/Deterministic.v, with the wide
   subcategory [Det]), and the [state]/[marginal_left]/[marginal_right]
   vocabulary below makes the distinction speakable: copying a state
   yields a perfectly correlated joint, both of whose marginals return the
   original state ([marginal_left_copy], [marginal_right_copy]), not an
   independent pair. *)

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
