Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * FinSet is an elementary topos

    This is the campaign's genuine elementary-topos WITNESS: skeletal
    FinSet carries every component of [Structure/Topos.v] — terminal
    object, binary products, pullbacks, exponentials, and a subobject
    classifier — with ALL data computable (the codecs of
    [Instance/FinSet/{Product,Closed,Classifier}.v] are structural
    fixpoints, so closed instances reduce by [eq_refl]) and no universe
    subtleties: every object is a [nat].  The Sets story is deliberately
    the cross-universe THEOREM file ([Instance/Sets/Classifier.v]); the
    honest, universe-clean witness lives here. *)

(* Deliberately a plain Definition, NOT an Existing Instance: the five
   topos_* projections are Existing Instances, and the component
   structures (FinSet_Terminal, FinSet_Cartesian, ...) are already
   registered directly, so registering the bundle too would give
   typeclass search two convergent resolution paths for each component.
   Consumers pass FinSet_Topos explicitly, as the Examples below do. *)
Definition FinSet_Topos : ElementaryTopos FinSet := {|
  topos_terminal   := FinSet_Terminal;
  topos_cartesian  := FinSet_Cartesian;
  topos_pullbacks  := FinSet_Pullbacks;
  topos_closed     := FinSet_Closed;
  topos_classifier := FinSet_Classifier
|}.

(** ** Sanity checks: the topos data COMPUTES

    The power object of the 2-element set is Ω ^ 2 = 2 ^ 2 = the
    4-element set, by [eq_refl] — the exponential codec of
    [Instance/FinSet/Closed.v] is a closed nat power. *)

Example FinSet_Pow_two : @Pow FinSet FinSet_Topos 2%nat = 4%nat := eq_refl.

Example FinSet_Pow_zero : @Pow FinSet FinSet_Topos 0%nat = 1%nat := eq_refl.

(** The truth point evaluates to [fin_true] on the sole element of 1. *)

Example FinSet_truth_computes :
  @truth FinSet FinSet_Terminal FinSet_Classifier Fin.F1 = fin_true
  := eq_refl.

(** The characteristic morphism of the point [truth : 1 ~> 2] itself:
    it classifies the subobject {true} ⊆ Ω, so it is the identity
    predicate on truth values — [fin_true ↦ fin_true],
    [fin_false ↦ fin_false] — and both cases reduce by [eq_refl],
    because [char] of [Instance/FinSet/Classifier.v] is a boolean
    search over the (here one-element) domain. *)

Definition point_true : 1%nat ~{FinSet}~> 2%nat := fun _ => fin_true.

Lemma point_true_monic : Monic point_true.
Proof.
  apply finset_monic_iff_injective; intros a b _.
  exact (eq_trans (fin1_unique a) (eq_sym (fin1_unique b))).
Qed.

Example FinSet_char_at_true :
  char point_true point_true_monic fin_true = fin_true := eq_refl.

Example FinSet_char_at_false :
  char point_true point_true_monic fin_false = fin_false := eq_refl.

(** Membership at the power object: [eval : Pow 2 × 2 ~> Ω] applied to
    the code 2 of the "negation" subset-of-truth-values (the digit
    string [fin_false, fin_true]) at the element [fin_true] yields
    [fin_false], by [eq_refl] — the computability claim is real all the
    way through the derived combinators. *)

Example FinSet_Pow_membership :
  @eval FinSet FinSet_Cartesian FinSet_Closed 2%nat
        (@Ω FinSet FinSet_Terminal FinSet_Classifier)
    (fin_pair (Fin.FS (Fin.FS Fin.F1) : Fin.t 4) fin_true)
    = fin_false := eq_refl.
