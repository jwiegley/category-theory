Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Elements.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(** * A universal element is an initial object of the category of elements *)

(* nLab: https://ncatlab.org/nlab/show/category+of+elements
   Text: Riehl, "Category Theory in Context", Dover 2016, §2.4,
         Proposition 2.4.8

   Riehl's Proposition 2.4.8 is the sharpest form of the universal-element
   idea: a universal element of H : D ⟶ Sets is precisely an INITIAL OBJECT
   of the category of elements of H.  Both notions are already in the tree --
   [AUniversalElement] (Theory/Universal/Element.v) and [Elements]
   (Construction/Elements.v) -- and this file is the two-line-per-direction
   bridge between them.

   It is kept SEPARATE from Theory/Universal/Element.v for the reason
   Theory/Universal/Arrow/Dual/Examples.v is kept separate from its parent:
   the statement costs a dependency on [Structure/Initial.v] and on
   [Construction/Elements.v]'s category (as opposed to its [SetsOne], which
   the parent already uses), and a consumer wanting only the subsumption
   theorem should not inherit them.

   A DOCUMENTATION ERRATUM, found here and REPAIRED IN THE SAME COMMIT at the
   file that carried it.  Instance/Coq/Nat.v used to say its concrete argument
   presents "the category of elements ... concretely as [FAlg NatF] rather
   than built as a general construction, WHICH THE TREE DOES NOT CARRY".  The
   tree does carry it.  The sentence was true when written (30c01af0,
   5 August 2026) and went stale four days later, when
   [Construction/Elements.v] landed (f2177328, 9 August 2026).  Nat.v now
   carries the correction and its own pointer here; no line citation is given
   for it, since the two files move independently.  What remains true is the narrower
   claim -- Nat.v does not USE the general construction, and the comparison
   [Elements Endos_Forget ≃ FAlg NatF] is not in the tree either.  This file
   supplies the general theorem the comment was reaching for; it does not
   supply that comparison, so Nat.v's [repr_initial] is not re-derived here
   and is not made redundant. *)

(* WHAT IS DELIVERED

   [Elements_Initial], [AUniversalElement_of_Elements_Initial] and
   [UniversalElement_of_Elements_Initial], with the object and element kept
   by [eq_refl] in both directions, and the mediating morphism identified
   with the factorization of [aue_universal] ([Elements_zero_is_med]).

   WHAT IS NOT DELIVERED

   No isomorphism of setoids between [AUniversalElement H r] and the
   initial-object structures: [Initial] carries a chosen [one] field, so two
   [Initial (Elements H)] values at the same object need not be equal and
   there is no in-tree setoid on them to state such an iso against.  The
   round trips below are therefore recorded on the DATA (object, element),
   which is what the two directions actually preserve. *)

Section ElementsInitial.

Context {D : Category}.
Context (H : D ⟶ Sets).

(* Forward.  The object (r, e) is initial: the unique arrow to (d, x) is the
   unique k with (H k) e ≈ x, and the [Elements] hom-setoid compares only
   the underlying D-morphism, so uniqueness there IS [uniqueness]. *)
(* Built with [unshelve refine] rather than [Program] so that the names in
   the uniqueness obligation are this file's and not the elaborator's. *)
Definition Elements_Initial {r : D} (U : AUniversalElement H r)
  : @Initial (Elements H).
Proof.
  unshelve eapply (@Build_Terminal ((Elements H)^op)).
  - exact ((r; @aue_elem D H r U) : Elements H).
  - intros [d elt].
    exists (unique_obj (aue_universal d elt)).
    exact (unique_property (aue_universal d elt)).
  - intros [d elt] [f Hf] [g Hg]; simpl in *.
    transitivity (unique_obj (aue_universal d elt)).
    + symmetry; exact (uniqueness (aue_universal d elt) f Hf).
    + exact (uniqueness (aue_universal d elt) g Hg).
Defined.

(* The mediating arrow IS the factorization, by conversion. *)
Lemma Elements_zero_is_med {r : D} (U : AUniversalElement H r) (d : D) (x : H d) :
  `1 (@zero (Elements H) (Elements_Initial U) ((d; x) : Elements H))
    = unique_obj (aue_universal d x).
Proof. reflexivity. Qed.

(* Backward.  The initial object's two projections are the universal object
   and the universal element; its [zero] is the factorization and
   [zero_unique] its uniqueness.  The only step with content is that the
   carried condition [`2 (zero ...)] is exactly the required equation. *)
Definition AUniversalElement_of_Elements_Initial (I : @Initial (Elements H))
  : AUniversalElement H (`1 (@initial_obj (Elements H) I)).
Proof.
  unshelve econstructor.
  - exact (`2 (@initial_obj (Elements H) I)).
  - intros d x.
    unshelve eexists (`1 (@zero (Elements H) I ((d; x) : Elements H))).
    + exact (`2 (@zero (Elements H) I ((d; x) : Elements H))).
    + intros v Hv.
      exact (@zero_unique (Elements H) I ((d; x) : Elements H)
               (@zero (Elements H) I ((d; x) : Elements H)) (v; Hv)).
Defined.

Definition UniversalElement_of_Elements_Initial (I : @Initial (Elements H))
  : UniversalElement H :=
  UniversalElement_of_AUniversalElement
    (AUniversalElement_of_Elements_Initial I).

(* Both directions keep the data on the nose. *)
Corollary Elements_Initial_obj {r : D} (U : AUniversalElement H r) :
  `1 (@initial_obj (Elements H) (Elements_Initial U)) = r.
Proof. reflexivity. Qed.

Corollary Elements_Initial_elem {r : D} (U : AUniversalElement H r) :
  `2 (@initial_obj (Elements H) (Elements_Initial U)) = @aue_elem D H r U.
Proof. reflexivity. Qed.

Corollary aue_of_Elements_Initial_elem (I : @Initial (Elements H)) :
  @aue_elem D H _ (AUniversalElement_of_Elements_Initial I)
    = `2 (@initial_obj (Elements H) I).
Proof. reflexivity. Qed.

(* ... and the element-side round trip closes by [eq_refl]. *)
Corollary Elements_Initial_round {r : D} (U : AUniversalElement H r) :
  @aue_elem D H _
    (AUniversalElement_of_Elements_Initial (Elements_Initial U))
    = @aue_elem D H r U.
Proof. reflexivity. Qed.

End ElementsInitial.
