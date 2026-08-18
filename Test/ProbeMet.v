(* ========================================================================= *)
(* Machine-checked boundary probes for Instance/Met.v, Instance/Met/          *)
(* Extended.v and Instance/Met/Completion.v.                                 *)
(*                                                                           *)
(* WHY THIS FILE EXISTS.  The three files above make several claims of the    *)
(* form: this holds by conversion; and several of the form: this does NOT     *)
(* hold by conversion, only up to a proof.  A claim of the first kind is      *)
(* guarded by an [eq_refl] in the file itself.  A claim of the second kind    *)
(* is not guarded by anything unless the rejection is pinned, which is what   *)
(* this file does: MEASURED is not GUARDED, and a strictness boundary that    *)
(* nobody re-checks silently moves.                                          *)
(*                                                                           *)
(* THE HYGIENE COST IS STATED, NOT HIDDEN.  Each use of the rejection         *)
(* vernacular is a hit for the [make todo] sweep (Makefile:5 greps            *)
(* case-insensitively over every .v file for a small set of trigger words,    *)
(* one of which is that vernacular's own name).  Confining them here follows  *)
(* Test/Size.v:1-20, Test/Issue138.v:75-76 and Test/ProbeFunnyPoly.v:69,77.   *)
(* This file contributes exactly THREE such hits, and the surrounding prose  *)
(* is worded to avoid the trigger words so the sweep's delta is exactly those *)
(* three commands.                                                           *)
(*                                                                           *)
(* WHAT THE VERNACULAR DOES AND DOES NOT SHOW.  It succeeds when the command  *)
(* it wraps raises ANY error, and it does not report which one, so on its own *)
(* it cannot tell a genuine non-convertibility from a typo or a scope slip.   *)
(* The probes below were therefore checked by hand in the way Test/Size.v     *)
(* prescribes: the wrapper was stripped, the bare command compiled, and the   *)
(* error read to confirm it is a unification error about the intended terms   *)
(* and not something else.  Each is also paired with a POSITIVE CONTROL       *)
(* immediately above it — a closely related statement that DOES close by      *)
(* conversion — so that a probe cannot pass merely because the surrounding    *)
(* vocabulary stopped elaborating.                                           *)
(* ========================================================================= *)

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Met.
Require Import Category.Instance.Met.Extended.
Require Import Category.Instance.Met.Completion.

Generalizable All Variables.

Open Scope R_scope.

(* ===== BLOCK A — the vocabulary elaborates (instrument sanity check) ===== *)

(* If these stopped type-checking, the rejections in Blocks B and C would
   pass for the wrong reason. *)
Check (Met : Category).
Check (CMet : Category).
Check (CMet_Incl : CMet ⟶ Met).
Check (R_Metric : MetricSpace).
Check (Harmonic : MetricSpace).
Check (fun X : MetricSpace => Completion X : MetricSpace).
Check (fun X : MetricSpace => eta X : Isometry X (Completion X)).
Check (fun X : MetricSpace =>
         Completion_AUniversalArrow X
           : AUniversalArrow (X : Met) CMet_Incl (Completion_CMet X)).
Check (TwoFar : ExtMetricSpace).

(* ===== BLOCK B — what IS definitional, and what is not, on the metric ===== *)

(* POSITIVE CONTROL.  The distance of [R_Metric] reduces to the absolute
   difference; Instance/Met.v states this as an [Example] and it is repeated
   here so that Block B's rejection has a live neighbour. *)
Example R_Metric_dist_is_abs (x y : R_Metric) : dist x y = Rabs (x - y) := eq_refl.

(* POSITIVE CONTROL.  The carrier of the completion is the type of Cauchy
   sequences, definitionally. *)
Example Completion_carrier (X : MetricSpace) :
  met_carrier (Completion X) = CauchySeq_Object X := eq_refl.

(* THE BOUNDARY.  The embedding preserves the distance, but NOT by
   conversion: [cdist] is the limit produced by [R_complete], so relating it
   to [dist a b] requires the uniqueness-of-limits argument that
   Instance/Met/Completion.v's [eta_dist] carries out.  Verified by hand:
   stripping the wrapper below reports that it cannot unify
   [dist (eta X a) (eta X b)] with [dist a b], which is the intended
   non-convertibility and not a typo or a scope slip. *)
Fail Example eta_dist_is_definitional (X : MetricSpace) (a b : X) :
  dist (isometry_map (eta X) a) (isometry_map (eta X) b) = dist a b := eq_refl.

(* ... and here is the same statement holding, by proof.  Without this the
   rejection above would be consistent with the statement being false. *)
Example eta_dist_holds_by_proof (X : MetricSpace) (a b : X) :
  dist (isometry_map (eta X) a) (isometry_map (eta X) b) = dist a b.
Proof. exact (isometry_dist (eta X) a b). Qed.

(* ===== BLOCK C — the extended/ordinary round trips are asymmetric ===== *)

(* POSITIVE CONTROL, the strict direction.  Going from a metric space up to
   the extended world and back down along the canonical finiteness witness
   returns the distance on the nose. *)
Example ext_roundtrip_strict (X : MetricSpace) (x y : X) :
  dist (X := Metric_of_EFinite (ExtMetric_of_Metric X)
                               (ExtMetric_of_Metric_EFinite X)) x y
    = dist x y := eq_refl.

(* THE BOUNDARY, the other direction.  Starting from an extended metric
   space and an ARBITRARY finiteness witness [Hfin], the value [efin] reads
   off is [`1 (Hfin x y)], and recovering [edist x y] from
   [RFin (`1 (Hfin x y))] needs [`2 (Hfin x y)] — a proof, not a
   conversion.  Verified by hand: stripping the wrapper below reports that
   it cannot unify [@edist (ExtMetric_of_Metric (Metric_of_EFinite E Hfin))
   x y] with [@edist E x y], which is the intended non-convertibility. *)
Fail Example ext_roundtrip_strict_other (E : ExtMetricSpace) (Hfin : EFinite E)
     (x y : E) :
  edist (X := ExtMetric_of_Metric (Metric_of_EFinite E Hfin)) x y = edist x y
    := eq_refl.

(* ... and the same statement holding, by proof. *)
Example ext_roundtrip_other_by_proof (E : ExtMetricSpace) (Hfin : EFinite E)
        (x y : E) :
  edist (X := ExtMetric_of_Metric (Metric_of_EFinite E Hfin)) x y = edist x y.
Proof. exact (ExtMetric_of_Metric_roundtrip E Hfin x y). Qed.

(* ===== BLOCK D — a DONOR limitation, pinned so its repair is noticed ===== *)

(* Instance/Met/Completion.v's header records that the second generic
   uniqueness route — [univ_property_unique_up_to_unique_iso] reached through
   [UniversalArrowIsUniversalProperty] — could not be taken, and that the
   obstruction belongs to the bridge rather than to metric spaces.  This is
   the evidence for that claim, and it is a statement ABOUT THE DONOR, not
   about this development.

   The control is the identity functor on [Sets] — a trivial instance, but
   NOT the simplest one available: the bridge does elaborate at [_1], [_2]
   and [Cat], so what this probe pins is the rejection at the tree's LARGE
   concrete categories, not a blanket failure.  Verified by hand: stripping
   the wrapper below reports
   a universe inconsistency, of the form "Cannot enforce u = v because
   u < w <= v".  If the bridge's universes are ever repaired this probe
   starts complaining, which is the intended alarm — at that point
   Instance/Met/Completion.v's disclosure should be revisited and the second
   route taken. *)
Fail Check (fun c : Sets => UniversalArrowIsUniversalProperty _ _ (Id[Sets]) c).

(* POSITIVE CONTROL: the bridge's own statement elaborates, so the rejection
   above is about instantiating it and not about the name being absent. *)
Check @UniversalArrowIsUniversalProperty.
Check @univ_property_unique_up_to_unique_iso.

(* ===== BLOCK E — the deferred functor really is obstruction-free ===== *)

(* Instance/Met/Completion.v's header states that the completion functor and
   the adjunction [Completion ⊣ CMet_Incl] follow from the universal arrow
   with no further proof obligation, and that they are left out of the
   library surface by choice rather than by difficulty.  That is a claim
   about what elaborates, so it is checked here rather than asserted there.
   Nothing below is exported: these are local names in a test file, and the
   library gains no new constant from them. *)

Definition probe_CompletionFunctor : Met ⟶ CMet :=
  LeftAdjointFunctorFromUniversalArrows CMet_Incl
    (fun X : Met => Completion_UniversalArrow X).

Definition probe_CompletionAdj : probe_CompletionFunctor ⊣ CMet_Incl :=
  AdjunctionFromUniversalArrows CMet_Incl
    (fun X : Met => Completion_UniversalArrow X).

(* ===== BLOCK F — the negative results are live, not vacuous ===== *)

(* The harmonic space really is incomplete, its completion really does have a
   point outside the image of the embedding, and the two-point space at
   infinite distance really is not an ordinary metric space.  These are
   [Check]s of already-proved statements: their value here is that they fix
   the STATEMENTS, so that a later weakening of any of them (to a vacuous
   hypothesis, say) shows up as a type error in this file. *)
Check (Harmonic_not_MComplete : MComplete Harmonic → False).
Check (Completion_Harmonic_adds_a_point
         : ∃ z : Completion Harmonic,
             ∀ k : Harmonic, isometry_map (eta Harmonic) k ≈ z → False).
Check (TwoFar_not_EFinite : EFinite TwoFar → False).
Check (TwoFar_not_a_metric_space : MetricPresentation TwoFar → False).

(* Mac Lane's parenthetical, and its categorical consequence. *)
Check (fun (X Y : MetricSpace) (f : Isometry X Y) =>
         isometry_injective f
           : ∀ x y : X, isometry_map f x ≈ isometry_map f y → x ≈ y).
Check (fun (X Y : Met) (f : X ~> Y) => Met_all_Monic f : Monic f).
