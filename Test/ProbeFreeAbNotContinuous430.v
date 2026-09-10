(** * Probe for Instance/Ab/FreeNotContinuous.v (issue #430)

    Pins the measured boundaries of the discontinuity witness with
    negatives of three kinds, kept lexically apart: CONVERSION (N1-N3: the
    identifications the proofs use — the image of the point's terminal
    arrow is [id], the image legs are [id], the free group on a point is
    not the zero group — hold at [≈] or as theorems, never on the nose);
    TYPING (N4-N5: the cone-level refutations do not ascribe at the
    apex-only classes — [ContinuousFunctor] against [PreservesAllLimits],
    and the binary witness against [PreservesLimit] — so the header's
    "only the empty shape reaches the apex level" is a measured boundary);
    UNIVERSE (N6-N8: [Ab_trivial], [Ab_Terminal] and [Ab_Cartesian] are
    refused at a hom level strictly above [Set] while [Ab] and [Ab_Forget]
    are accepted there — the [Set] pin is the trivial group's, Instance/
    Ab.v:227, not the category's).  Three [eq_refl] readbacks (the carrier
    of the free group on a point, the binary diagram's objects, the zero
    endomorphism's value) are positive controls, the last making
    [ab_zero_endo]'s [Defined] load-bearing.  Each refutation was stripped
    one at a time in a copy of the whole file; the import list mirrors the
    target's.  Section D's checks and the guard block are positive
    controls. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Zero.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Free.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Ab.FreeNotContinuous.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe430_absent_name.

(** ** A: CONVERSION — the identifications the proofs use hold at [≈], not
       on the nose *)

(* controls: the [≈] forms are the file's own lemmas *)
Check fmap_one_point.
Check free_ab_one_id_not_zero.

(* N1 CONVERSION: the image of the point's terminal arrow is [id] up to [≈]
   ([fmap_one_point]), not definitionally *)
Fail Example p430_fmap_one_not_definitional :
  fmap[FreeAb] (@one Sets Sets_Terminal SetsPoint) = @id Ab (FreeAb SetsPoint)
  := eq_refl.

(* N2 CONVERSION: the image cone's legs, likewise *)
Fail Example p430_image_leg_not_definitional :
  cone_leg (FCone FreeAb NatOneCone) 0%nat = @id Ab (FreeAb SetsPoint)
  := eq_refl.

(* N3 CONVERSION: the free group on a point is not the zero group — nor is
   it convertible to it; the separation is a theorem, not a computation *)
Fail Example p430_free_on_point_is_not_the_zero_group :
  FreeAb SetsPoint = Ab_trivial := eq_refl.

(** ** B: TYPING — the two strength levels do not ascribe into each other *)

(* controls: each refutation at its own level *)
Check (FreeAb_not_continuous : ContinuousFunctor FreeAb → False).
Check (FreeAb_not_PreservesAllLimits : PreservesAllLimits FreeAb → False).
Check (FreeAb_not_PreservesLimitCone_binary_product
         : PreservesLimitCone BinDiagram FreeAb → False).

(* N4 TYPING: the cone-level conclusion is not the apex-level one — the
   latter needs the empty shape's separate argument *)
Fail Definition p430_cone_level_is_not_apex_level :
  PreservesAllLimits FreeAb → False := FreeAb_not_continuous.

(* N5 TYPING: the binary witness reaches the cone level only *)
Fail Definition p430_binary_witness_is_cone_level_only :
  PreservesLimit BinDiagram FreeAb → False
  := FreeAb_not_PreservesLimitCone_binary_product.

(** ** C: UNIVERSE — the [Set] pin is [Ab_trivial]'s, not [Ab]'s *)

Monomorphic Universe uo uh.
Monomorphic Constraint Set < uh.
Monomorphic Constraint uh < uo.

(* controls: the category and its forgetful functor form at a hom level
   strictly above [Set] *)
Check (Ab@{uo uh} : Category@{uo uh uh}).
Check (Ab_Forget@{uo uh}).

(* N6-N8 UNIVERSE: everything assembled from the trivial group is pinned
   at [Set] *)
Fail Check (Ab_trivial : AbObject@{uh uh uh}).
Fail Check (Ab_Terminal : @Terminal Ab@{uo uh}).
Fail Check (Ab_Cartesian : @Cartesian Ab@{uo uh}).

(** ** D: readbacks *)

Example p430_freeab_is_left_adjoint : FreeAb ⊣ Ab_Forget := free_ab_adjunction.

Example p430_free_ab_one_carrier :
  carrier (Ab_Forget (FreeAb SetsPoint)) = FATerm SetsPoint := eq_refl.

Example p430_bin_diagram_objects : BinOnes true = SetsPoint := eq_refl.

Example p430_zero_endo_value (A : Ab) (a : carrier (cmon_setoid A)) :
  cmon_map (ab_zero_endo A) a = cmon_zero A := eq_refl.

Check FreeAb_not_PreservesLimit_empty.
Check FreeAb_not_PreservesLimitCone_empty.
Check FreeAb_not_PreservesLimitCone_countable_product.
Check FreeAb_binary_comparison_not_iso.
Check FreeAb_not_CartesianFunctor.
Check FreeAb_not_continuous_via_empty.
Check Ab_Forget_Continuous.
Check FreeAb_Cocontinuous.

(** ** Guard block *)

Check @FreeAb.
Check @SetsPoint.
Check @NatOneCone.
Check @BinDiagram.
Check @Ab_trivial.
Check @Ab_Terminal.
Check @Ab_Cartesian.
Check @Ab.
Check @Ab_Forget.
Check @AbObject.
Check @ab_zero_endo.
Check @FreeAb_not_continuous.
Check @FreeAb_not_PreservesLimitCone_binary_product.
Check @PreservesAllLimits.
Check @PreservesLimit.
Check @PreservesLimitCone.
Check @ContinuousFunctor.
Check @cone_leg.
Check @FCone.
Check @fmap.
Check @one.
Check @id.
Check @Terminal.
Check @Cartesian.
Check @Category.
Check @Sets_Terminal.
Check nat.
