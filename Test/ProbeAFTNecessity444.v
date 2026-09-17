(** * Probe for the necessity of the solution set condition (issue #444)

    Pins the two universe-instance boundaries that carry this development's
    headline, and nothing else.  Both are measured in the two targets'
    headers; measured is not guarded, which is what this file is for.

    THE BOUNDARY IS THAT ONE LIBRARY CLASS IS INHABITED AT ONE UNIVERSE
    INSTANCE AND REFUTED AT ANOTHER, over one and the same category.
    [Complete] at the SMALL instance (diagram shape strictly below the
    ambient objects) holds of the reversed order on the large ordinals;
    [Complete] at the COLLAPSED instance (shape at the object level) is
    refuted there.  N1-N3 pin the refused side and the [Check]s beside them
    pin the inhabited side, so neither can drift without this file stopping.

    N4 is the sharpest of the four: it feeds the INHABITED instance to the
    constant that REFUTES the collapsed one.  If that ever succeeded the
    development would prove False, so this refutation is the guard on the
    whole two-instances framing.

    N5 records that [Complete_Initial] is inert on the large categories --
    the measurement that redirected the issue -- against the accepted
    control on the thin one, which is Freyd's collapse appearing as a
    universe constraint.

    Each refutation was stripped ONE AT A TIME in a copy of this WHOLE file
    and its refusal read.  Only the STABLE HEAD of each refusal is described
    here, never the trailing clause, which is import-sensitive. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Size.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Category.Adjunction.GAFT.Necessity.
Require Import Category.Instance.Ordinal.Large.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Limit.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(* instrument: the refutation keyword is live in this file *)
Fail Check probe444_absent_name.

(** ** The inhabited side, as positive controls *)

Check SmallOrd_op_Complete.
Check SmallOrd_self_limit.
Check SmallOrd_no_greatest.
Check SmallOrd_op_not_large_complete.

(** ** N2-N3: [Complete] is refused wherever the collapsed instance is forced *)

(* An ascription alone does NOT pin the instance, and the first draft of this
   probe got that wrong: [Definition _ : @Complete SmallOrd_op_Proset :=
   SmallOrd_op_Complete.] is ACCEPTED, because Coq is free to instantiate the
   ascription's universes at the small instance.  So the collapsed instance
   has to be forced by a CONSUMER that demands it, which is what N2 and N4
   do.  That mistaken first draft is recorded rather than deleted, because
   "refuted by ascription" is the tempting wrong way to state this boundary.

   N2: [Complete_Initial] demands the collapsed instance, and the ordinals'
   small-instance witness does not meet it. *)
Fail Check (Complete_Initial SmallOrd_op_Complete).

(* N3: the same for the tree's large witnesses, which is what makes N5's
   control the only accepted one. *)
Fail Check (Complete_Initial Sets_Complete).
Fail Check (Complete_Initial Grp_Complete).
Fail Check (Complete_Initial Ab_Complete).

(** ** N4: the two instances cannot be fed to each other

    This is the guard on the whole framing.  [SmallOrd_op_not_large_complete]
    takes the COLLAPSED instance and returns [False]; [SmallOrd_op_Complete]
    inhabits the SMALL one.  If the application below ever went through, the
    development would prove [False]. *)

Fail Definition p444_boom : False :=
  SmallOrd_op_not_large_complete SmallOrd_op_Complete.

(** ** N5: the accepted control — Freyd's collapse, and only it *)

Section ThinWitness.
Context (X : SetoidObject).
(* ACCEPTED: the thin powerset lattice is large-complete, and is the one
   witness in tree that is. *)
Check (Complete_Initial (Subsets_Complete (X:=X))).
End ThinWitness.

(** ** Guard block *)

Check @ConstOne.
Check @ConstOne_continuous.
Check @ConstOne_representable_iff_initial.
Check @ConstOne_not_representable.
Check @Complete_Initial.
(* NOTE: [Initial] is a NOTATION (Structure/Initial.v), so writing
   [Check @Initial_of_limit_id.] makes the parser read the notation applied
   to [_of_limit_id] and report that reference as absent.  The qualified
   name sidesteps it. *)
Check Category.Adjunction.GAFT.Necessity.Initial_of_limit_id.
Check @SmallShapeComplete.
Check @SmallOrd.
Check @ole.
Check @ojoin.
Check @SmallOrd_op_Proset.
Check @Subsets_Complete.
