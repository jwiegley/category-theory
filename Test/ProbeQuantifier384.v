Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Powerset.Quantifier.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Probe for Instance/Powerset/Quantifier.v (issue #384)

    Every boundary that file's header MEASURES is pinned here, from
    OUTSIDE it: an in-file [Fail] renames in lockstep with the constant
    it guards and so cannot detect a rename.  The [Require] list above
    is the target's own, plus the target.

    SIX NEGATIVES OF THREE KINDS -- four CONVERSION, one TYPING, one
    FORMABILITY -- told apart by the error TEXT rather than by label,
    plus one scope-free instrument check.  Each was stripped of its
    [Fail] ONE AT A TIME, compiled alone, and its whole error read; the
    typing one reports a plain "has type ... while it is expected to
    have type" with NO "cannot unify" and no universe clause, the four
    conversion ones end in "cannot unify", and the formability one ends
    in "universe inconsistency: Cannot enforce pr = po".

      1 CONVERSION -- [GaloisFunctor_l] of the new connection is not
        [InverseImage f].  "cannot unify"; the two functor records have
        the same [fobj] and the same [fmap] (controls below) and differ
        only in their three opaque law fields, which is why the headline
        is built with [proset_adjunction_at] rather than with #380's
        [GaloisAdjunction].

      2 CONVERSION -- [proj_exists S] is not [Powerset_Prop_image] along
        the projection.  "cannot unify"; the [≈] form is the target's
        [proj_exists_is_image] and the pointwise disagreement is real,
        an [ex] against a [Powerset_squash] of a [sigT].

      3 CONVERSION -- [proj_forall S] is not [Powerset_Prop_dual] along
        the projection.  Same shape: the two quantify over different
        carriers.

      4 CONVERSION -- [Subsets 1] and [Props] are not the same category:
        their OBJECT types differ, an [equiv]-respecting predicate on the
        point against a bare [Prop].  So the target's
        [subsets_one_Props], which is an [≅[Cat]] and hence an
        EQUIVALENCE in this library, cannot be strengthened to an
        identity of categories, and the target's header says so.

    A NEGATIVE THAT DID NOT FIRE, RECORDED RATHER THAN REMOVED SILENTLY.
    The first cut of this probe carried, as negative 4, the refutation of
    Beck-Chevalley at WHOLE-SUBSET Leibniz equality, and it did not fire.
    The equality holds, the target now ships it at that grade
    ([beck_chevalley_exists]/[beck_chevalley_forall]), the probe carries
    it as a POSITIVE, and both headers record the reason.  The
    replacement negative 4 above is the [Subsets 1]-vs-[Props] one.

      5 TYPING -- the headline adjunction cannot be ascribed at the
        reversed handedness.  A plain "has type ... while it is expected
        to have type"; its tail does mention the two functors, so the
        kind is read off the whole message and not off the tail.

      6 FORMABILITY -- [Powerset_Prop_obj] does not accept a setoid whose
        carrier and relation universes are declared apart.  "Universe
        inconsistency"; the carrier and the setoid structure of that very
        argument ARE accepted at those levels, which is what makes the
        rejection attributable to [Powerset_Prop_obj] rather than to the
        argument.  It is probed FIRST, before [Powerset_Prop_dual], for
        the reason #340 records: a probe aimed at the derived constant
        would be rejected at its [Powerset_Prop_obj] argument and would
        measure nothing of its own. *)

(* ------------------------------------------------------------------------ *)
(** ** Instrument check *)

(* [Fail] must be able to see a rejection at all.  Scope-free: no constant
   of the target occurs in it, so no rename can silence it. *)
Fail Check (probe_instrument_absent_384 : nat).

(* ------------------------------------------------------------------------ *)
(** ** Controls: every constant the negatives name, outside a [Fail] *)

Check @Powerset_Prop_dual.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_image.
Check @Powerset_Prop_preimage.
Check @DualImage.
Check @InverseImage.
Check @DirectImage.
Check @GaloisFunctor_l.
Check @GaloisFunctor_r.
Check @subset_le_preorder.
Check @preimage_dual_galois.
Check @substitution_forall_adjunction.
Check @exists_substitution_adjunction.
Check @image_preimage_adjunction.
Check @proj_exists.
Check @proj_forall.
Check @proj_fst.
Check @ProdSetoid.
Check @cylinder.
Check @cyl_reindex.
Check @quantifier_triple.
Check @forall_unit_incl.
Check @forall_counit_incl.
Check @proset_adjunction_at.
Check @gal_r_preserves_glb.
Check @gal_l_preserves_lub.
Check @carrier.
Check @is_setoid.
Check @subsets_one_Props.
Check @Delta_X.
Check @exists_X.
Check @forall_X.
Check @quant_one.
Check @quant_bang.
Check @exists_not_right_adjoint.
Check @forall_not_left_adjoint.
Check @dual_image_not_join_preserving.
Check @beck_chevalley_exists_mem.
Check @beck_chevalley_exists.

(* ------------------------------------------------------------------------ *)
(** ** (1) The two preimage functors are different RECORDS *)

Section GaloisFunctorRecord.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* POSITIVE: the object actions agree on the nose ... *)
Example p384_fobj_agrees (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[GaloisFunctor_l (subset_le_preorder@{o} Y)
         (subset_le_preorder@{o} X) (preimage_dual_galois f)] T
    = fobj[InverseImage f] T := eq_refl.

(* ... and so do the arrow actions. *)
Example p384_fmap_agrees (T T' : carrier (Powerset_Prop_obj@{o} Y))
  (h : subset_le T T') :
  @fmap _ _ (GaloisFunctor_l (subset_le_preorder@{o} Y)
               (subset_le_preorder@{o} X) (preimage_dual_galois f)) T T' h
    = @fmap _ _ (InverseImage f) T T' h := eq_refl.

(* NEGATIVE 1 (CONVERSION).  The WHOLE records do not: the three law
   fields are separate opaque [Program] obligations. *)
Fail Example p384_functor_records_agree :
  GaloisFunctor_l (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (preimage_dual_galois f)
  = InverseImage f := eq_refl.

(* NEGATIVE 5 (TYPING).  The headline runs [InverseImage f ⊣ DualImage f]
   and cannot be ascribed the other way round. *)
Fail Example p384_reversed_handedness :
  DualImage f ⊣ InverseImage f := substitution_forall_adjunction f.

(* POSITIVE: the pinned existential leg IS #382's adjunction. *)
Example p384_exists_leg_is_donor :
  exists_substitution_adjunction f = image_preimage_adjunction f := eq_refl.

(* POSITIVE: the unit and the counit ARE Mac Lane's two inclusions. *)
Example p384_unit_is_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  @unit _ _ (InverseImage f) (DualImage f)
    (substitution_forall_adjunction f) T = forall_unit_incl f T := eq_refl.

Example p384_counit_is_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  @counit _ _ (InverseImage f) (DualImage f)
    (substitution_forall_adjunction f) S = forall_counit_incl f S := eq_refl.

End GaloisFunctorRecord.

(* ------------------------------------------------------------------------ *)
(** ** (2), (3) Mac Lane's two operations against the general ones *)

Section ProjectionGrades.

Universe o so u.
Constraint o < so.

Context (U V : SetoidObject@{o o}).
Context (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))).

(* NEGATIVE 2 (CONVERSION). *)
Fail Example p384_exists_is_image_strict :
  @proj_exists@{o so} U V S
    = Powerset_Prop_image@{o} (proj_fst@{o so} U V) S := eq_refl.

(* NEGATIVE 3 (CONVERSION). *)
Fail Example p384_forall_is_dual_strict :
  @proj_forall@{o so} U V S
    = Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S := eq_refl.

(* POSITIVE: the [≈] forms hold, and are the target's. *)
Check (proj_exists_is_image U V S).
Check (proj_forall_is_dual U V S).

(* POSITIVE: the cylinder IS the inverse image along the projection, on
   the nose -- so the two negatives above are about [proj_exists] and
   [proj_forall] and not about the projection. *)
Example p384_cylinder_is_preimage
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  @cylinder@{o so} U V Xs
    = Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs := eq_refl.

End ProjectionGrades.

(* ------------------------------------------------------------------------ *)
(** ** (4) Beck-Chevalley: pointwise yes, whole-subset no *)

Section BeckGrades.

Universe o so.
Constraint o < so.

Context (U U' V : SetoidObject@{o o}).
Context (g : U' ~{Sets@{o so}}~> U).
Context (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))).

(* POSITIVE: pointwise, at [eq_refl]. *)
Example p384_beck_pointwise (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S) x
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x := eq_refl.

(* POSITIVE: and at the WHOLE SUBSET too, which is what the target
   ships.  This was measured, not assumed: a first draft of the probe
   pinned its refutation as a negative and that guard did not fire. *)
Example p384_beck_whole_subset :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) := eq_refl.

(* POSITIVE: the [≈] reading is the target's. *)
Check (beck_chevalley_exists_equiv U U' V g S).
Check (beck_chevalley_exists U U' V g S).

End BeckGrades.

(* ------------------------------------------------------------------------ *)
(** ** (4) [Subsets 1] is EQUIVALENT to [Props], not isomorphic to it *)

Section OmegaGrades.

Universe o so u.
Constraint o < so.

(* POSITIVE: the equivalence is the target's, and both round trips hold.
   The two CATEGORIES and their two object types are [Check]ed here as
   well, so that a rename of [Subsets] or of [Props] breaks this section
   at a control rather than turning the negative below vacuously green --
   before these four lines they occurred outside the [Fail] only in
   prose. *)
Check subsets_one_Props.
Check subsets_one_Props_round.
Check Props_subsets_one_round.
Check (Subsets@{o u} quant_one@{o so}).
Check Props@{o u}.
Check (obj[Subsets@{o u} quant_one@{o so}]).
Check (obj[Props@{o u}]).

(* NEGATIVE 4 (CONVERSION).  The two categories are not the same object:
   an object of [Subsets 1] is an [equiv]-respecting predicate, an object
   of [Props] is a [Prop].  So the [≅[Cat]] the target ships -- which in
   this library IS equivalence -- cannot be strengthened to an identity,
   and the header says so. *)
Fail Example p384_subsets_one_is_Props :
  obj[Subsets@{o u} quant_one@{o so}] = obj[Props@{o u}] := eq_refl.

End OmegaGrades.

(* ------------------------------------------------------------------------ *)
(** ** (6) The donors' universe identification *)

Section UniverseBoundary.

Universe po pr.
Constraint pr < po.

Context (A : SetoidObject@{po pr}).

(* POSITIVE controls at the very same declared levels: the argument's
   carrier and its setoid structure are both fine. *)
Check (carrier A).
Check (is_setoid A).
Check (A : Type@{po}).

(* NEGATIVE 6 (FORMABILITY).  [Powerset_Prop_obj@{o}] wants
   [SetoidObject@{o o}], one level for both. *)
Fail Check (Powerset_Prop_obj A).

End UniverseBoundary.

(* ------------------------------------------------------------------------ *)
(** ** Riehl's triple, and the truth-value comparison, exercised *)

Section RiehlChecks.

Universe o so u.
Constraint o < so.

Context (X : SetoidObject@{o o}).

Check (Delta_X X).
Check (exists_X X).
Check (forall_X X).
Check (riehl_exists_delta X).
Check (riehl_delta_forall X).
Check (riehl_adjoint_triple X).
Check (Delta_X_obj_mem X).

End RiehlChecks.

Check @subsets_one_to_Props.
Check @Props_to_subsets_one.
Check @subsets_one_Props_round.
Check @Props_subsets_one_round.
