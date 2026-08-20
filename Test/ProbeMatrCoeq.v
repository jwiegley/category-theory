Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Matr.Elimination.
Require Import Category.Instance.Matr.Coequalizer.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * Probe: strength boundaries of the matrix coequalizer *)

(* Guard file for Instance/Matr/Elimination.v and
   Instance/Matr/Coequalizer.v, in the Test/ProbeFunnyPoly.v convention.

   THE IMPORT LIST ABOVE IS Coequalizer.v's OWN, VERBATIM AND IN ITS
   ORDER, AND THAT IS LOAD-BEARING RATHER THAN TIDINESS.  While drafting
   these negatives, two candidates PASSED for the wrong reason under a
   shortened import list: they failed at ELABORATION (a missing constant)
   instead of at UNIFICATION, so the [Fail] succeeded while measuring
   nothing at all.  A probe that cannot elaborate its own statement is
   not a probe.  Note in particular that [Coq.QArith.QArith] must come
   BEFORE [Category.Lib] -- QArith exports an [equiv] that shadows
   Lib/Setoid.v's, and with the other order every [Proper (equiv ==> ...)]
   in scope fails to elaborate.

   Every negative below is paired with a positive control NAMING ITS OWN
   CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
   constants appearing in the NEGATIVES -- not merely over those the
   controls happen to name, which is the narrower check that let three
   unguarded negatives ship in an earlier probe file in this tree.

   All SEVEN negatives here are CONVERSION negatives ([Fail Definition
   ... := eq_refl]); this file states no formability negative, so no
   lexical separation is needed.  Each was stripped of its [Fail] once
   and the resulting message inspected; every one reports a genuine
   "cannot unify". *)

(** ** Instrument check

    A [Fail] that must itself fail, so a globally broken [Fail]
    vernacular would be caught here rather than silently greening the
    negatives below.  This is the INSTRUMENT, not one of the seven
    negatives. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** The Qed-opaque decider

    THE SHARPEST MEASUREMENT IN THIS FILE, and it was found by a refuted
    probe rather than anticipated.  [Instance/Field.v]'s [F2_Field_dec]
    (:534) and [Q_Field_dec] (:410) are [Qed] lemmas.  They inhabit the
    decidability hypothesis perfectly well -- the engine is TOTAL and
    CORRECT when fed them -- but nothing REDUCES through an opaque
    constant, so the coequalizer object does not compute.  Elimination.v
    and Coequalizer.v therefore use transparent copies ([f2_dec], [q_dec],
    [Defined]) for every [eq_refl] witness.

    This is a fact about opacity, NOT about the mathematics: the negative
    and its control below differ ONLY in which decider is supplied. *)

Fail Definition probe_qed_decider_blocks :
  matr_coeq_obj F2_Field F2_Field_dec coeq_f2_A coeq_f2_B = 1%nat
  := eq_refl.

Definition probe_pos_transparent_decider_computes :
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_B = 1%nat
  := eq_refl.

(** ** No normal form for the coequalizing map

    The next three are three faces of one fact: this development
    computes A coequalizing map, not a NORMALISED one, and [delta] is
    stuck under a free index.  Entrywise agreement holds; whole-function
    Leibniz equality does not. *)

Fail Definition probe_map_is_identity :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A
    = mat_id F2_Field 2 := eq_refl.

Fail Definition probe_map_is_h :
  coeq_f2_map = coeq_f2_h := eq_refl.

Fail Definition probe_map_is_const :
  coeq_f2_map = ((fun _ _ => true) : 2%nat ~{Matr F2_Field}~> 1%nat)
  := eq_refl.

(* Positive control naming Coequalizer.v's own agreement lemma: the two
   maps DO agree entrywise, so the refutations above are about
   whole-function equality and not about the maps differing in value. *)
Definition probe_pos_map_agrees_at :
  coeq_f2_map F1 F1 = coeq_f2_h F1 F1 := eq_refl.

(** ** The op-bridge is not a definitional identity of records

    Reduction.v (#326) proved abstractly that [IsCoequalizer] and
    [IsEqualizer (C^op)] are distinct record types though their fields
    are convertible.  This CONFIRMS that abstract negative at a CONCRETE
    category, which the abstract statement alone does not do. *)

Fail Definition probe_op_record_identity :
  IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map
    = @IsEqualizer ((Matr F2_Field)^op) 2%nat 1%nat
        coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map := eq_refl.

(* Positive control naming the bridge constant itself. *)
Definition probe_pos_op_bridge :
  @IsEqualizer ((Matr F2_Field)^op) 2%nat 1%nat
    coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map
  := IsEqualizer_op_of_IsCoequalizer coeq_f2.

(** ** Elimination.v: the engine's own boundaries *)

Section EliminationNegatives.

Context (K : FieldObject).
Context (a b : nat).
Context (A : Matrix K a b).

(* The identity acts as a unit only up to [≈]; [mat_mul] does not
   reduce a Kronecker [delta] against a free matrix. *)
Fail Definition probe_mat_id_l_strict :
  mat_mul K (mat_id K a) A = A := eq_refl.

Fail Definition probe_mat_sub_self_strict :
  mat_sub K A A = mat_zero K := eq_refl.

End EliminationNegatives.

(* Positive controls naming Elimination.v's own constants, so a rename or
   a statement change in the engine breaks this file loudly. *)
Definition probe_pos_mat_id_l (K : FieldObject)
  (Kdec : forall a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b -> False))
  (a b : nat) (A : Matrix K a b) :
  mat_mul K (mat_id K a) A ≈ A := mat_mul_id_l K Kdec A.

(** ** Controls for constants that appear ONLY inside negatives

    The rename simulation over the constants occurring in the NEGATIVES
    (not merely those the controls happened to name) found FIVE that no
    control mentioned -- [F2_Field_dec], [matr_coeq_map], [IsCoequalizer],
    [mat_sub] and [mat_zero].  Renaming any of them left this file
    compiling and turned its negative vacuously green.  The controls
    below are the repair, and they are recorded here rather than quietly
    added because this is the THIRD probe file in this tree to ship with
    that same gap. *)

Check F2_Field_dec.

Check (matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_B).

Check (IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map).

Check (fun (K : FieldObject) (a b : nat) (A : Matrix K a b) =>
         mat_sub K A A).

Check (fun (K : FieldObject) (a b : nat) => @mat_zero K a b).

(** ** Positive controls for the headline artifacts

    These name the two principal constants directly, so that neither can
    be renamed or restated without this file failing. *)

Check (matr_IsCoequalizer F2_Field f2_dec coeq_f2_A coeq_f2_B).

Check (Matr_HasCoequalizers F2_Field f2_dec).

Check (left_null_basis F2_Field f2_dec).

Check (left_null_basis_diff F2_Field f2_dec).

(* Non-degeneracy, named so the witness cannot silently become trivial:
   the coequalizing map is epic but NOT monic, so it is a proper
   quotient rather than an isomorphism in disguise. *)

Check coeq_f2_map_epic.

Check coeq_f2_map_not_monic.

Check coeq_f2_obj_not_zero.

Check coeq_f2_obj_not_two.
