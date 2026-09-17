Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Pushout.
Require Import Category.Instance.Sets.QuotObj.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.
Require Import Category.Instance.Grp.QuotObj.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.FinSet.Regular.
Require Import Category.Instance.FinSet.Subobject.
Require Import Category.Instance.FinSet.QuotObj.

Generalizable All Variables.

(** * Probe for the three quotient-object witness files

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.7
    Definition 3, printed p. 126.  Issue #446, witness half.  The targets
    are Instance/Sets/QuotObj.v, Instance/Grp/QuotObj.v and
    Instance/FinSet/QuotObj.v.

    The import list above is the UNION of the three targets' own import
    lists, unabbreviated.  A short prefix is what makes a probe pass
    vacuously, so nothing is trimmed even where a require is redundant.

    Each statement asserted below to be refuted has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read: this repo's coqc prints nothing for a
    refutation that holds, so a whole-file rc=0 would establish only THAT
    each command is rejected and never WHY.  Every negative here is
    classified CONVERSION -- "The term eq_refl has type X while it is
    expected to have type Y", with a trailing "(cannot unify A and B)".
    The parenthetical is rendered with the short names in scope, so the
    same refusal prints differently under a different import list.

    The instrument check comes first: a name that does not exist,
    refused for a reason unrelated to any boundary.  Every constant a
    negative names then appears in a positive control outside any
    refutation command, so that a rename cannot leave a negative refused
    for reference-not-found and therefore vacuously green. *)

(** ** Instrument check *)

Fail Check quot_obj_446_no_such_constant.

(** ** Positive controls: every constant the negatives name *)

Check @QuotObj.
Check @SubObj.
Check @SetoidObject.
Check @Sets.
Check @Isomorphism.
Check @to.
Check @quot_cod.
Check @quot_epi.
Check @quot_le.
Check @quot_is_epic.
Check @mk_quot.
Check @quot_meet.
Check @sub_meet.
Check @Sets_HasPushouts.
Check @NatDiscrete.
Check @Sets_Q_parity.
Check @Sets_Q_mod3.
Check @Sets_Q_total.
Check @Sets_quot_epi_surjective.
Check @Sets_quot_of_surjection.
Check @SetsQuotient_QuotObj.
Check @Sets_coimage.
Check @Sets_CoimageOf.
Check @Sets_HasCoimages.
Check @Sets_quot_meet_parity_mod3.
Check @grp_quot_of_normal.
Check @grp_quot_is_quot_by_kernel.
Check @grp_quot_le_of_included.
Check @finset_quot_epi_surjective.
Check @finset_quot_of_surjection.
Check @finset_coimage.
Check @FinSet_CoimageOf.
Check @FinSet_HasCoimages.
Check @finset_merge01.
Check @finset_merge12.
Check @finset_q01.
Check @finset_q12.
Check @finset_q_meet.
Check @fin4_0.
Check @fin4_2.
Check @fin4_3.

(** ** Positive controls for the computing readbacks themselves *)

(* The pushout of "identify {0,1}" and "identify {1,2}" over the
   four-element set has TWO classes, by [eq_refl]. *)
Example p446_meet_two : quot_cod finset_q_meet = 2%nat := eq_refl.

Example p446_meet_merges :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_2 := eq_refl.

Example p446_coimage_three :
  quot_cod (finset_coimage finset_merge01) = 3%nat := eq_refl.

(** ** N1 -- the meet has two classes and not three (CONVERSION) *)

(* Guards [finset_quot_meet_two].  A probe against the right number
   alone would pass for a construction that did not reduce at all; this
   one pins that the number is computed and is 2. *)
Fail Example p446_n1 : quot_cod finset_q_meet = 3%nat := eq_refl.

(** ** N2 -- the meet does not collapse everything (CONVERSION) *)

(* Guards [finset_quot_meet_separates_0_3] at the strongest reading: 0
   and 3 are not identified even up to conversion. *)
Fail Example p446_n2 :
  quot_epi finset_q_meet fin4_0 = quot_epi finset_q_meet fin4_3 := eq_refl.

(** ** N3 -- a coimage is smaller than the codomain it is read in
       (CONVERSION) *)

(* Guards [finset_coimage_merge01_three]: the coimage of a 4 ↠ 3 map is
   3 and not 4, so the construction is not silently the domain. *)
Fail Example p446_n3 :
  quot_cod (finset_coimage finset_merge01) = 4%nat := eq_refl.

Section SetsBoundaries.

Universe o so.
Constraint o < so.

(** ** N4 -- the quotient-object meet is an ≈ and NOT a Leibniz equality
       (CONVERSION) *)

(* Guards the strength of [Sets_quot_meet_parity_mod3].  [QuotObj]
   inherits [SubObj]'s setoid (Theory/Subobject.v) and has no
   antisymmetry, so the theorem holds at ≈ and the same statement at `=`
   is refused. *)
Fail Example p446_n4 :
  @quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
    Sets_Q_parity Sets_Q_mod3 = Sets_Q_total := eq_refl.

(** ** N5 -- a quotient object of C is not a subobject of C (CONVERSION) *)

(* [@QuotObj (C^op) x = @SubObj C x] holds by [eq_refl], C^op^op being C
   on the nose.  Dropping the [^op] must NOT: that is the whole content
   of the definition. *)
Fail Example p446_n5 (X : SetoidObject@{o o}) :
  @QuotObj Sets@{o so} X = @SubObj Sets@{o so} X := eq_refl.

(** ** N6 -- the covariant reading of the setoid is a LEMMA, not a
       conversion (CONVERSION) *)

(* The order [quot_le] unfolds covariantly on the nose, but the SETOID
   does not: [SubObj_Setoid] at [C^op] asks for an isomorphism IN
   [C^op], whose [to] runs the other way.  The covariant spelling below
   is well FORMED at a concrete category -- it elaborates, and the
   refusal is of the [eq_refl] and not of the statement -- so a
   covariant characterization has to be proved, which is what
   Theory/Subobject/Quotient.v's [quot_equiv_iff_iso] does, with its
   corollary [quot_equiv_of_cod_iso] (first proved in the Grp witness
   and lifted at integration) in the direction the Grp witness needs. *)
Fail Example p446_n6 (X : SetoidObject@{o o})
  (q r : @QuotObj Sets@{o so} X) :
  (q ≈ r) = { i : quot_cod q ≅ quot_cod r & to i ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

End SetsBoundaries.
