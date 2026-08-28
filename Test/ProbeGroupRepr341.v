(** * Probe: the universe boundary of Structure/Group/Representable.v

    Issue #341 (Mac Lane CWM 2nd ed. section III.6 Proposition 1 and
    remark 2).  The target file pins four refutations of its own, and all
    four are CONVERSION failures (`cannot unify`):
    `data_psh_data_law`, `data_psh_data_whole`, `rt_mul_strict` and
    `exp_mempty_is_Hom_Monoid`, each with a positive control beside it,
    and three of the four additionally with a proved `≈` repair.
    `data_psh_data_whole` is the exception and the asymmetry is not an
    oversight: no setoid on `HomGroupData` exists anywhere in the tree,
    so an `≈` statement about the whole record is not even formable, and
    its control is therefore the bare `data_psh_data_whole_control`.
    (An earlier revision of this sentence claimed a control OR a repair
    for each and was wrong about that one on both counts -- it had
    neither, `data_psh_data_law_control` being a control for the LAW
    FIELD rather than for the record.)

    This file supplies the OTHER kind, which a
    library file cannot state: FORMABILITY.  Stating it needs a section
    declaring universe levels strictly apart, and a library file cannot
    carry such a `Constraint` without constraining itself.

    THREE NEGATIVES, ALL FORMABILITY, plus a POSITIVE MEASUREMENT.

      * Negatives 1-3 attribute the hom = proof identification that every
        constant of the target carries in its BINDER.  Three subjects are
        rejected INDEPENDENTLY under `Constraint uh < up` -- the two
        ambient donors `Cartesian` and `Terminal`, and the target's OWN
        central record `HomGroupData` -- while a control naming a hom of
        such a category at those very levels is accepted.  Testing all
        three separately is the point: blaming whichever comes to mind
        first would be wrong.

        `GroupObject` is deliberately NOT among them, and the reason is a
        defect this file was written to avoid.  An earlier revision wrote
        negative 3 as

          Fail Check (fun (C : Category@{uo uh up}) (M : @Monoidal C)
                          (x : C) => @GroupObject C M x).

        and labelled it the `GroupObject` donor.  That is FALSE:
        elaboration never reaches `GroupObject`, because `@Monoidal C` in
        the binder is rejected first -- the error lands at character 52 of
        that line, which is the `C` argument of `Monoidal`.  (`GroupObject`
        in fact takes a `CartesianMonoidal`, not a `Monoidal`, so the line
        was doubly wrong.)  A class whose binder is already identified by
        an earlier argument cannot be tested apart from that argument;
        whether `GroupObject` contributes an identification OF ITS OWN is
        UNKNOWN, not refuted.  This is the same trap the sibling probe for
        issue #340 records for `MonoidObject` under `Monoidal`.

      * The POSITIVE is `HomGroupData`, and it is a sharper instance of
        the rule the index states elsewhere than the target file's own
        siblings: A UNIVERSE IDENTIFICATION CAN HIDE ENTIRELY IN THE
        BINDER.  `HomGroupData@{u u0}`'s constraint block is LITERALLY
        EMPTY -- `(* u u0 |= *)` -- yet its binder reads
        `forall {C : Category@{u u0 u0}}`, identifying hom with proof by
        reusing the level variable.  A reader who checks only the block
        concludes "no identification" and is wrong.  `About` it and read
        BOTH.

    Measured, not assumed: each negative below was stripped of its `Fail`
    once and its error read in full; all three are genuine universe
    inconsistencies naming the declared levels, with zero `cannot unify`.
    The file is rename-simulated with the `Require` lines PRESERVED, since
    two of the guarded names also name modules and renaming those lines
    would break the copy on a missing module rather than on the guard --
    reading as a pass. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Group.Representable.

Generalizable All Variables.

(** ** Negatives 1-3 (FORMABILITY): three donors identify hom with proof *)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category is perfectly formable here. *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(* Controls: each guarded donor exists at UNCONSTRAINED levels.  Without
   these, a rename of any of them would leave its negative succeeding on a
   reference-not-found error rather than on the universe boundary. *)
Check @Cartesian.
Check @Terminal.
Check @GroupObject.
Check @HomGroupData.

(* NEGATIVE 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(* NEGATIVE 3.  [HomGroupData] is the target's OWN central record, and
   unlike [GroupObject] it takes no monoidal argument -- its signature is
   [forall {C : Category}, obj[C] -> Type] -- so the rejection is
   attributable to it rather than to something elaborated before it. *)
Fail Check (fun (C : Category@{uo uh up}) (e : C) => @HomGroupData C e).

End Donors.

(** ** The positive measurement: an identification hiding in the BINDER

    Not a refutation -- a definition whose universe signature IS the
    measurement.  `About HomGroupData` prints an EMPTY constraint block
    over a binder that identifies hom with proof. *)

Definition probe_homgroupdata_binder
  `{C : Category} (e : C) : Type := HomGroupData e.

(* About probe_homgroupdata_binder.
   About HomGroupData.
     HomGroupData@{u u0} :
       forall {C : Category@{u u0 u0}}, obj -> Type@{max(u,u0)}
     (* u u0 |=  *)                      <-- EMPTY block
                    ^^^^^^^^^^^^^^^^^^   <-- hom = proof in the BINDER *)

(** ** What this file does NOT claim

    The identification is the DONORS' doing and is NOT claimed
    unavoidable; no lift was attempted.  Negative 3 DOES show
    [HomGroupData] rejected on its own, with no donor elaborated before
    it, so the rejection is attributable to that record; what is NOT
    established is whether it would still identify were [Category] itself
    stated with its levels apart.  And no separation is proved between the
    representable and the internal formulations. *)
