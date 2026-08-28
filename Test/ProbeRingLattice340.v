(** * Boundary probes for Structure/Ring.v and Structure/Lattice.v (#340)

    Mac Lane CWM 2nd ed. §III.6, book p. 75.

    The two targets already ship FOUR refutations of their own, and all
    four are CONVERSION (`Structure/Ring.v:585`, `:602`,
    `Structure/Lattice.v:518`, `:536` -- the Sets round trips, whole record
    and internal `Monoid` record respectively; each was stripped and each
    gives exactly one `cannot unify`, zero universe and zero typing
    errors).  This file pins what they CANNOT state: the universe
    boundary, which needs a section declaring levels strictly apart.

    CORRECTION, added later: this file originally continued "...which a
    library file cannot carry without constraining itself."  THAT IS
    FALSE.  `Instance/Fun/Group.v` (issue #342) carries exactly such
    probes in-file, as `Universes`/`Constraint` inside a `Section` with
    `Context` variables and `Check` controls; the declarations are
    discharged at `End`, and a downstream consumer that imports the file
    can still declare its own levels strictly apart.  Measured, not
    assumed.  So a separate Test file is a CHOICE here, not a necessity,
    and the in-file form is arguably better since it keeps a refutation
    beside what it refutes.

    THREE NEGATIVES, ALL FORMABILITY, plus a POSITIVE MEASUREMENT.

      * Negatives 1-3 attribute the hom = proof identification that every
        class in both files carries.  THREE donors do it INDEPENDENTLY --
        `Cartesian`, `Terminal` and `Monoidal` -- each rejected under
        `Constraint uh < up` while a control naming a hom at those very
        levels is accepted.  Testing all three separately is the point:
        blaming whichever comes to mind first would be wrong, and the
        classes here take all three.  `MonoidObject` is NOT a fourth
        donor and is not probed as one: its [Monoidal] argument is
        rejected first, so it cannot be tested apart from `Monoidal`,
        and whether it identifies anything of its own is UNKNOWN.

      * The POSITIVE is `dup_left`/`dup_right`, and it is the sharpest
        instance in this tree of a rule the index states elsewhere: A
        UNIVERSE IDENTIFICATION CAN HIDE ENTIRELY IN THE BINDER.
        `dup_left@{u u0}`'s constraint block is LITERALLY EMPTY --
        `(* u u0 |= *)` -- yet its binder reads
        `C : Category@{u u0 u0}`, identifying hom with proof by reusing
        the level variable.  A reader who checks only the block concludes
        "no identification" and is wrong.  Run `About dup_left` to see it.
        Inherited from `Cartesian`, not introduced by either target.

    What the OBJECT universe does is worth as much as what the hom does:
    it stays FREE in all four classes, appearing only in `<=` bounds.

    Every negative is paired with a positive control naming its own
    constants.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others, with `Require` lines
    preserved. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Structure.Ring.
Require Import Category.Structure.Lattice.

Generalizable All Variables.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negatives 1-3 (FORMABILITY): three INDEPENDENT donors identify hom
       with proof

    Each is rejected under `Constraint uh < up` while the control shows a
    hom-set of such a category is perfectly formable at those levels. *)

Section Donors.

Universe uo uh up.
Constraint uh < up.

(* Control: a hom-set of such a category exists. *)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).

(* Controls: all three donors exist at UNCONSTRAINED levels.  Without
   these, a rename of any of them would leave its negative succeeding on a
   reference-not-found error rather than on the universe boundary. *)
Check @Cartesian.
Check @Terminal.
Check @MonoidObject.
Check @Monoidal.

(* NEGATIVE 1. *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 2. *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

(* NEGATIVE 3.  The donor is [Monoidal], NOT [MonoidObject].  An earlier
   revision of this file wrote the negative as

     Fail Check (fun (C : Category@{uo uh up}) (M : @Monoidal C)
                     (x : C) => @MonoidObject C M x).

   and labelled it the [MonoidObject] donor.  That was FALSE: elaboration
   never reaches [MonoidObject], because [@Monoidal C] in the binder is
   rejected first -- the error lands at the [C] argument of [Monoidal].
   [MonoidObject] cannot be probed apart from [Monoidal] at all, its own
   signature being
     [MonoidObject@{u u0} : forall {C : Category@{u u0 u0}},
                            Monoidal@{u u0} -> obj[C] -> Type@{u0}],
   whose [Monoidal] argument pins [C] before any field is consulted.  So
   whether [MonoidObject] contributes an identification OF ITS OWN is
   UNKNOWN -- not refuted, and not measured anywhere in this commit. *)
Fail Check (fun (C : Category@{uo uh up}) => @Monoidal C).

End Donors.

(** ** The positive measurement: an identification hiding in the BINDER

    Not a refutation -- two definitions whose universe signatures ARE the
    measurement.  `About dup_left` prints an EMPTY constraint block over a
    binder that identifies hom with proof. *)

Check @dup_left.
Check @dup_right.

(** ** Positive controls for the headline artifacts *)

Check @InternalSemiring.
Check @InternalRing.
Check @InternalSemilattice.
Check @InternalLattice.

(** The two derivations that are the mathematical content: annihilation is
    a THEOREM for a ring, and idempotence is DERIVED from absorption. *)

Check @ring_annihilate_l.
Check @ring_annihilate_r.
Check @ring_cancel_idem.
Check @InternalRing_InternalSemiring.
Check @InternalRing_GroupObject.
Check @lattice_join_idem.
Check @lattice_meet_idem.
Check @lattice_bot_meet.
Check @lattice_top_join.

(** The Sets passages, both directions, in both files. *)

Check @Sets_InternalSemiring.
Check @Rig_of_InternalSemiring.
Check @Sets_InternalRing.
Check @Ring_of_InternalRing.
Check @Sets_InternalLattice.
Check @SetoidLattice_of_InternalLattice.
Check @SetoidLattice.

(** Independence, proved by refutation rather than asserted: the two
    annihilation fields of a semiring do not follow from the rest, and
    absorption does not follow from the monoid structure. *)

Check @nat_plus_not_distributive.
Check @bool_or_not_annihilating.
Check @bool_join_not_absorbing.
Check @bool_xor_not_idempotent.

(** Computing witnesses. *)

Check @Nat_ISemiring.
Check @Int_IRing.
Check @Bool_Lattice.
Check @Bool_Semilattice.

(** ** MEASURED RENAME-SIMULATION SCORE

    Read off the `Fail` commands themselves, not from memory.

      Negative 1 names [Cartesian], [Category]
      Negative 2 names [Terminal], [Category]
      Negative 3 names [Monoidal], [Category]

    Excluding [Category] as core vocabulary named by almost every file in
    the tree -- the stated ground, rather than any claim that it is hard
    to guard -- the constants a NEGATIVE names are THREE: [Cartesian],
    [Terminal], [Monoidal].

    Each of the three is named by a positive control above -- [Monoidal]
    only after a first run scored 3/4 and showed it named ONLY inside
    Negative 3, so a rename left that `Fail` succeeding on a
    reference-not-found error.  That observation was the tell that
    Negative 3 was testing [Monoidal] rather than [MonoidObject], and it
    was read as an incidental guard gap instead; the negative is now
    written as what it measures.  [MonoidObject] keeps its control above
    even though no negative names it, since the prose discusses it.
    Score: 3/3, on
    an unpadded denominator, measured by compiling a renamed copy of this
    file against an instrument-checked baseline -- with the `Require`
    lines PRESERVED, since three of these four share a name with a module
    and renaming those lines would break the copy on a missing module
    rather than on the guard, reading as a pass. *)
