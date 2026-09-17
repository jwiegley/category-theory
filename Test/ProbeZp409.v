Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.InverseLimit.
Require Import Category.Instance.Rng.Zp.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.
Open Scope category_scope.

(** * Boundary probes for Instance/Rng/Zp.v

    NINE refutation commands = a scope-free instrument check plus EIGHT
    negatives of THREE kinds, told apart by the error TEXT: four
    CONVERSION (negatives 1-4), two TYPING (negatives 5 and 7, whose
    errors carry no universe clause) and two FORMABILITY (negatives 6 and
    8, whose do).  Each is stripped one at a time in a copy of this WHOLE
    file and compiled alone.  Every constant a negative names is also
    named by a [Check] outside every refutation command, so a rename
    breaks this file at a control line rather than turning a guard
    vacuously green. *)

(** ** Instrument: a refutation command must be able to fail *)

Fail Check probe_zp409_no_such_name.

(** ** Guard block: every constant the negatives name, named outside them *)

Check @dsum.
Check @dadd.
Check @d7.
Check @d5.
Check @ResRing.
Check @ZComm.
Check @dpow.
Check @Int_Ring.
Check @zpd.
Check @zp_const.
Check @mraw.
Check @Zp_digits_iso.
Check @Zp.
Check @DigitSeq.
Check @Isomorphism.
Check @Rng.
Check @Sets.
Check @rig_setoid.
Check @carrier.
Check @mraw_1.
Check @RKills.
Check @ResIdeal.
Check @PrincipalIdeal.
(* [ResTower] is named by negative 7 and nowhere else; without this
   line a rename of it would turn that guard vacuously green, which
   the rename simulation caught. *)
Check @ResTower.

(** ** Negative 1 (CONVERSION): the carry is real

    [Zp_digits_add] is an equation in [ResRing n], NOT at Leibniz equality
    of the partial sums: the carry out of position n is exactly the
    difference.  In base ten at n = 1 the digit-string sum of 7 and 5 has
    partial sum 2 while the integers sum to 12; at n = 2, where the carry
    has been absorbed, the two agree. *)

Fail Example probe_carry_leibniz :
  dsum 10%Z (dadd 10%Z d7 d5) 1%nat
    = (dsum 10%Z d7 1%nat + dsum 10%Z d5 1%nat)%Z := eq_refl.

Example probe_carry_control_n1_lhs :
  dsum 10%Z (dadd 10%Z d7 d5) 1%nat = 2%Z := eq_refl.

Example probe_carry_control_n1_rhs :
  (dsum 10%Z d7 1%nat + dsum 10%Z d5 1%nat)%Z = 12%Z := eq_refl.

Example probe_carry_control_n2 :
  dsum 10%Z (dadd 10%Z d7 d5) 2%nat
    = (dsum 10%Z d7 2%nat + dsum 10%Z d5 2%nat)%Z := eq_refl.

(** ** Negative 2 (CONVERSION): the residue relation is coarser than [=]

    The quotient keeps the carrier of the base ring and coarsens only the
    setoid, so a residue equation is NOT an equation of integers. *)

Fail Example probe_residue_leibniz :
  (2%Z : carrier (rig_setoid (ResRing ZComm 2%Z 1%nat))) = 0%Z := eq_refl.

(* AN EARLIER REVISION of this control read [existT _ 1%Z eq_refl].  Since
   the PR "algebraic carriers are sets" (2026-09-17) a quotient ring's
   equality is the propositional TRUNCATION of ideal membership
   (Instance/Rng/Quotient.v's [rquot_rel]), so the witness is wrapped in
   [inhabits].  The negative above is unaffected -- what it pins is that the
   residue relation is coarser than [=], which is still true, and still for
   the same reason. *)
Example probe_residue_control :
  @equiv _ (rig_setoid (ResRing ZComm 2%Z 1%nat)) 2%Z 0%Z
  := inhabits (existT _ 1%Z eq_refl).

(** ** Negative 3 (CONVERSION): the normalisation in [zpd] is load-bearing

    Dividing the representative directly, without first reducing it modulo
    d^(n+1), gives the wrong digit at a negative representative: the
    units digit of −1 in base ten is 9, not −1. *)

Fail Example probe_zpd_without_mod :
  ((-1)%Z / (@dpow Int_Ring 10%Z 0%nat))%Z = 9%Z := eq_refl.

Example probe_zpd_without_mod_value :
  ((-1)%Z / (@dpow Int_Ring 10%Z 0%nat))%Z = (-1)%Z := eq_refl.

Example probe_zpd_control :
  zpd 10%Z (zp_const 10%Z (-1)%Z) 0%nat = 9%Z := eq_refl.

(** ** Negative 4 (CONVERSION): [mraw] is the convolution, not the
       pointwise product *)

Fail Example probe_mraw_pointwise (a b : nat -> Z) :
  mraw a b 1%nat = (a 1%nat * b 1%nat)%Z := eq_refl.

(** ** Negative 5 (TYPING): the bijection is in [Sets], not in [Rng]

    No ring structure is put on digit strings, so [DigitSeq p] is an
    object of [Sets] and not of [Rng]; the correspondence of the
    operations is [Zp_digits_add] and [Zp_digits_mul] instead. *)

Fail Check (fun (p : Z) (Hp : (1 < p)%Z) =>
  (Zp_digits_iso p Hp : @Isomorphism Rng (Zp ZComm p) (DigitSeq p))).

Check (fun (p : Z) (Hp : (1 < p)%Z) =>
  (Zp_digits_iso p Hp
     : @Isomorphism Sets (rig_setoid (Zp ZComm p)) (DigitSeq p))).

(** ** Negatives 6-7: where the ring's three universes are identified

    Sections (A)-(B) do NOT identify the ambient ring's carrier, relation
    and proof universes: [PrincipalIdeal], [ResIdeal] and [ResRing] are
    all formable at a ring whose three levels are declared strictly apart.
    Everything from [res_kills] on -- the first constant to mention
    [Rng] -- carries the identification.  THE DONOR IS [Rng] ITSELF, NOT
    [RKills], and a first draft of this comment said otherwise:
    [Instance/Rng.v:102]'s [Rng := Ring] has [obj] at
    [RingObject@{u u u}], so [R : obj[Rng]] alone is refused at these
    levels with the IDENTICAL error and no [RKills] in the command
    (negative 8); and [RKills]'s own type mentions [R ~{Rng}~> K], so it
    cannot be tested apart from that -- negative 6's error fires at its
    [R] ARGUMENT, the already-refused-argument trap.  What the three
    controls below DO discriminate is that sections (A)-(B) are free of
    the identification; they attribute it to nothing.

    Read the two kinds apart: negative 8 is FORMABILITY (its error ends in
    a universe clause, "Cannot enforce rr = ro because ro < rr"), while
    negatives 6 and 7 are TYPING -- elaboration refuses the section's
    [RingObject]/[RingComm] instance where the all-equal one is wanted,
    with no universe clause at all.

    AN EARLIER REVISION of this paragraph assigned the FORMABILITY reading
    to negative 6 and the TYPING reading to negative 7 alone.  Re-measured
    at the PR "algebraic carriers are sets" (2026-09-17), by stripping each
    [Fail] in a copy of this whole file: negative 6 now reports

      The term "R" has type "RingObject@{rp ro rr}" while it is expected
      to have type "RingObject@{u u u}"

    -- one fresh universe repeated three times, printed under whatever name
    the enclosing module gives it -- with no universe clause, so it reads
    as TYPING and not as FORMABILITY;
    negative 7 reports the same shape at [RingComm]; and negative 8 still
    ends in "(universe inconsistency: Cannot enforce rr = ro because
    ro < rr)".  What each negative PINS is unchanged -- the identification
    is still [Rng]'s and still absent from sections (A)-(B) -- only the
    error kinds were misattributed. *)

Section UniverseBoundary.

Universes ro rr rp.
Constraint ro < rr.
Constraint rr < rp.

(* AN EARLIER REVISION wrote [RingObject@{ro rr rp}].  Since the PR
   "algebraic carriers are sets" (2026-09-17) the record's AUXILIARY universe
   moved from the third argument to the first -- the [PropEquiv] field puts
   [Set+1] in the record's sort -- so the three roles permuted from
   (carrier, proof, aux) to (aux, carrier, proof).  Each named universe keeps
   its original role; only the order changed.  The boundary this section pins
   is unmoved: [ro < rr < rp] still declares the three levels strictly
   apart. *)
Context (R : RingObject@{rp ro rr}) (Rc : RingComm R)
        (d : carrier (rig_setoid R)) (n : nat).

(* Controls: accepted at those very levels. *)
Check (PrincipalIdeal Rc d).
Check (ResIdeal Rc d n).
Check (ResRing Rc d n).

Fail Check (@RKills R (ResIdeal Rc d (S n)) (ResRing Rc d n)).

Fail Check (ResTower Rc d).

(* Negative 8 (FORMABILITY): the donor, ISOLATED.  Neither [RKills] nor
   any constant of [Instance/Rng/Zp.v] occurs in this command -- mere
   objecthood in [Rng] is already refused, and this is the one negative of
   the three whose message ends in a universe clause.  An earlier revision
   said "with negative 6's error"; re-measured, negative 6's message is a
   plain instance mismatch and only this one carries "Cannot enforce
   rr = ro because ro < rr". *)
Fail Check (R : obj[Rng]).

End UniverseBoundary.
