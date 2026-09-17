(** * Probe: the measured boundaries of the two algebraic limit files
      Instance/Ab/Limit.v and Instance/Rng/Limit.v (issue #443)

    Sibling of Test/ProbeGrpLimit411.v, which pins the same ground for
    Instance/Grp/Limit.v — the group template both targets transpose.  Two
    things make a probe worth writing for the transpositions rather than
    letting the group one stand for all three.

    FIRST, THE HEADLINE SENTENCE IS "THE LIFTED STRUCTURE IS THE POINTWISE
    ONE", and at [Ab] and [Rng] that sentence has three and five operations
    in it against the group's three.  Both targets ship the positive halves
    as [Example]s of their own, so those guard themselves; what they cannot
    guard from inside is that the positive halves are SHARP.  Sections A and
    B restate each readback beside the obvious wrong statement — arguments
    swapped, one operation written where another belongs, negation written
    as the identity — so that the [eq_refl]s are known to be saying
    something.  The two swap refutations are the interesting pair: [Ab]'s
    addition IS commutative and [Rng]'s multiplication need not be, yet
    BOTH swaps are refused, which locates the readbacks at conversion and
    not at [≈].

    SECOND, [Ab] now carries TWO DISTINCT TERMS of type
    [ContinuousFunctor Ab_Forget] — Instance/Ab/FreeNotContinuous.v's
    [Ab_Forget_Continuous], which is RAPL applied to the free/forgetful
    adjunction, and the new [Ab_Forget_creates_continuous], which comes from
    limit creation.  Since they share a type, the sharp question is whether
    they share a TERM, and section F answers it: they do not (N15), the
    apex-only corollary descends from the creation one and not from the
    RAPL one (N16), and each is read back to the constant it is built from
    at [eq_refl].  That is what makes the new one worth declaring, and it is
    the whole reason the [Ab] file exists.

    KINDS, read off the messages actually produced rather than guessed, by
    the convention Test/ProbeGrpLimit411.v states in terms: a TYPE negative
    is a has-type mismatch with NO [cannot unify] clause, and a CONVERSION
    negative is the same mismatch CARRYING one.  Measured that way the
    twenty-five split NAME-ABSENCE (I1, N17, N18, N21) four, TYPE (I2, I3,
    N8) three, CONVERSION (N1–N7, N9–N16, N19, N20, N22) eighteen.  None of
    the twenty-five mentions a universe.

    ONE LABEL DISAGREES WITH A SIBLING PROBE, AND AN EARLIER REVISION OF
    THIS PARAGRAPH EXPLAINED THE DISAGREEMENT WRONGLY.
    Test/ProbeGrpFreeAFT442.v labels its N6 and N7 — the [Grp] forms of N11
    and N12 below — TYPE; stripped here, the [Ab] and [Rng] forms carry a
    [cannot unify] clause, so by 411's convention they are CONVERSION, and
    they are labelled so below.  That revision said "the commands differ
    from 442's only in the category".  They do not: 442's N6
    (Test/ProbeGrpFreeAFT442.v) passes FOUR arguments, including its
    solution set, while N11 and N12 below pass THREE and stop at the third.
    And the [cannot unify] clause is import-sensitive in any case (see
    section E), so its presence or absence is not a fact about the
    categories.  What is common to all of them, and is the whole content of
    the refutation, is the STABLE head: [ContinuousFunctor] does not ascribe
    where [PreservesImageLimit] is expected.

    Each was stripped ONE AT A TIME in a copy of this WHOLE file — not a
    preamble-plus-command scratch, which would drop the [Section]s'
    [Context] and the two locally built oracles and refuse for a reason
    unrelated to the claim — compiled alone, and its whole error read.  All
    twenty-five are refused, and each error lands inside the span of the
    command that was stripped.

    Every constant a refutation names also appears outside every refutation
    — section I is the guard block, and several appear in a control as well
    — so a rename breaks this file loudly instead of turning a refutation
    vacuously green.  Measured mechanically: 77 identifiers occur inside a
    refutation and 57 also occur outside every one, the twenty exceptions
    being exhaustively the keyword itself, the fifteen names a refutation
    DECLARES (which never enter the environment) and the four that are
    meant to be ABSENT — [p443_absent_name], [Ab_Forget_continuous],
    [Rng_Forget_Continuous] and [CMon_Complete].  Rename-simulated 6/6 over
    the load-bearing constants — [Ab_Complete],
    [Ab_Forget_creates_continuous], [Ab_Forget_reflects_limits],
    [Ab_Forget_Continuous], [Rng_Forget_continuous] and
    [Rng_Forget_creates_limits] — each rename breaking this file at a
    POSITIVE site and never inside a refutation, which is the property that
    matters.  Five break at a [Check] or an [Example]; the sixth,
    [Rng_Forget_creates_limits], breaks inside the [Definition]
    [Rng_ConeSet_Complete] (measured, not assumed — an earlier revision of
    this sentence said all six land at a [Check] or an [Example]).

    The import list is the union of the two targets' lists IN FULL, plus
    the two targets, plus five files the refutations and their controls
    need — Adjunction/GAFT.v and Construction/Comma/Creation.v for section
    E, and Adjunction/Continuity.v, Instance/Ab/Free.v and
    Instance/Ab/FreeNotContinuous.v for section F's second term — and one
    that nothing needs in order to typecheck, Theory/Adjunction.v:
    measured, this file compiles without it, and it is kept only so that
    section E's controls print [F ⊣ Ab_Forget] rather than
    [Adjunction.Adjunction F Ab_Forget].  Dropping Instance/Ab/Free.v, by
    contrast, was measured to leave [free_ab_adjunction] with no binding at
    section F's second readback.

    WHAT THIS PROBE DOES NOT PIN.  No universe boundary: unlike
    Test/ProbeGrpLimit411.v's N1 and N2, nothing here binds a shape below
    [Sets]' carrier universe, because that boundary belongs to
    [IsALimit] and to the generic [Sets] section, which both targets
    duplicate character-for-character from the group file and which 411
    already pins.  Nothing here measures the duplication itself.  No
    colimit, no cocompleteness, no monadicity, no comparison with
    Instance/Rng/Zp.v's [Zp_limit] — all four are on the targets' own
    NOT-DELIVERED lists and none acquires a probe here.  And no GAFT
    APPLICATION is built at either category: section E pins only that the
    hypothesis a consumer would reach for does not ascribe, which is the
    correction the [Ab] header already carries in prose. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Ab.FreeNotContinuous.

Generalizable All Variables.

(** ** Instruments *)

(* I1 NAME-ABSENCE: the refutation keyword is live.  If the harness were
   reporting refusals as successes, or the reverse, this line would say
   so. *)

Fail Check p443_absent_name.

(* I2 TYPE: elaboration is really happening.  This is the deliberately
   ill-typed variant of [ab_complete_leg], which DOES hold (the control
   sits beside it in section A): the leg of the created cone is a
   homomorphism of abelian groups, so comparing it with a map of setoids
   is a type error and not a conversion one.  [cmon_map] in the control is
   load-bearing. *)

Fail Example p443_i2 {J : Category} (K : J ⟶ Ab) (d : J) :
  cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

(* I3 TYPE: the same instrument on the other target, at the carrier rather
   than at a leg.  [rng_complete_carrier] holds with [rig_setoid] applied;
   without it the two sides are a ring and a setoid. *)

Fail Example p443_i3 {J : Category} (K : J ⟶ Rng) :
  vertex_obj[Rng_Complete J K] = Sets_limit_obj (Rng_Forget ◯ K) := eq_refl.

(** ** A: at [Ab] the lifted structure is the pointwise one, and sharply

    Positive readbacks at an ARBITRARY shape and an ARBITRARY diagram, each
    beside the wrong statement it excludes.  The positives restate the
    target's own [ab_complete_*] [Example]s so that each refutation has its
    discriminating partner in view. *)

Section AbPointwise.

Context {J : Category}.
Context (K : J ⟶ Ab).

(* control: the carrier *)
Example p443_ab_carrier :
  cmon_setoid (ab_cmon (vertex_obj[Ab_Complete J K]))
    = Sets_limit_obj (Ab_Forget ◯ K) := eq_refl.

(* control: the leg, with the coercion I2 removes *)
Example p443_ab_leg (d : J) :
  cmon_map (cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d)
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

(* control: the addition *)
Example p443_ab_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 a d) (`1 b d) := eq_refl.

(* N1 CONVERSION: ...and the arguments are in that order on the nose.  The
   swapped statement is TRUE up to [≈] — [cmon_plus_comm] is a field of
   [CMonObject] and the target proves [alim_comm] for the lifted structure
   — so what this refutation locates is the LEVEL of the readback: the
   positive above holds by conversion, and commutativity does not. *)

Fail Example p443_n1
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 b d) (`1 a d) := eq_refl.

(* control: the zero *)
Example p443_ab_zero (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d = cmon_zero (K d) := eq_refl.

(* N3 CONVERSION: the created zero is the coordinatewise zero and not its
   negation.  [ab_neg (K d) (cmon_zero (K d)) ≈ cmon_zero (K d)] is an
   ordinary consequence of [ab_neg_left]; it is not a conversion, so one
   operation cannot be read back as another even where they agree. *)

Fail Example p443_n3 (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d
    = ab_neg (K d) (cmon_zero (K d)) := eq_refl.

(* control: the negation *)
Example p443_ab_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d
    = ab_neg (K d) (`1 a d) := eq_refl.

(* N2 CONVERSION: the negation is a real operation and not the identity map
   on the apex.  At an arbitrary diagram neither side reduces to the other,
   so the readback above is saying something about which operation was
   lifted and not merely that some map was. *)

Fail Example p443_n2
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d = `1 a d := eq_refl.

End AbPointwise.

(** ** B: at [Rng] the same, over five operations *)

Section RngPointwise.

Context {J : Category}.
Context (K : J ⟶ Rng).

(* control: the carrier, with the coercion I3 removes *)
Example p443_rng_carrier :
  rig_setoid (vertex_obj[Rng_Complete J K]) = Sets_limit_obj (Rng_Forget ◯ K)
  := eq_refl.

(* control: the leg *)
Example p443_rng_leg (d : J) :
  rig_map (cone_leg (@limit_cone _ _ _ (Rng_Complete J K)) d)
    = Sets_limit_leg (Rng_Forget ◯ K) d := eq_refl.

(* control: the addition *)
Example p443_rng_add
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_add (K d) (`1 a d) (`1 b d) := eq_refl.

(* control: the multiplication *)
Example p443_rng_mul
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

(* N4 CONVERSION: the two binary operations are lifted SEPARATELY, through
   two cones with the same apex [rlim_pair], and neither readback is the
   other's.  A single mediator reused for both would make this accepted. *)

Fail Example p443_n4
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_add (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 a d) (`1 b d) := eq_refl.

(* N6 CONVERSION: multiplication keeps its argument order.  The contrast
   with N1 is the point: [Ab]'s addition commutes up to [≈] and [Rng]'s
   multiplication need not commute at all, and BOTH swaps are refused
   alike, so the refusal is about conversion and carries no algebra. *)

Fail Example p443_n6
  (a b : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (rig_mul (vertex_obj[Rng_Complete J K]) a b) d
    = rig_mul (K d) (`1 b d) (`1 a d) := eq_refl.

(* control: the additive unit *)
Example p443_rng_zero (d : J) :
  `1 (rig_zero (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

(* control: the multiplicative unit *)
Example p443_rng_one (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_one (K d) := eq_refl.

(* N5 CONVERSION: the two units are lifted through two DIFFERENT cones out
   of the same apex [unit_setoid_object], and neither reduces to the other
   at an arbitrary diagram of rings.  One and zero coincide in a zero ring,
   but that is an [≈] and never a conversion, which is exactly what this
   refutation records. *)

Fail Example p443_n5 (d : J) :
  `1 (rig_one (vertex_obj[Rng_Complete J K])) d = rig_zero (K d) := eq_refl.

(* control: the negation *)
Example p443_rng_neg
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d
    = ring_neg (K d) (`1 a d) := eq_refl.

(* N7 CONVERSION: and it is not the identity either.  [ring_neg] is the one
   operation whose coherence the target discharges by [RigHom_neg] rather
   than by a projection, since [RigHom] has no negation clause, so its
   readback is the one most worth keeping honest. *)

Fail Example p443_n7
  (a : carrier (Sets_limit_obj (Rng_Forget ◯ K))) (d : J) :
  `1 (ring_neg (vertex_obj[Rng_Complete J K]) a) d = `1 a d := eq_refl.

End RngPointwise.

(** ** C: strictness — the created cone lies over the given one on the nose

    Both targets record this inside their lifting sections, as
    [alim_over_obj] and [rlim_over_obj].  What is read back here is the
    packaged form a consumer meets: the [slift_eq] field of the
    [StrictLift] the class hands out IS [eq_refl], which is strictly more
    than "the two objects are equal" — it says the recorded proof is the
    trivial one, so [hom_rew] in the [slift_legs] clause transports along
    nothing. *)

Example p443_ab_strict {J : Category} (K : J ⟶ Ab)
  (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N) :
  slift_eq (@screates _ _ _ _ _ (Ab_Forget_StrictlyCreatesLimit K) N HN)
    = eq_refl := eq_refl.

Example p443_rng_strict {J : Category} (K : J ⟶ Rng)
  (N : Cone (Rng_Forget ◯ K)) (HN : IsLimitCone N) :
  slift_eq (@screates _ _ _ _ _ (Rng_Forget_StrictlyCreatesLimit K) N HN)
    = eq_refl := eq_refl.

(* control: what the lift IS — a cone of abelian groups *)
Check (fun (J : Category) (K : J ⟶ Ab) N HN =>
         (slift_cone (@screates _ _ _ _ _ (Ab_Forget_StrictlyCreatesLimit K)
                        N HN) : Cone K)).

(* N8 TYPE: "on the nose" is an equation between IMAGES, and does not
   identify the two cones.  Reading the lifted cone as though it WERE the
   given one is a type error — [Cone K] against [Cone (Ab_Forget ◯ K)],
   with no [cannot unify] clause — which is what keeps strictness a
   statement about [Ab_Forget] rather than a collapse of the two
   categories. *)

Fail Check (fun (J : Category) (K : J ⟶ Ab) N HN =>
              (slift_cone (@screates _ _ _ _ _
                             (Ab_Forget_StrictlyCreatesLimit K) N HN)
                 : Cone (Ab_Forget ◯ K))).

(** ** D: the readbacks are about the limits [Sets_Complete] chooses

    Test/ProbeGrpLimit411.v's N4 at two more categories.  The created
    object depends DEFINITIONALLY on which limit oracle the creation
    theorem is fed; over Mac Lane's cone-set oracle the carrier is
    [cone_apex] and not [Sets_limit_obj], though the two are canonically
    isomorphic.  Built here and not in the library files: each is a second
    [Complete] for its category and must not become the one a consumer
    sees. *)

Definition Ab_ConeSet_Complete : @Complete Ab :=
  creates_limits_Complete Ab_Forget ConeSet_Complete Ab_Forget_creates_limits.

Definition Rng_ConeSet_Complete : @Complete Rng :=
  creates_limits_Complete Rng_Forget ConeSet_Complete Rng_Forget_creates_limits.

Section Oracle.

Context {J : Category}.
Context (KA : J ⟶ Ab).
Context (KR : J ⟶ Rng).

(* control: over the cone-set oracle the carrier IS [cone_apex] *)
Example p443_ab_coneset :
  cmon_setoid (ab_cmon (vertex_obj[Ab_ConeSet_Complete J KA]))
    = cone_apex (Ab_Forget ◯ KA) := eq_refl.

(* N9 CONVERSION *)
Fail Example p443_n9 :
  cmon_setoid (ab_cmon (vertex_obj[Ab_ConeSet_Complete J KA]))
    = Sets_limit_obj (Ab_Forget ◯ KA) := eq_refl.

(* control *)
Example p443_rng_coneset :
  rig_setoid (vertex_obj[Rng_ConeSet_Complete J KR])
    = cone_apex (Rng_Forget ◯ KR) := eq_refl.

(* N10 CONVERSION *)
Fail Example p443_n10 :
  rig_setoid (vertex_obj[Rng_ConeSet_Complete J KR])
    = Sets_limit_obj (Rng_Forget ◯ KR) := eq_refl.

End Oracle.

(** ** E: which preservation hypothesis Freyd's theorem asks for

    Test/ProbeGrpFreeAFT442.v pins this as its N6 and N7 at [Grp]; the two
    targets make it apply at two more categories, and the [Ab] header
    records the refusal in prose as a correction to an earlier revision of
    itself.  [GAFT]'s THIRD argument is the cone-level
    [PreservesImageLimit], which takes a [Limit K] and then a cone over the
    image; neither [ContinuousFunctor], which takes a [Cone K] and then a
    proof that it is limiting, nor the apex-only [PreservesAllLimits]
    ascribes to it, so
    [Continuous_PreservesImageLimit] stands in the term.  NO GAFT
    application is built at either category — the controls stop at the
    partial application, which is exactly what the targets make
    available.

    THE PARENTHETICAL OF THIS REFUSAL IS IMPORT-SENSITIVE, AND AN EARLIER
    REVISION OF THIS COMMENT GOT THAT WRONG.  That revision recorded, as a
    measured CORRECTION to Instance/Ab/Limit.v, that the header's
    closing clause [cannot unify «Limit.Limit K» and «Cone.Cone K»] "does
    not reproduce" and should read
    [cannot unify «Cone (Ab_Forget ◯ K)» and «IsLimitCone N»].  That was
    wrong, and acting on it would have damaged correct prose.  BOTH texts
    are real; which one Coq prints depends on what is imported, because the
    parenthetical is rendered with the module short-names in scope.
    Measured, same command, varying one [Require Import]:

      base (+ Structure.Limit.Preservation)
                            cannot unify «Limit.Limit K» and «Cone.Cone K»
      + Structure.Limit     cannot unify «Cone.Cone (Ab_Forget ◯ K)»
                                     and «IsLimitCone N»
      + Structure.Cone      cannot unify «Limit.Limit K» and «Cone K»
      + Structure.Limit.Creation
                            cannot unify «Limit.Limit K» and «Cone.Cone K»

    The HEAD of the error is stable under all four and is what actually
    matters: [ContinuousFunctor] does not ascribe where
    [PreservesImageLimit] is expected.  Instance/Ab/Limit.v's quote is
    correct for its own environment; this file's strip produces a different
    parenthetical because this file imports more.  N11 and N12 below pin the
    refusal, not the wording. *)

(* controls: the bridged hypothesis is accepted at both *)
Check (GAFT Ab_Forget Ab_Complete
            (Continuous_PreservesImageLimit Ab_Forget_creates_continuous)).
Check (GAFT Rng_Forget Rng_Complete
            (Continuous_PreservesImageLimit Rng_Forget_continuous)).

(* N11 CONVERSION: measured, the pair the message reports is the two
   hypotheses' FOURTH binders — [PreservesImageLimit] asks next for a cone
   over the image where [ContinuousFunctor] asks for a proof that the cone
   it was already given is limiting. *)
Fail Check (GAFT Ab_Forget Ab_Complete Ab_Forget_creates_continuous).

(* N12 CONVERSION: nor the apex-only class, which the [Ab] target also
   supplies and which is the tempting wrong choice.  Its message prints
   [PreservesImageLimit]'s body in full, so the two are visibly different
   statements and not two spellings of one. *)
Fail Check (GAFT Ab_Forget Ab_Complete Ab_Forget_PreservesAllLimits).

(* N13 CONVERSION *)
Fail Check (GAFT Rng_Forget Rng_Complete Rng_Forget_continuous).

(* N14 CONVERSION *)
Fail Check (GAFT Rng_Forget Rng_Complete Rng_Forget_PreservesAllLimits).

(** ** F: two terms of type [ContinuousFunctor Ab_Forget], and they differ

    The reason the [Ab] file exists.  Instance/Ab/FreeNotContinuous.v
    already declares [Ab_Forget_Continuous] and proves it by RAPL
    applied to Instance/Ab/Free.v's [free_ab_adjunction]; the new
    [Ab_Forget_creates_continuous] comes from limit creation and
    presupposes only [Sets_Complete].  Both are read back to the constant
    they are built from, so the provenance claim is machine-checked and not
    asserted, and N15 settles the sharp question their shared type
    raises. *)

(* controls: the same type, twice *)
Check (Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget).
Check (Ab_Forget_Continuous : ContinuousFunctor Ab_Forget).

(* control: the new one IS creation applied, on the nose *)
Example p443_creates_continuous_term :
  Ab_Forget_creates_continuous
    = creates_limits_continuous Ab_Forget Sets_Complete Ab_Forget_creates_limits
  := eq_refl.

(* control: the old one IS RAPL applied, on the nose *)
Example p443_rapl_continuous_term :
  Ab_Forget_Continuous = right_adjoint_Continuous free_ab_adjunction
  := eq_refl.

(* N15 CONVERSION: so they are not the same term.  This is what makes the
   second declaration worth having: feeding Freyd's theorem a continuity
   witness built out of the very adjunction the theorem is asked to produce
   would establish nothing, and the two constants are now known to be
   distinct rather than assumed to be. *)

Fail Example p443_n15 :
  Ab_Forget_creates_continuous = Ab_Forget_Continuous := eq_refl.

(* control: the apex-only corollary descends from the CREATION one *)
Example p443_ab_apex_descends :
  Ab_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Ab_Forget_creates_continuous := eq_refl.

(* N16 CONVERSION: and not from the RAPL one, which would have been
   available and is not what the target used. *)

Fail Example p443_n16 :
  Ab_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Ab_Forget_Continuous := eq_refl.

(* control: at [Rng] there is only one, and it descends the same way *)
Example p443_rng_apex_descends :
  Rng_Forget_PreservesAllLimits
    = Continuous_PreservesAllLimits Rng_Forget_continuous := eq_refl.

(* N17 NAME-ABSENCE: the two files' naming IS asymmetric, and a consumer
   reaching for the [Rng]-style name at [Ab] gets nothing.  An earlier
   revision of this comment gave a FALSE reason — that the name "could NOT
   be given" because [Ab_Forget_Continuous] was already taken.  Coq
   identifiers are case-sensitive, so [Ab_Forget_continuous] and
   [Ab_Forget_Continuous] would coexist perfectly well; the audit of this
   probe checked that by defining the former in an environment already
   holding the latter (rc=0).  The real reason is a CHOICE, made in
   Instance/Ab/Limit.v and stated in its header: two constants of the same
   type [ContinuousFunctor Ab_Forget], differing only in case, would be a
   trap, because one is RAPL applied to the free/forgetful adjunction and
   the other is derived from limit creation, and only the second is usable
   as a GAFT hypothesis without circularity.  So the new one is
   [Ab_Forget_creates_continuous], whose name says where it comes from.
   This refutation pins that the tempting name is absent. *)

Fail Check Ab_Forget_continuous.

(* N18 NAME-ABSENCE: the mirror.  There is no RAPL-style continuity
   constant at [Rng], and the [Rng] header's reason is measured there: no
   adjunction in tree has [Rng_Forget] as its right adjoint, so
   [right_adjoint_Continuous] does not reach it. *)

Fail Check Rng_Forget_Continuous.

(** ** G: reflection is not preservation, and the two creation classes are
        two types *)

(* control: what the target delivers *)
Check (fun (J : Category) (K : J ⟶ Ab) =>
         (Ab_Forget_reflects_limits K : ReflectsLimitCone K Ab_Forget)).

(* N22 CONVERSION: [ReflectsLimitCone] and [PreservesLimitCone] are converse
   implications between the same two propositions, so neither ascribes as
   the other.  This is the clause the [Ab] header says RAPL does not give
   at all, and it is a separate hypothesis from every continuity constant
   in section F. *)

Fail Check (fun (J : Category) (K : J ⟶ Ab) =>
              (Ab_Forget_reflects_limits K : PreservesLimitCone K Ab_Forget)).

(* controls: each target ships an inhabitant of both creation classes *)
Check (Ab_Forget_creates_limits : CreatesAllLimits Ab_Forget).
Check (Ab_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Ab_Forget).
Check (Rng_Forget_creates_limits : CreatesAllLimits Rng_Forget).
Check (Rng_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Rng_Forget).

(* N19, N20 CONVERSION: neither is an ascription of the other — 411's N3 at
   the two new categories, and its message here too carries the [cannot
   unify] clause that 411 uses to tell the two kinds apart. *)

Fail Definition p443_n19 : StrictlyCreatesLimits Ab_Forget :=
  Ab_Forget_creates_limits.

Fail Definition p443_n20 : StrictlyCreatesLimits Rng_Forget :=
  Rng_Forget_creates_limits.

(** ** H: one NOT-DELIVERED claim, pinned

    The [Ab] header says in terms that no [CMon] analogue is extracted,
    "No [CMon_Complete] exists either", though the engine transfers
    unchanged once [ab_neg] and its two laws are dropped.  Measured on the
    worktree this probe was written against, a whole-tree word-bounded grep
    of every [.v] file for that token returns exactly one hit,
    Instance/Ab/Limit.v, and that hit is the sentence itself; the
    refutation below is the same absence taken from the environment rather
    than from the text. *)

(* N21 NAME-ABSENCE *)
Fail Check CMon_Complete.

(** ** I: guard block — every constant a refutation names, named outside
        every refutation *)

Check @carrier.
Check @Cone.
Check @cone_leg.
Check @cone_apex.
Check @limit_cone.
Check @IsLimitCone.
Check @vertex_obj.
Check @Sets_limit_obj.
Check @Sets_limit_leg.
Check @Sets_Complete.
Check @ConeSet_Complete.
Check @screates.
Check @slift_eq.
Check @slift_cone.
Check @CreatesAllLimits.
Check @StrictlyCreatesLimits.
Check @ReflectsLimitCone.
Check @PreservesLimitCone.
Check @ContinuousFunctor.
Check @Continuous_PreservesAllLimits.
Check @Continuous_PreservesImageLimit.
Check @creates_limits_Complete.
Check @creates_limits_continuous.
Check @right_adjoint_Continuous.
Check @GAFT.

Check @Ab.
Check @Ab_Forget.
Check @ab_cmon.
Check @ab_neg.
Check @cmon_setoid.
Check @cmon_map.
Check @cmon_plus.
Check @cmon_zero.
Check @Ab_Complete.
Check @Ab_ConeSet_Complete.
Check @Ab_Forget_StrictlyCreatesLimit.
Check @Ab_Forget_StrictlyCreatesLimits.
Check @Ab_Forget_creates_limits.
Check @Ab_Forget_creates_continuous.
Check @Ab_Forget_PreservesAllLimits.
Check @Ab_Forget_reflects_limits.
Check @Ab_Forget_Continuous.
Check @free_ab_adjunction.

Check @Rng.
Check @Rng_Forget.
Check @rig_setoid.
Check @rig_map.
Check @rig_add.
Check @rig_mul.
Check @rig_zero.
Check @rig_one.
Check @ring_neg.
Check @Rng_Complete.
Check @Rng_ConeSet_Complete.
Check @Rng_Forget_StrictlyCreatesLimit.
Check @Rng_Forget_StrictlyCreatesLimits.
Check @Rng_Forget_creates_limits.
Check @Rng_Forget_continuous.
Check @Rng_Forget_PreservesAllLimits.
Check @Rng_Forget_reflects_limits.
