(** * Probe for the reflective and coreflective examples (issue #370)

    Pins the measured boundaries of the nine files #370 adds for Mac
    Lane §IV.3, book p. 92 (PDF p. 101), catalog item
    maclane:IV.3:construction1, with the appended Seven Sketches Example
    3.74 (7sketches:3.4.2:example3.74), Riehl's Example 4.6.13, the
    second half of (ii) and (iv) (riehl:4.6:example13), and Riehl's
    Exercise 5.3.ii (riehl:5.3:exii).  The files are Construction/
    Reflective/Coreflective.v (the covariant bridge into the op-typed
    [Coreflective]), Construction/Reflective/Monadic.v (a reflective
    inclusion is monadic), Construction/Reflective/Universal.v (the
    record from universal and from couniversal arrows), Instance/Grp/
    Abelianize/Reflective.v (Ab in Grp), Instance/Ab/Torsion.v (torsion
    groups coreflective in Ab), Instance/Rng/Commutativize.v with its
    satellite Instance/Rng/Commutativize/UT2.v (CRing in Ring),
    Instance/Met/Uniform.v (complete spaces in the metric spaces with
    uniformly continuous maps, and in [Met]) and Instance/Mod/RingEpi.v
    (T-Mod in R-Mod for a ring epimorphism).  N1-N21 and N23 restate
    refusals #370's two builders and its review measured in scratch
    files (LABELS, below); N22 is this file's own.  Every one is
    recorded in a target header.  The positive controls restate the
    files' claims independently.
    CORRECTION (#1347): N8, N10, N12 and N13 now hold at [eq_refl], since
    Instance/Sets.v gives its identity's and composite's properness fields
    as terms; they are controls, and keep their labels.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    Target by target, in the order the nine files are named above, the
    [Require] lines each adds to those before it, in its own order, and
    then that target unless an earlier line required it.  Seventy-four
    lines: the sixty-nine distinct [Require]s of the nine targets, four
    targets among them, and the five targets no target requires.  The
    last two lines of Instance/Mod/RingEpi.v's own list, QArith and Lia,
    come last here as there, and QArith's import shadows [equiv], so the
    statements below write [Setoid.equiv] or [≈].  Under this list the
    file's dependency closure is one hundred and seventy-seven
    [Category] modules (the transitive closure of [coqdep -R . Category]
    over the sixty-two [Category] lines), the nine targets among them.
    A shorter import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of
    an absent name is refused for that reason ("The reference
    p370_absent_name was not found in the current environment."), and
    each of the thirty-eight definitions and examples of this file that
    is not a refutation (eighteen definitions, twenty examples),
    wrapped in the refutation keyword in a copy of this WHOLE file,
    stops the build at that command with the report that the guarded
    command had been accepted (thirty-eight of thirty-eight, by a script
    over the copies).  Every negative other than that instrument is a
    [Definition] or an [Example], never a [Check], so that an open evar
    cannot satisfy it.  Each negative was stripped of its refutation
    keyword in a copy of this WHOLE file, one at a time, compiled, and
    its error read; each of the twenty-three copies stops inside the
    stripped command (by the File line of its error, compared by a
    script with the command's extent).  The kind recorded is the kind of
    that error, and each negative has positive controls beside it.
    Quotations are Rocq 9.1.1's under this file's import list, with the
    error's environment block left out; Rocq prints the "cannot unify"
    parenthetical with the short names in scope.  The nine targets and
    this file also compile on Coq 8.19.2 and 8.20.1, with no warning,
    against the prebuilt trees of this library for those versions, whose
    sources of the one thousand and eighty-six modules they hold are
    this tree's byte for byte (compared by script) but for eight, which
    differ from this tree's only by the CORRECTION (#370) comments that
    issue adds.  Each of the twenty-three stripped copies is refused
    there at the File line and characters of its Rocq 9.1.1 refusal.
    Under 8.20.1 all twenty-three errors are the Rocq 9.1.1 ones up to
    the serial names of universes; under 8.19.2 twenty-two are, and N23
    prints the same type mismatch with no parenthetical (compared by a
    script).
    CORRECTION (#1347): N8, N10, N12 and N13 are controls now.  Each,
    wrapped in the refutation keyword in a copy of this WHOLE file, stops
    the build at that command, so the definitions and examples that are
    not refutations are forty-two (eighteen definitions, twenty-four
    examples).  The negatives are nineteen, and each, stripped in a copy
    of this WHOLE file, stops inside its command with the error it
    printed before #1347 (compared by script, universe serial names
    aside).  Both measurements on Rocq 9.1.1 only; the older versions
    were not re-run.

    KINDS.  Twenty-four refutations, counted as the lines that open with
    the refutation keyword: NAME-ABSENCE (the instrument), TYPING (N1,
    N2, N5, N22), CONVERSION (N3, N4, N6-N21) and UNIVERSE (N23): one,
    four, eighteen and one.  A TYPING refusal is a term whose type is
    not the one expected, with no parenthetical; a CONVERSION refusal is
    [eq_refl] refused with a "cannot unify" parenthetical; the UNIVERSE
    refusal is a type mismatch whose parenthetical is a universe
    inconsistency.
    CORRECTION (#1347): N8, N10, N12 and N13 now hold at [eq_refl] and
    are controls, so the refutations are twenty and CONVERSION counts
    fourteen (N3, N4, N6, N7, N9, N11, N14-N21): one, four, fourteen and
    one.

    LABELS.  builder-alg's scratch negatives n6a, n6b, n7, n8, n1, s1,
    n4, s2, n5, s3, n2, n3, n14 and n13 are N1, N2, N3, N5, N7, N8, N9,
    N10, N11, N12, N16, N17, N18 and N19; its hom-setoid comparison is
    N4; and its controls p1, p4, p5, p7, p7b and the comparison of the
    two [equiv] relations are [p370_abgrp_unit], [p370_torsion_counit],
    [p370_crng_unit], [p370_op_obj], [p370_op_hom] and [p370_op_equiv].
    builder-an's b_unit_strict, g_unit_whole, g_unit_whole_met,
    h_unit_whole, g_counit_pointwise and g_fmap_pointwise are N6, N13,
    N14, N15, N20 and N21.  The review's loc_big is N23, its loc_small
    the control [p370_loc_at_set].  The labels are not constants: each
    refutation carries its own in a comment on the line above it, the
    instrument's reading "The instrument".
    CORRECTION (#1347): N8, N10, N12 and N13 are controls now and keep
    their labels in the comments on the lines above them.

    ** Instance/Grp/Abelianize/Reflective.v: why a new subcategory

    Controls: the inclusion of [AbGrp_Sub] and the record over it
    ([p370_abgrp_incl], [p370_abgrp_record]); Abelianize.v's [Ab_to_Grp]
    factors through [AbGrp_Sub] on objects at [eq_refl]
    ([p370_ab_to_grp_obj]).

    N1 (TYPING).  The header's WHY A NEW SUBCATEGORY, for an arbitrary
    [S : Subcategory Grp], N1:
      The term "Ab_to_Grp" has type "Ab ⟶ Grp" while it is expected to
      have type "Sub Grp S ⟶ Grp".
    N2 (TYPING).  The record from Abelianize.v's adjunction, N2:
      The term "Abelianization_Functor" has type "Grp ⟶ Ab" while it is
      expected to have type "Grp ⟶ Sub Grp S".

    ** Construction/Reflective/Coreflective.v: what the bridge is for

    Controls: the objects, the hom types and the two [equiv] relations of
    [Opposite (Sub C S)] and [Sub (Opposite C) (op_subcategory S)]
    convert ([p370_op_obj], [p370_op_hom], [p370_op_equiv]); a record
    read back covariantly and rebuilt is the record, at [eq_refl]
    ([p370_bridge_roundtrip]); the coreflector read back is a covariant
    functor ([p370_coreflector_covariant]).

    N3, N4 (CONVERSION).  The header's WHY FIELD BY FIELD: the two
    categories, N3, and their hom-setoids, N4:
      (cannot unify "(Sub C S)^op" and "Sub C^op (op_subcategory S)")
      (cannot unify "@homset (Sub C S)^op x y" and "@homset (Sub C^op
      (@op_subcategory C S)) x y")
    N5 (TYPING).  The record's own reflector against the covariant one:
      The term "reflector R" has type "C^op ⟶ Sub C^op (op_subcategory
      S)" while it is expected to have type "C ⟶ Sub C S".

    ** The units: whole records against pointwise readbacks

    Each reflection's unit, and the torsion coreflection's counit, is the
    map the books name when applied to an element, at [eq_refl], and is
    the transposed composite with an identity as a record, at [eq_refl]
    too, but is not the named map as a record.  Controls: the transposed
    composites ([p370_ua_unit], [p370_abgrp_unit], [p370_torsion_counit],
    [p370_crng_unit]) and the pointwise readbacks
    ([p370_abgrp_unit_point], [p370_torsion_counit_point],
    [p370_crng_unit_point], [p370_completionU_unit_point],
    [p370_completion_unit_point], [p370_tmod_unit_point]).

    N6 (CONVERSION).  Universal.v's STRENGTHS, from universal arrows:
      (cannot unify "unit" and "arrow")
    N7, N8 (CONVERSION).  Abelianize/Reflective.v's STRENGTHS, the whole
    record and its setoid-morphism component:
      (cannot unify "abgrp_unit G" and "abel_proj G")
      (cannot unify "grp_map (abgrp_unit G)" and "grp_map (abel_proj G)")
    N9, N10 (CONVERSION).  Torsion.v's STRENGTHS, likewise:
      (cannot unify "torsion_counit A" and "torsion_incl A")
      (cannot unify "cmon_map (torsion_counit A)" and "cmon_map
      (torsion_incl A)")
    N11, N12 (CONVERSION).  Commutativize.v's STRENGTHS, likewise:
      (cannot unify "crng_unit R" and "rquot_proj (CommIdeal R)")
      (cannot unify "rig_map (crng_unit R)" and "rig_map (rquot_proj
      (CommIdeal R))")
    CORRECTION (#1347): N8, N10 and N12, the setoid-morphism components,
    now hold at [eq_refl], since Instance/Sets.v gives its identity's and
    composite's properness fields as terms; they are controls, and N7, N9
    and N11, the whole records, are still refused.  N8, N10 and N12 were
    CONVERSION by their errors; the three target headers gave their cause
    as a composite whose setoid-morphism component differs, by argument,
    and the measurement shows the residue was the standard library's: the
    opaque lemmas instance resolution had put in the two properness fields, the
    identity's and that composite's.
    N13, N14 (CONVERSION).  Uniform.v's STRENGTHS, in [MetU] and in
    [Met]:
      (cannot unify "unit" and "etaU X")
      (cannot unify "unit" and "eta X")
    CORRECTION (#1347): N13 likewise now holds at [eq_refl] and is a
    control, the unit in [MetU] being [etaU X] as a whole record; N14, in
    [Met], is still refused.  Uniform.v's cause, the unit being the
    transpose [fmap[Incl] id ∘ etaU X], was argued; in [MetU] the residue
    was the standard library's, as above.
    N15 (CONVERSION).  RingEpi.v's STRENGTHS, against Instance/Mod/
    Extension.v's unit:
      (cannot unify "unit" and "extend_adj_unit phi Hc M")

    ** Arrow parts, counits and a composite functor

    N16 and N18-N21 are [unique_obj] of Theory/Universal/Arrow.v's
    [Qed]-closed [ump_universal_arrows].  Measured by flipping, that
    [Qed] is the whole cause for N19 (a transparent copy reads the
    torsion corestriction back whole) and not for N16, N20 or N21 (the
    same flip leaves them refused); N18 was not flipped.  N17 involves
    no universal arrow: its refusal sits in the law fields of the
    composite functor.  Controls: the abelianization reflector
    against Abelianize.v's on objects at [eq_refl] and on arrows up to
    [≈] ([p370_abgrp_factors_obj], [p370_abgrp_factors_fmap]); the
    inclusion's factorization on arrows at [eq_refl] and as functors up
    to [≈] ([p370_ab_to_grp_fmap], [p370_ab_to_grp_factors]); the
    abelianization counit invertible ([p370_abgrp_counit_iso]); the
    torsion couniversal arrow IS [torsion_incl] ([p370_torsion_coarrow]);
    the MetU reflector's object IS the completion
    ([p370_completionU_obj]).

    N16, N17 (CONVERSION).  Abelianize/Reflective.v's STRENGTHS, the
    arrow part and the whole factorization:
      (cannot unify "fmap[AbGrp_reflector] f" and "fmap[Ab_to_AbGrp]
      (fmap[Abelianization_Functor] f)")
      (cannot unify "Incl Grp AbGrp_Sub ◯ Ab_to_AbGrp" and "Ab_to_Grp")
    N18 (CONVERSION).  The same header, the counit at an element:
      (cannot unify "projT1 counit a" and "a")
    N19 (CONVERSION).  Torsion.v's STRENGTHS, the coreflector's arrow
    part against the corestriction:
      (cannot unify "fmap[torsion_coreflector] f" and "(torsion_lift
      (TorsionAb_IsTorsion A) (f ∘ torsion_incl A); I)")
    N20, N21 (CONVERSION).  Uniform.v's STRENGTHS, the counit and the
    reflector's arrow part at an embedded point:
      (cannot unify "projT1 counit (eta_seq `1 (Y) y)" and "y")
      (cannot unify "projT1 (fmap[reflector CMet_Reflective_in_MetU] f)
      (eta_seq X a)" and "eta_seq Y (f a)")

    ** Instance/Met/Uniform.v: MetU is not Met

    Controls: a constant map of [Harmonic] is an arrow of [MetU]
    ([p370_const_umap]); the comparison is the identity on objects
    ([p370_met_to_metu_obj]) and is not full ([p370_not_full]).

    N22 (TYPING).  The same constant map is not an arrow of [Met]:
      The term "const_umap Harmonic Harmonic 0%nat" has type "UMap
      Harmonic Harmonic" while it is expected to have type "Harmonic ~{
      Met }~> Harmonic".

    ** Instance/Mod/RingEpi.v: clause (iv)

    Controls: the localization's universal property at a ring of carrier
    level [Set] ([p370_loc_at_set]); the mediator [loc_hom] at a ring
    above it ([p370_loc_hom_above]); restriction full exactly for
    epimorphisms, for arbitrary rings ([p370_full_iff_epic]); the
    reflection's adjunction as its own constant ([p370_tmod_adj]).

    N23 (UNIVERSE).  RingEpi.v's UNIVERSES: [ZtoQ_IsLocalization] at a
    ring W above [Set], N23:
      The term "W" has type "obj[Rng@{u p}]" while it is expected to
      have type "obj[Rng@{<1> Set}]" (universe inconsistency: Cannot
      enforce Set = p).
    Here <1> stands for the universe the stripped copy names after
    itself and a serial number.

    ** Non-vacuity, and the reals

    Controls, each statement restated independently of its proof: the
    reflection of S₃ is not trivial on its own setoid
    ([p370_S3_nontrivial]) and its unit is not invertible
    ([p370_S3_not_iso]); the torsion counit at ℤ × ℤ/2
    ([p370_mixed_not_iso]), the commutator-ideal unit at UT2
    ([p370_UT2_not_iso]) and the completion unit at the harmonic space
    ([p370_harmonic_not_iso]) are not invertible; ℤ is not in the
    subcategory of the ℤ → ℚ reflection ([p370_ZMod_not_fixed]).

    The reals are not a refutation.  [Print Assumptions
    CMet_Reflective_in_MetU], near the end of this file, prints the
    three standard-library axioms of the reals that every constant of
    Instance/Met/Uniform.v from [uext_seq] on carries
    ([ClassicalDedekindReals.sig_forall_dec],
    [ClassicalDedekindReals.sig_not_dec] and
    [functional_extensionality_dep]); a [Print Assumptions] cannot
    refuse, so the line is a readback and guards nothing.  By the same
    command, the seven constants of this file that mention [MetU],
    [Met] or [Harmonic] carry the reals axioms too; the other thirty-one
    are closed under the global context.
    CORRECTION (#1347): by the same command, in a copy of this WHOLE file,
    eight of the forty-two constants it now defines carry the reals
    axioms, N13's the eighth, and the other thirty-four are closed.

    NOT PINNED HERE.  (a) [About] readbacks as such, the headers' [Set]
    censuses and their attributions to first carriers: pinned only where
    a binder carries them or a refusal does (N23, and the controls with
    their levels in [Set] or strictly above it).  (b) Flip censuses
    ([Defined] against [Qed]) and the closure of the targets under
    [Print Assumptions]: measurements of the build rather than of
    commands; the Makefile's print-assumptions gate is where closure is
    kept.  (c) Construction/Reflective/Monadic.v's [pose] against [pose
    proof]: a step of a proof script, not a statement.  (d) Construction/
    Reflective/Coreflective.v's refusal of the donor's [from] and [to]
    handed to [Build_Isomorphism Sets] as they stand; its cause, the two
    hom-setoids not converting, is N4.  (e) The facts the headers argue
    and do not formalize: that x ↦ 1/x is continuous and not uniformly
    continuous, and that an epimorphism out of a commutative ring has a
    commutative target.  (f) The absences the headers record (no
    bimodule tensor, hence [CentralImage] on the T-Mod record; no
    general R[S⁻¹]): an absence has no command.

    The guard block at the end names the two hundred and ninety-one
    constants of the nine targets, so that a rename breaks this file:
    fifteen of Construction/Reflective/Coreflective.v, fourteen of
    Construction/Reflective/Monadic.v, six of Construction/Reflective/
    Universal.v, sixty-one of Instance/Grp/Abelianize/Reflective.v,
    thirty-seven of Instance/Ab/Torsion.v, thirty of Instance/Rng/
    Commutativize.v, fifteen of Instance/Rng/Commutativize/UT2.v,
    fifty-eight of Instance/Mod/RingEpi.v and fifty-five of Instance/Met/
    Uniform.v.  They are exactly the entries [Print Module] gives for
    each, [Program] obligations and the generated schemes of
    [InCommIdeal] among them, with the record constructor [Build_UMap]
    and the six constructors of [InCommIdeal].  The two hundred and
    thirty-six closed under the global context come first; the
    fifty-five of Instance/Met/Uniform.v, none of them closed, come last
    under their own heading.  Under the full import list each short name
    denotes the target's constant ([Locate] lists it first), and the
    thirty-four [Program] obligations, which [Import] does not make
    visible by the short name, are written with their module's last
    component, the name [Locate] gives as the shorter one. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Coreflective.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Construction.Reflective.Universal.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Abelianization.
Require Import Category.Instance.Grp.Abelianize.
Require Import Category.Instance.Grp.Abelianize.Reflective.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Instance.Ab.TorsionFree.
Require Import Category.Instance.Ab.Torsion.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Commutativize.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Rng.Commutativize.UT2.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.
Require Import Category.Instance.Met.
Require Import Category.Instance.Met.Completion.
Require Import Category.Instance.Met.Uniform.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Coproduct.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Instance.Mod.Extension.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Adjunction.FullFaithful.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import Category.Instance.Mod.RingEpi.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

(* The instrument *)
Fail Check p370_absent_name.

(** ** Instance/Grp/Abelianize/Reflective.v: why a new subcategory *)

(* CONTROL: the inclusion of [AbGrp_Sub], the record over it, and
   Abelianize.v's [Ab_to_Grp] factoring through it on objects. *)
Definition p370_abgrp_incl@{u p +} : Sub Grp@{u p} AbGrp_Sub ⟶ Grp@{u p} :=
  Incl Grp@{u p} AbGrp_Sub.

Definition p370_abgrp_record@{u p +} : @Reflective Grp@{u p} AbGrp_Sub :=
  Ab_Reflective_in_Grp.

Example p370_ab_to_grp_obj@{u p +} (A : Ab@{u p}) :
  Incl Grp@{u p} AbGrp_Sub (Ab_to_AbGrp A) = Ab_to_Grp A := eq_refl.

(* N1 *)
Fail Definition p370_incl_is_ab_to_grp (S : Subcategory Grp) :
  Incl Grp S = Ab_to_Grp := eq_refl.

(* N2 *)
Fail Definition p370_record_from_abelianize (S : Subcategory Grp) :
  Reflective S :=
  @Build_Reflective Grp S _ Abelianization_Functor
    abelianize_adjunction_via_transform.

(** ** Construction/Reflective/Coreflective.v: what the bridge is for *)

(* CONTROL: the objects, the hom types and the two [equiv] relations of
   the two categories convert. *)
Example p370_op_obj {C : Category} (S : Subcategory C) :
  obj[Opposite (Sub C S)] = obj[Sub (Opposite C) (op_subcategory S)]
  := eq_refl.

Example p370_op_hom {C : Category} (S : Subcategory C) (x y : Sub C S) :
  @hom (Opposite (Sub C S)) x y
    = @hom (Sub (Opposite C) (op_subcategory S)) x y := eq_refl.

Example p370_op_equiv {C : Category} (S : Subcategory C) (x y : Sub C S) :
  @Setoid.equiv _ (@homset (Opposite (Sub C S)) x y)
    = @Setoid.equiv _ (@homset (Sub (Opposite C) (op_subcategory S)) x y)
  := eq_refl.

(* N3 *)
Fail Example p370_op_cat {C : Category} (S : Subcategory C) :
  Opposite (Sub C S) = Sub (Opposite C) (op_subcategory S) := eq_refl.

(* N4 *)
Fail Example p370_op_homset {C : Category} (S : Subcategory C)
  (x y : Sub C S) :
  @homset (Opposite (Sub C S)) x y
    = @homset (Sub (Opposite C) (op_subcategory S)) x y := eq_refl.

(* CONTROL: a record read back covariantly and rebuilt is the record,
   and its coreflector is a covariant functor into the subcategory. *)
Example p370_bridge_roundtrip {C : Category} {S : Subcategory C}
  (R : Coreflective S) :
  Coreflective_of_adjunction (coreflective_full R) (coreflector R)
    (coreflective_adj R) = R := eq_refl.

Definition p370_coreflector_covariant {C : Category} {S : Subcategory C}
  (R : Coreflective S) : C ⟶ Sub C S := coreflector R.

(* N5 *)
Fail Example p370_coreflector_is_reflector {C : Category}
  {S : Subcategory C} (R : Coreflective S) :
  coreflector R = reflector R := eq_refl.

(** ** The units, as records and pointwise *)

(* CONTROL: from universal arrows, the unit is the transpose of the
   identity on the nose. *)
Example p370_ua_unit {C : Category} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  @Category.Theory.Adjunction.unit _ _ _ _
    (reflective_adj (Reflective_of_UniversalArrows full UA)) x
    = fmap[Incl C S]
        (@id (Sub C S)
           (fobj[reflector (Reflective_of_UniversalArrows full UA)] x))
      ∘ @arrow C (Sub C S) x (Incl C S) (UA x) := eq_refl.

(* N6 *)
Fail Example p370_ua_unit_arrow {C : Category} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  @Category.Theory.Adjunction.unit _ _ _ _
    (reflective_adj (Reflective_of_UniversalArrows full UA)) x
    = @arrow C (Sub C S) x (Incl C S) (UA x) := eq_refl.

(* CONTROL: the abelianization unit, as the transposed composite and
   pointwise as Mac Lane's projection. *)
Example p370_abgrp_unit@{u p +} (G : Grp@{u p}) :
  abgrp_unit G
    = fmap[Incl Grp@{u p} AbGrp_Sub] (@id AbGrp (fobj[AbGrp_reflector] G))
      ∘ abel_proj G := eq_refl.

Example p370_abgrp_unit_point@{u p +} (G : Grp@{u p}) (a : carrier G) :
  grp_map (abgrp_unit G) a = grp_map (abel_proj G) a := eq_refl.

(* N7 *)
Fail Example p370_abgrp_unit_proj@{u p +} (G : Grp@{u p}) :
  abgrp_unit G = abel_proj G := eq_refl.

(* N8 *)
Example p370_abgrp_unit_map@{u p +} (G : Grp@{u p}) :
  grp_map (abgrp_unit G) = grp_map (abel_proj G) := eq_refl.

(* CONTROL: the torsion counit, likewise, against the inclusion of TA. *)
Example p370_torsion_counit@{u p +} (A : Ab@{u p}) :
  torsion_counit A
    = torsion_incl A
      ∘ fmap[Incl Ab@{u p} Torsion_Sub]
          (@id TorsionCat (fobj[torsion_coreflector] A)) := eq_refl.

Example p370_torsion_counit_point@{u p +} (A : Ab@{u p})
  (x : carrier (TorsionAb A)) :
  cmon_map (torsion_counit A) x = cmon_map (torsion_incl A) x := eq_refl.

(* N9 *)
Fail Example p370_torsion_counit_incl@{u p +} (A : Ab@{u p}) :
  torsion_counit A = torsion_incl A := eq_refl.

(* N10 *)
Example p370_torsion_counit_map@{u p +} (A : Ab@{u p}) :
  cmon_map (torsion_counit A) = cmon_map (torsion_incl A) := eq_refl.

(* CONTROL: the commutator-ideal unit, likewise, against the quotient
   map. *)
Example p370_crng_unit@{u p +} (R : Rng@{u p}) :
  crng_unit R
    = fmap[Incl Rng@{u p} CRng_Sub] (@id CRng (fobj[CRng_reflector] R))
      ∘ rquot_proj (CommIdeal R) := eq_refl.

Example p370_crng_unit_point@{u p +} (R : Rng@{u p})
  (a : carrier (rig_setoid R)) :
  rig_map (crng_unit R) a = rig_map (rquot_proj (CommIdeal R)) a := eq_refl.

(* N11 *)
Fail Example p370_crng_unit_proj@{u p +} (R : Rng@{u p}) :
  crng_unit R = rquot_proj (CommIdeal R) := eq_refl.

(* N12 *)
Example p370_crng_unit_map@{u p +} (R : Rng@{u p}) :
  rig_map (crng_unit R) = rig_map (rquot_proj (CommIdeal R)) := eq_refl.

(* CONTROL: the completion unit in MetU and in Met, pointwise the
   constant sequence. *)
Example p370_completionU_unit_point@{u o +} (X : MetU@{u o}) (a : X) :
  umap (@Category.Theory.Adjunction.unit _ _ _ _ completionU_adj X) a
    = eta_seq X a := eq_refl.

Example p370_completion_unit_point@{u o +} (X : Met@{u o}) (a : X) :
  isometry_map (@Category.Theory.Adjunction.unit _ _ _ _ completion_adj X) a
    = eta_seq X a := eq_refl.

(* N13 *)
Example p370_completionU_unit_eta@{u o +} (X : MetU@{u o}) :
  @Category.Theory.Adjunction.unit _ _ _ _ completionU_adj X = etaU X
  := eq_refl.

(* N14 *)
Fail Example p370_completion_unit_eta@{u o +} (X : Met@{u o}) :
  @Category.Theory.Adjunction.unit _ _ _ _ completion_adj X = eta X
  := eq_refl.

(* CONTROL: the unit of the T-Mod reflection, pointwise Riehl's 1 ⊗ m. *)
Example p370_tmod_unit_point {R T : Rng} (phi : R ~{Rng}~> T)
  (Hc : CentralImage phi) (He : Epic phi) (M : RMod R)
  (m : carrier (cmon_setoid M)) :
  cmon_map
    (rm_hom (@Category.Theory.Adjunction.unit _ _ _ _
               (TMod_adj phi Hc He) M)) m
    = ext_gen phi M (rig_one (ring_rig T)) m := eq_refl.

(* N15 *)
Fail Example p370_tmod_unit_ext {R T : Rng} (phi : R ~{Rng}~> T)
  (Hc : CentralImage phi) (He : Epic phi) (M : RMod R) :
  @Category.Theory.Adjunction.unit _ _ _ _ (TMod_adj phi Hc He) M
    = extend_adj_unit phi Hc M := eq_refl.

(** ** Arrow parts, counits and a composite functor *)

(* CONTROL: the abelianization reflector against Abelianize.v's, on
   objects on the nose and on arrows up to [≈]. *)
Example p370_abgrp_factors_obj@{u p +} (G : Grp@{u p}) :
  fobj[AbGrp_reflector] G
    = fobj[Ab_to_AbGrp] (fobj[Abelianization_Functor] G) := eq_refl.

Definition p370_abgrp_factors_fmap@{u p +} (G H : Grp@{u p})
  (f : G ~{Grp@{u p}}~> H) :
  fmap[AbGrp_reflector] f
    ≈ fmap[Ab_to_AbGrp] (fmap[Abelianization_Functor] f) :=
  abgrp_reflector_factors_fmap G H f.

(* N16 *)
Fail Example p370_abgrp_factors_fmap_eq@{u p +} (G H : Grp@{u p})
  (f : G ~{Grp@{u p}}~> H) :
  fmap[AbGrp_reflector] f
    = fmap[Ab_to_AbGrp] (fmap[Abelianization_Functor] f) := eq_refl.

(* CONTROL: the inclusion's factorization agrees on arrows on the nose,
   and as functors up to [≈]. *)
Example p370_ab_to_grp_fmap@{u p +} (A B : Ab@{u p})
  (f : A ~{Ab@{u p}}~> B) :
  fmap[Incl Grp@{u p} AbGrp_Sub] (fmap[Ab_to_AbGrp] f) = fmap[Ab_to_Grp] f
  := eq_refl.

Definition p370_ab_to_grp_factors@{u p +} :
  Incl Grp@{u p} AbGrp_Sub ◯ Ab_to_AbGrp ≈ Ab_to_Grp :=
  ab_to_grp_factors.

(* N17 *)
Fail Example p370_ab_to_grp_factors_eq@{u p +} :
  Incl Grp@{u p} AbGrp_Sub ◯ Ab_to_AbGrp = Ab_to_Grp := eq_refl.

(* CONTROL: the abelianization counit is invertible at every object of
   the subcategory. *)
Definition p370_abgrp_counit_iso@{u p +} (d : Sub Grp@{u p} AbGrp_Sub) :
  fobj[AbGrp_reflector] (fobj[Incl Grp@{u p} AbGrp_Sub] d) ≅[AbGrp] d :=
  abgrp_reflect_iso d.

(* N18 *)
Fail Example p370_abgrp_counit_point@{u p +} (d : Sub Grp@{u p} AbGrp_Sub)
  (a : carrier `1 d) :
  grp_map `1 (@counit _ _ _ _ AbGrp_adj d) a = a := eq_refl.

(* CONTROL: the couniversal arrow of the torsion coreflection is the
   inclusion of TA, on the nose. *)
Example p370_torsion_coarrow@{u p +} (A : Ab@{u p}) :
  @coarrow Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub)
    (torsion_couniversal_arrow A) = torsion_incl A := eq_refl.

(* N19 *)
Fail Example p370_torsion_fmap@{u p +} (A B : Ab@{u p})
  (f : A ~{Ab@{u p}}~> B) :
  fmap[torsion_coreflector] f
    = (torsion_lift (TorsionAb_IsTorsion A) (f ∘ torsion_incl A); I)
  := eq_refl.

(* CONTROL: the MetU reflector's object is the completion, the whole
   Σ-object, on the nose. *)
Example p370_completionU_obj@{u o +} (X : MetU@{u o}) :
  fobj[reflector CMet_Reflective_in_MetU] X = CompletionU X := eq_refl.

(* N20 *)
Fail Example p370_completionU_counit_point@{u o +}
  (Y : Sub MetU@{u o} CompleteSpacesU) (y : `1 Y) :
  umap (`1 (@counit _ _ _ _ completionU_adj Y)) (eta_seq (`1 Y) y) = y
  := eq_refl.

(* N21 *)
Fail Example p370_completionU_fmap_point@{u o +} (X Y : MetU@{u o})
  (f : X ~{MetU@{u o}}~> Y) (a : X) :
  umap (`1 (fmap[reflector CMet_Reflective_in_MetU] f)) (eta_seq X a)
    = eta_seq Y (umap f a) := eq_refl.

(** ** Instance/Met/Uniform.v: MetU is not Met *)

(* CONTROL: a constant map of [Harmonic] is an arrow of [MetU]; the
   comparison is the identity on objects; and it is not full. *)
Definition p370_const_umap@{u +| Set < u +} :
  Harmonic ~{MetU@{u Set}}~> Harmonic :=
  const_umap Harmonic Harmonic 0%nat.

Example p370_met_to_metu_obj@{u o +| o < u +} (X : Met@{u o}) :
  fobj[Met_to_MetU@{u o}] X = X := eq_refl.

Definition p370_not_full@{u +| Set < u +} :
  Functor.Full Met_to_MetU@{u Set} → False := Met_to_MetU_not_Full.

(* N22 *)
Fail Definition p370_const_isometry@{u +| Set < u +} :
  Harmonic ~{Met@{u Set}}~> Harmonic :=
  const_umap Harmonic Harmonic 0%nat.

(** ** Instance/Mod/RingEpi.v: clause (iv) *)

(* CONTROL: the localization's universal property at a ring of carrier
   level [Set], and the mediator [loc_hom] above it. *)
Definition p370_loc_at_set@{u +| Set < u +} (W : obj[Rng@{u Set}])
  (psi : Int_Ring ~{Rng@{u Set}}~> W)
  (H : InvertsSet (R := Int_Ring) PosZ psi) :=
  @snd _ _ ZtoQ_IsLocalization W psi H.

Definition p370_loc_hom_above@{u p +| Set < p, p < u +}
  (W : obj[Rng@{u p}]) (psi : Int_Ring ~{Rng@{u p}}~> W)
  (H : InvertsSet (R := Int_Ring) PosZ psi) : Q_Ring ~{Rng@{u p}}~> W :=
  loc_hom W psi H.

(* N23 *)
Fail Definition p370_loc_above@{u p +| Set < p, p < u +}
  (W : obj[Rng@{u p}]) (psi : Int_Ring ~{Rng@{u p}}~> W)
  (H : InvertsSet (R := Int_Ring) PosZ psi) :=
  @snd _ _ ZtoQ_IsLocalization W psi H.

(* CONTROL: restriction is full exactly for epimorphisms, for arbitrary
   rings, and the reflection's adjunction is its own constant. *)
Definition p370_full_iff_epic {R T : Rng} (phi : R ~{Rng}~> T) :
  Functor.Full (Restrict phi) ↔ Epic phi := Restrict_Full_iff_Epic phi.

Definition p370_tmod_adj {R T : Rng} (phi : R ~{Rng}~> T)
  (Hc : CentralImage phi) (He : Epic phi) :
  reflector (TMod_Reflective_in_RMod phi Hc He)
    ⊣ Incl (RMod R) (UnitFixed (extend_restrict_adjunction phi Hc)) :=
  TMod_adj phi Hc He.

(** ** Non-vacuity, restated *)

(* CONTROL: each reflection or coreflection is proper at a named object,
   the statement restated independently of its proof. *)
Definition p370_S3_nontrivial@{u +} :
  @Setoid.equiv (carrier `1 (fobj[AbGrp_reflector] (S3 : Grp@{u Set}))) _
    S3_s s3_unit → False := S3_reflection_nontrivial.

Definition p370_S3_not_iso@{u +} :
  IsIsomorphism (abgrp_unit (S3 : Grp@{u Set})) → False :=
  abgrp_unit_S3_not_iso.

Definition p370_mixed_not_iso@{u +} :
  IsIsomorphism (torsion_counit (MixedAb : Ab@{u Set})) → False :=
  torsion_counit_MixedAb_not_iso.

Definition p370_UT2_not_iso@{u p +} :
  IsIsomorphism (crng_unit (UT2 : Rng@{u p})) → False :=
  crng_unit_UT2_not_iso.

Definition p370_harmonic_not_iso@{u +| Set < u +} :
  IsIsomorphism
    (@Category.Theory.Adjunction.unit _ _ _ _ completionU_adj
       (Harmonic : MetU@{u Set})) → False :=
  completionU_unit_Harmonic_not_iso.

Definition p370_ZMod_not_fixed :
  sobj (RMod Int_Ring) (UnitFixed (extend_restrict_adjunction ZtoQ Q_central))
    (Ring_RMod Int_Ring) → False := ZMod_not_UnitFixed.

(** ** The reals: a readback, not a refutation *)

(* Prints ClassicalDedekindReals.sig_forall_dec,
   ClassicalDedekindReals.sig_not_dec and functional_extensionality_dep;
   see the header. *)
Print Assumptions CMet_Reflective_in_MetU.

(** ** Guard: the constants of the nine targets closed under the global
    context *)

(* Construction/Reflective/Coreflective.v: 15 names. *)
Check Coreflective_of_adjunction.
Check Coreflective_roundtrip.
Check coreflective_adj.
Check coreflective_adj_roundtrip.
Check coreflective_counit_is_op_unit.
Check coreflective_full.
Check coreflective_full_roundtrip.
Check coreflective_unit_is_op_counit.
Check coreflective_unit_iso.
Check coreflector.
Check coreflector_fmap_roundtrip.
Check coreflector_obj_roundtrip.
Check coreflector_op.
Check coreflector_op_adj.
Check coreflector_roundtrip.

(* Construction/Reflective/Monadic.v: 14 names. *)
Check Reflective_EM_Equivalence.
Check Reflective_Monadic.
Check Reflective_Monadic_left.
Check reflective_comparison.
Check reflective_comparison_ESO.
Check reflective_comparison_Faithful.
Check reflective_comparison_Full.
Check reflective_comparison_alg.
Check reflective_comparison_obj.
Check reflective_comparison_prefmap.
Check reflective_eso_iso.
Check reflective_eso_iso_to.
Check reflective_eso_obj.
Check reflective_eso_obj_is_reflector.

(* Construction/Reflective/Universal.v: 6 names. *)
Check Coreflective_of_CouniversalArrows.
Check Coreflective_of_CouniversalArrows_counit.
Check Coreflective_of_CouniversalArrows_obj.
Check Reflective_of_UniversalArrows.
Check Reflective_of_UniversalArrows_obj.
Check Reflective_of_UniversalArrows_unit.

(* Instance/Grp/Abelianize/Reflective.v: 61 names. *)
Check AbGrp.
Check AbGrp_Full.
Check AbGrp_IdempotentMonad.
Check AbGrp_Incl_Monadic.
Check AbGrp_Sub.
Check AbGrp_adj.
Check AbGrp_iso.
Check AbGrp_reflector.
Check AbTwo_in_AbGrp.
Check Ab_AbGrp_Equivalence.
Check Ab_Reflective_in_Grp.
Check Ab_to_AbGrp.
Check Ab_to_AbGrp_ESO.
Check Ab_to_AbGrp_Faithful.
Check Ab_to_AbGrp_Full.
Check AbelianizationGrp.
Check Grp_to_AbOb.
Check IsAbelian.
Check Reflective.AbGrp_iso_obligation_1.
Check Reflective.AbGrp_iso_obligation_2.
Check Reflective.AbGrp_iso_obligation_3.
Check Reflective.AbGrp_iso_obligation_4.
Check Reflective.AbGrp_iso_obligation_5.
Check Reflective.AbGrp_iso_obligation_6.
Check Reflective.AbGrp_iso_obligation_7.
Check Reflective.AbGrp_iso_obligation_8.
Check Reflective.Ab_to_AbGrp_Full_obligation_1.
Check Reflective.Ab_to_AbGrp_obligation_1.
Check Reflective.Ab_to_AbGrp_obligation_2.
Check Reflective.Ab_to_AbGrp_obligation_3.
Check Reflective.Grp_to_AbOb_obligation_1.
Check Reflective.Grp_to_AbOb_obligation_2.
Check Reflective.Grp_to_AbOb_obligation_3.
Check Reflective.Grp_to_AbOb_obligation_4.
Check Reflective.abel_med_grp_obligation_1.
Check Reflective.abel_med_grp_obligation_2.
Check Reflective.abel_med_grp_obligation_3.
Check S3_not_IsAbelian.
Check S3_reflection_nontrivial.
Check ab_to_grp_factors.
Check ab_to_grp_factors_fmap.
Check ab_to_grp_factors_obj.
Check abel_kills_grp.
Check abel_med_grp.
Check abgrp_S3_med_s.
Check abgrp_S3_med_unit.
Check abgrp_S3_separates.
Check abgrp_arrow_is_proj.
Check abgrp_record_reflector.
Check abgrp_reflect_iso.
Check abgrp_reflector_factors.
Check abgrp_reflector_factors_fmap.
Check abgrp_reflector_factors_obj.
Check abgrp_reflector_obj.
Check abgrp_unit.
Check abgrp_unit_S3_merges.
Check abgrp_unit_S3_not_iso.
Check abgrp_unit_is_proj.
Check abgrp_unit_pointwise.
Check abgrp_universal.
Check abgrp_universal_arrow.

(* Instance/Ab/Torsion.v: 37 names. *)
Check IsTorsion.
Check MixedAb_not_torsion.
Check Torsion.torsion_lift_obligation_1.
Check Torsion.torsion_lift_obligation_2.
Check Torsion.torsion_lift_obligation_3.
Check TorsionAb_IsTorsion.
Check TorsionCat.
Check TorsionFree_EM_Equivalence.
Check TorsionFree_EM_MLocal.
Check TorsionFree_IdempotentMonad.
Check TorsionFree_Incl_Monadic.
Check TorsionFree_Monad.
Check TorsionPart.
Check Torsion_Coreflective.
Check Torsion_Full.
Check Torsion_Sub.
Check ZAb_TA_trivial.
Check ZMod2_IsTorsion.
Check ZMod2_Torsion.
Check ZMod2_coreflect_iso.
Check mixed_tors_in_TA.
Check mixed_tors_in_TA_nonzero.
Check torsion_coarrow_is_incl.
Check torsion_coreflection.
Check torsion_coreflector.
Check torsion_coreflector_obj.
Check torsion_counit.
Check torsion_counit_MixedAb_not_iso.
Check torsion_counit_is_incl.
Check torsion_counit_pointwise.
Check torsion_couniversal.
Check torsion_couniversal_arrow.
Check torsion_lift.
Check torsion_map.
Check torsion_record_adj.
Check torsion_record_coreflector.
Check torsionfree_monad_obj.

(* Instance/Rng/Commutativize.v: 30 names. *)
Check CRng_Reflective_in_Rng.
Check CRng_adj.
Check CRng_reflector.
Check CommIdeal.
Check Commutativize.
Check CommutativizeC.
Check Commutativize_comm.
Check InCommIdeal.
Check InCommIdeal_ind.
Check InCommIdeal_rec.
Check InCommIdeal_rect.
Check InCommIdeal_sind.
Check IsCommutative.
Check IsCommutative_is_CRng_sobj.
Check comm_kills.
Check crng_arrow_is_proj.
Check crng_reflect_iso.
Check crng_reflector_obj.
Check crng_unit.
Check crng_unit_is_proj.
Check crng_unit_pointwise.
Check crng_universal.
Check crng_universal_arrow.
Check ici_add.
Check ici_gen.
Check ici_mul_l.
Check ici_mul_r.
Check ici_resp.
Check ici_zero.
Check rcomm.

(* Instance/Rng/Commutativize/UT2.v: 15 names. *)
Check Commutativize_UT2_nonzero.
Check UT2.ut2_diag1_hom_obligation_1.
Check UT2.ut2_diag1_hom_obligation_2.
Check UT2.ut2_diag1_hom_obligation_3.
Check UT2.ut2_diag1_hom_obligation_4.
Check UT2_not_commutative_ring.
Check crng_UT2_med_one.
Check crng_unit_UT2_merges.
Check crng_unit_UT2_not_iso.
Check ut2_diag1.
Check ut2_diag1_hom.
Check ut2_diag1_proper.
Check ut2_e12_commutator.
Check ut2_e12_in_CommIdeal.
Check ut2_e12_nonzero.

(* Instance/Mod/RingEpi.v: 58 names. *)
Check AbEndRing.
Check EndRig_conj.
Check Epic_Restrict_Full.
Check Epic_Restrict_Full_prefmap.
Check InvertsSet.
Check IsLocalization.
Check PosZ.
Check QMod_Reflective_in_ZMod.
Check QMod_equiv_UnitFixed.
Check Restrict_Faithful.
Check Restrict_Full_Epic.
Check Restrict_Full_iff_Epic.
Check Restrict_UnitFixed.
Check Restrict_UnitFixed_ESO.
Check Restrict_UnitFixed_Faithful.
Check Restrict_UnitFixed_Full.
Check Restrict_UnitFixed_incl.
Check Restrict_UnitFixed_obj.
Check Restrict_ZtoQ_Full.
Check TMod_Reflective_in_RMod.
Check TMod_adj.
Check TMod_equiv_UnitFixed.
Check TMod_reflector_obj.
Check TMod_unit_pointwise.
Check ZMod_not_UnitFixed.
Check ZtoQ_IsLocalization.
Check ZtoQ_epic_of_localization.
Check ZtoQ_inverts.
Check inject_pos_nonzero.
Check linear_of_twist_fixed.
Check loc_cancel.
Check loc_fun.
Check loc_fun_add.
Check loc_fun_mul.
Check loc_fun_respects.
Check loc_fun_spec.
Check loc_hom.
Check loc_hom_factors.
Check loc_hom_unique.
Check loc_images_commute.
Check loc_inv.
Check loc_inv_l.
Check loc_inv_one.
Check loc_inv_r.
Check loc_morphism.
Check loc_split.
Check localization_epic.
Check module_rep.
Check restrict_counit_iso.
Check restrict_idempotent.
Check shear_from.
Check shear_iso.
Check shear_to.
Check smul_endo.
Check twist_fixed_of_linear.
Check twisted_rep.
Check twisted_rep_value.
Check two_actions_id.

(** ** Guard: the reals-bound constants of Instance/Met/Uniform.v *)

(* Instance/Met/Uniform.v: 55 names, none closed under the global
   context.  By [Print Assumptions], 28 carry
   ClassicalDedekindReals.sig_forall_dec alone; 3 ([const_umap],
   [Met_to_MetU_not_Full], [ureal_below_all_zero]) carry it and
   functional_extensionality_dep; the other 24 carry those two and
   ClassicalDedekindReals.sig_not_dec. *)
Check Build_UMap.
Check CMetU.
Check CMetU_Full.
Check CMetU_Incl.
Check CMet_Reflective_in_Met.
Check CMet_Reflective_in_MetU.
Check CompleteSpacesU.
Check CompletionU.
Check CompletionU_UniversalArrow.
Check MetU.
Check Met_to_MetU.
Check Met_to_MetU_Faithful.
Check Met_to_MetU_not_Full.
Check Met_to_MetU_obj.
Check UCont.
Check UMap.
Check UMap_Setoid.
Check UMap_equiv.
Check Uniform.MetU_obligation_1.
Check Uniform.MetU_obligation_2.
Check Uniform.MetU_obligation_3.
Check Uniform.MetU_obligation_4.
Check Uniform.Met_to_MetU_obligation_1.
Check Uniform.Met_to_MetU_obligation_2.
Check Uniform.Met_to_MetU_obligation_3.
Check Uniform.UMap_Setoid_obligation_1.
Check completionU_adj.
Check completionU_reflector_obj.
Check completionU_unit_Harmonic_not_iso.
Check completionU_unit_pointwise.
Check completion_adj.
Check completion_reflector_obj.
Check completion_reflectors_agree.
Check completion_unit_pointwise.
Check const_umap.
Check etaU.
Check iso_umap.
Check uext.
Check uext_MCauchy.
Check uext_close.
Check uext_eta.
Check uext_morphism.
Check uext_proper.
Check uext_seq.
Check uext_spec.
Check uext_uc.
Check uext_unique.
Check uext_val.
Check umap.
Check umap_MConverges.
Check umap_uc.
Check umet_compose.
Check umet_compose_respects.
Check umet_id.
Check ureal_below_all_zero.
