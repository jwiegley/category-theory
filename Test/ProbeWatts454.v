(** * Probe for Watt's theorem and Mac Lane V.8 Exercises 2-3 (issue #454)

    Pins the measured boundaries of the seven files #454 adds for Mac
    Lane §V.8, printed pp. 131-132 (Watt's theorem in the text, Exercise 2
    and Exercise 3): Functor/Representable/Additive.v (the Ab-valued hom
    functors, their continuity and the additive upgrade),
    Instance/Mod/HomTensor.v (Exercise 2(a)), Instance/Mod/Cogenerator.v
    (Exercise 2(b) on the book's premise, with its metatheorems),
    Instance/Mod/WellPowered.v, Instance/Mod/Colimit.v,
    Instance/Mod/Watts.v (the text form and Exercise 3 through the special
    adjoint functor theorem, over [Untruncate]) and
    Instance/Mod/Watts/Unconditional.v (the text form with no hypothesis,
    through the general one).  Most negatives restate a refusal a target
    header quotes, measured on #454 by its builders and reviews.
    N3 and N7 pin as refusals two equations the headers record as
    readbacks ([About] printing "ra = rc" and "x = w"); N24 and N25
    restate the review's measurement of the [Set] boundary that
    Unconditional.v's header states in words; N11, N18, N20, N21 and N22
    restate header refusals in a peeled or constant-level form, each
    paragraph saying how; N23, N26 and N27 are this file's own.  N28, N29
    and N30 pin the other side of the equations N7, N19 and N20 pin, and
    N31-N34 are Instance/Mod/Watts.v's refusals of
    [HomAbForget_continuous]'s body in that header's own form.  N28-N34
    were added after N1-N27 had been cited, so they sit beside the
    negatives they pair with rather than in the order of their numbers.
    The positive controls restate the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines with comments
    stripped.  First Instance/Mod/Watts.v's fifty-five lines verbatim and
    in order, six of them targets (Functor/Representable/Additive.v,
    Instance/Mod/WellPowered.v, Instance/Mod/Colimit.v,
    Instance/Mod/HomTensor.v, Instance/Mod/Cogenerator.v and, last,
    Instance/Mod/Watts/Unconditional.v); then the lines each other target
    adds, file by file in _CoqProject order, the target modules aside:
    Additive.v none, WellPowered.v nine, Colimit.v eleven, HomTensor.v
    one, Cogenerator.v six (among them its three stdlib lines, which it
    places before the library's own and this file after them) and
    Unconditional.v two; then the one target Watts.v's list does not
    carry, Instance/Mod/Watts.v itself.  Eighty-five lines, with no
    addition.  Two short names resolve
    differently from some target's.  Theory/Subobject.v comes after
    Adjunction/SAFT.v here, so [sub_mono] is the subobject's and not
    [SubobjectIndex]'s field, and the commands write [Subobject.sub_mono]
    as Instance/Mod/WellPowered.v's import comment advises.
    Instance/Mod/Spanning.v, one of WellPowered.v's additions, comes after
    Colimit.v, so its inductive [MGen] takes the short name, and the guard
    block writes Colimit.v's constant [Colimit.MGen].  A shorter import
    list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and each of the seventy-two
    definitions and examples of this file that is not a refutation,
    wrapped in one in a copy of this WHOLE file, stops the build at that
    command with the report that the guarded command had been accepted
    (seventy-two of seventy-two, by a script over the copies); [Print
    Assumptions] of each of the seventy-two, by its fully qualified name,
    reports "Closed under the global context".  Every negative other than
    that instrument is a [Definition] or an [Example], never a [Check], so
    that an open evar or a missing instance cannot satisfy it.  Each
    negative was stripped of its refutation keyword in a copy of this
    WHOLE file, one at a time, compiled, and its error read; each of the
    thirty-five copies stops inside the stripped command.  The kind
    recorded is the kind of that error, and each negative has positive
    controls beside it; every identifier a negative uses, its own name,
    the universes its binder names and N10's [match] and [ex_intro] aside,
    is used by some positive control of this file (by a script over the
    identifiers of the commands).  In one further copy of this WHOLE file
    per negative, the negative was followed by a BINDER INSTRUMENT, the
    same universe binder, arguments and return type with a trivial body
    (a hypothesis of the return type, or [Datatypes.unit] where the
    command states none): thirty-three of the thirty-four are accepted,
    and N5's is refused with N5's own text, so every negative but N5 is
    refused by its body.  Every UNIVERSE negative is a top-level
    definition whose universes are declared in its own binder or left to
    inference, never a [Section]'s.  Quotations are Rocq 9.1.1's under
    this file's import list, with the error's environment block left out;
    Rocq prints the "cannot unify" parenthetical with the short names in
    scope, and a universe the stripped copy names after itself and a
    serial number is written <1>, <2>, ..., numbered afresh in each
    quotation in order of first appearance.  The file also compiles
    on Coq 8.19.2 and 8.20.1, against copies of prebuilt trees of this
    library for those versions: a dependency closure of 250 files,
    containing the seven targets and this file's 231 (by the
    dependency file of the build), with each source that differs from
    this tree's replaced by this tree's and [coq_makefile] rebuilding
    what depends on it.  Four files were compiled on each, this file,
    Instance/Mod/Cogenerator.v, Instance/Mod/Watts.v and
    Instance/Mod/Watts/Unconditional.v, the last three for header edits
    alone; make returned 0 on both, and [make -n] then lists nothing to
    build.  The stripped copies were compiled there as well.  Every one
    is refused on both inside the stripped command,
    at the line and character range of its Rocq 9.1.1 refusal except N12
    and N13, which both versions report over the whole command.  Under
    8.20.1 every error is the Rocq 9.1.1 one up to the serial numbers
    (compared by a script over the copies).  Under 8.19.2 eighteen are
    (the instrument, N1, N2, N9, N10, N12, N13, N16, N21-N23, N25-N27 and
    N31-N34); N3-N8, N11, N14, N15, N17-N19, N24, N28 and N29 print as
    type mismatches with no universe-inconsistency clause, so that N28
    and N29 print as N7 and N19 do, and N20 and N30 print in place of
    their clauses one "cannot unify" of two cone types that differ in the
    [Ab] universe, m against o.

    KINDS.  Thirty-five refutations, counted as the lines that open with
    the refutation keyword: NAME-ABSENCE (the instrument), INSTANCE (N1),
    CONVERSION (N2, N16, N21-N23, N26, N27, N31-N34), TYPING (N10), BINDER
    (N5, N12, N13) and UNIVERSE (N3, N4, N6-N9, N11, N14, N15, N17-N20,
    N24, N25, N28-N30): one, one, eleven, one, three and eighteen.  N9's refusal is a sort's ("Type" is not a subtype
    of "Prop") and is counted UNIVERSE.  BINDER means refused for the
    command's own binder or argument list: N5 whatever its body, N12 and
    N13 because a closed universe list does not name universes their
    bodies create.  The kind follows the error's text, not its cause, and
    three groups read differently by cause.  N21, N22 and N31-N34 differ
    from their controls in one universe alone, and are universe-driven
    although their errors are "cannot unify"s.  N9 and N10 are one
    barrier, the elimination of a [Prop] into [Type], seen through two
    errors.  And BINDER for N12 and N13 means the closed universe list, not
    the argument list: their binder instruments are accepted, and the
    universes each error reports unbound are located at subterms of its
    body.

    LABELS.  The pins carry the N-numbers of this file; #454's builders
    and reviews measured them under other names, recorded here so that
    the target headers can cite either.  The scratch probes [WPin],
    [WRef] and [WCtl] (Instance/Mod/WellPowered.v) are N6, N8 and the
    control [p454_cwp_pin_U]; [WP3] and [WP5] are N12 and N13;
    [CRef] and [CCtl] (Instance/Mod/Colimit.v) are N14 and
    [p454_sols_at_set]; [ALP] and [ALPctl] (Functor/Representable/
    Additive.v) are N1 and [p454_lp_explicit].  The Watts.v measurements
    M1, M2, M2c, M3 and M6 are N16, N17, [p454_sets_apart_free],
    N19 and [p454_ex3_twice]; M4 is N31 and M5 is N33-N34,
    both in the header's composite form, and they are restated as well at
    a first factor as N20 and at the constant as N21-N22.  The
    Unconditional.v review's [P1] and [P2] are N24 and N25, and
    its [ctl], [ctl2] and [rmod_at_set] the controls [p454_unc_Z_ccc],
    [p454_unc_Z_apart] and [p454_rmod_at_set].  The labels are not
    constants.

    ** Functor/Representable/Additive.v

    N1 (INSTANCE).  [LocallyPropositional_op] is a [Definition], not an
    [Instance], so at T : (RMod R)^op ⟶ Ab resolution does not supply the
    local propositionality [watt_ab_iso] asks for:
      ... More precisely: - ?LP: Cannot infer the implicit parameter LP of
      watt_ab_iso whose type is "LocallyPropositional (RMod R)^op" (no type
      class instance found) ...,
    the head of the message, which reprints the unannotated term, elided.
    The same term with [LocallyPropositional_op _] passed is accepted
    ([p454_lp_explicit]).  The controls [p454_lp_op_at],
    [p454_homab_fmap_at], [p454_cohomab_fmap_at], [p454_watt_to_at] and
    [p454_watt_from_at] restate the file's [eq_refl] readbacks: the
    opposite's local propositionality, the arrow actions of [HomAb] and
    [CoHomAb], and the two components of [watt_ab_iso], which ARE the
    representation's.  [p454_homab_cont] and [p454_cohomab_cont] restate
    [HomAb_continuous] and [CoHomAb_continuous], defined once, in this
    target, and consumed by both Watts files, and
    [p454_cohomab_cont_is_op] that the second IS the first at the
    opposite category, at [eq_refl].

    ** Instance/Mod/HomTensor.v

    N2 (CONVERSION).  hom_Z(R, G) read through Exercise 2(a) and through
    the coextension agree in their groups and their actions at [eq_refl]
    ([p454_homzl_group], [p454_homzl_act], restating [homzl_ring_group] and
    [homzl_ring_act]) and are isomorphic by identity maps
    ([p454_homzl_coext_iso]); the two records are not convertible:
      The term "eq_refl" has type "HomZL (Ring_RMod (Ring_op R)) G = HomZL
      (Ring_RMod (Ring_op R)) G" while it is expected to have type "HomZL
      (Ring_RMod (Ring_op R)) G = CoextObj R G" (cannot unify "HomZL
      (Ring_RMod (Ring_op R)) G" and "CoextObj R G").

    N3 (UNIVERSE).  [tensor_homZ_adjunction] keeps the ring's three
    universes strictly apart ([p454_tensor_homZ_apart], at [rc < ra] and
    [rp < ra]).  [homzl_ring_adjunction], whose [About] reads "ra = rc"
    and "ra = rp", is formed at [RingObject@{r r r}]
    ([p454_homzl_ring_adj]); N3, at [rc < ra]:
      The term "R" has type "RingObject@{ra rc rp}" while it is expected to
      have type "RingObject@{<1> <1> <1>}" (universe inconsistency: Cannot
      enforce rc = ra because rc < ra).

    ** Instance/Mod/Cogenerator.v

    N4 (UNIVERSE).  [RMod_Cogenerator_large] is a cogenerator indexed at
    RMod's object universe ([p454_large_cog], [Cogenerator@{o o c}]), and
    [cogen_prod] at [RMod_Complete R] takes a cogenerator indexed at the
    carrier ([p454_small_cog_prod], the family a hypothesis;
    [p454_qz_cogen_prod], restating [QZ_cogen_prod]).  N4, the large one
    there:
      The term "RMod_Cogenerator_large R" has type "Cogenerator@{<1> <1> c}
      (RMod@{<1> <2> a p c} R)" while it is expected to have type
      "Cogenerator@{c <3> c} (RMod@{<3> <4> a p c} R)" (universe
      inconsistency: Cannot enforce c = <3> because c < <3>).

    N5 (BINDER).  The file's header records that the bare type [F ⊣ U]
    over [Category@{co hc hc}] and [Category@{do hd hd}] with [hc < hd]
    declared is refused, at [F : D ⟶ C], before the record is reached.
    N5 is refused in its argument list, there, whatever its body:
      The term "C" has type "Category@{co hc hc}" while it is expected to
      have type "Category@{<1> <2> <3>}" (universe inconsistency: Cannot
      enforce hc = <2> because hc < hd <= <2>).
    Theory/Functor.v's [Functor@{o1 h1 p1 o2 h2 p2}] carries [h1 <= h2]
    ([About Functor]), so the two functors of a pair already force the two
    hom universes equal, before the record is reached: measured in a
    scratch file carrying this file's import list, [F : D ⟶ C] and
    [U : C ⟶ D] as arguments of a definition with a trivial body read back
    "hc = hd", and [F : D ⟶ C] alone "hd <= hc".  The record's own [About]
    carries the equation too, and the header gives the same cause.
    [p454_adj_one_hom] is the type over one hom universe.

    CONTROLS of the rest of the file: [p454_ra_cog_obj] and
    [p454_qz_member] restate the transferred cogenerator's member at
    [eq_refl]; [p454_qz_dne], [p454_qz_wlem], [p454_stable_dne],
    [p454_stable_dne_Z], [p454_coext_dne] and [p454_coext_wlem] restate the
    six metatheorems at their stated types: the premises of Exercise 2(b),
    and its conclusion at R = ℤ, cost double-negation elimination or the
    informative weak excluded middle.  Nothing refutes them, and nothing
    here inhabits them.

    ** Instance/Mod/WellPowered.v

    N6, N8 (UNIVERSE).  The pin is [WellPowered@{o c c o x}] and
    [CoWellPowered@{o c c o x}], the index at the carrier c.  Under [U :
    Untruncate] both are met ([p454_wp_pin_U], [p454_cwp_pin_U]); one
    universe up both hold with nothing assumed ([p454_wp_up] at [c < w];
    [p454_cwp_up] at [c < w] and [a <= w], and [p454_cwp_up_ccc] at
    [RingObject@{c c c}] with [c < w] alone).  Offered at the pin without
    [U], (1) is refused, N6,
      The term "RMod_WellPoweredAt_up W" has type "WellPoweredAt@{<1> o o c
      x} W" while it is expected to have type "WellPoweredAt@{c o o c x} W"
      (universe inconsistency: Cannot enforce <1> = c because c < <1>),
    and so is (5), N8,
      The term "RMod_CoWellPoweredAt_up W" has type "WellPoweredAt@{<1> <2>
      <2> c <3>} W" while it is expected to have type "WellPoweredAt@{c o o
      c x} W" (universe inconsistency: Cannot enforce <1> = c because c <
      <1>).

    N7, N28 (UNIVERSE).  (1)'s fifth slot is x ([p454_wp_up]); the
    header's readback, that naming it w adds "x = w", is pinned on both
    sides, N7 at [x < w]:
      The term "RMod_WellPoweredAt_up W" has type "WellPoweredAt@{<1> o o c
      x} W" while it is expected to have type "WellPoweredAt@{w o o c w} W"
      (universe inconsistency: Cannot enforce x = w because x < w),
    and N28 at [w < x], with the same text but its clause, "Cannot enforce
    x = w because w < x".

    N9 (UNIVERSE), N10 (TYPING).  Where [U] is spent.  [pim_fn]'s body is
    accepted with [U] ([p454_pim_fn_U]); N9, the truncation applied to the
    identity instead:
      The term "x" has type "∃ a : sub_dom m, sub_mono m a ≈ `1 (p)" while
      it is expected to have type "?Q" (unable to find a well-typed
      instantiation for "?Q": cannot ensure that "Type" is a subtype of
      "Prop").
    [pre_fn]'s body is accepted with [U] ([p454_pre_fn_U]); N10, a [match]
    on the [ex] that [rmod_epic_surjective] returns:
      Incorrect elimination of "rmod_epic_surjective (quot_epi u)
      (quot_is_epic u) q" in the inductive type "ex": the return type has
      sort "Type" while it should be SProp or Prop. ...,
    the rest of the message elided.

    N11 (UNIVERSE).  The ring as a module over itself is formed at
    [RingObject@{c c c}] ([p454_ring_obj_ccc]); at [c < a]:
      The term "Ring_RMod R" has type "RModObject R" while it is expected
      to have type "obj[RMod R]" (universe inconsistency: Cannot enforce
      a = c because c < a).
    The header measures the same fact under a CLOSED binder, "Universe
    constraints are not implied by the ones declared: ... a = c a = p",
    whose list also names stdlib bounds that a binder cannot declare, so
    that form is refused at [RingObject@{c c c}] too (the header says so)
    and is not restated; N11's extensible binder is the discriminating
    form.

    N12, N13 (BINDER).  A closed universe list works for (2)'s record
    ([p454_wp_record_closed], exactly the five named universes).  For
    (3)'s record, formed under an extensible one ([p454_cwp_record]), N12
    is refused,
      Universes <1> (...) <2> (...) are unbound.,
    the two located at [pquot] and at [cwp_to_from] in its body; and for
    (5), with [RModPropSurjective] unfolded into its [Prop] and built as
    one term, formed under an extensible list ([p454_cwp_up_unfolded]),
    N13 is refused with the same text, the two located at
    [rmod_prop_surjective_epic] and at [rmod_epic_surjective].

    ** Instance/Mod/Colimit.v

    N14 (UNIVERSE).  The solution set at a [Set] carrier is formed
    ([p454_sols_at_set]), and the colimit above [Set]
    ([p454_colim_above_set]); the colimit at a [Set] carrier:
      The term "R" has type "RingObject@{ga Set gp}" while it is expected
      to have type "RingObject@{<1> <2> <3>}" (universe inconsistency:
      Cannot enforce Set = <2> because Set < <2>).
    The header measured it under [Monomorphic] universes in a section;
    N14 restates it with a polymorphic binder.

    N15 (UNIVERSE).  The adjoint functor theorem's initial module and
    Instance/Mod.v's zero module are each formed alone
    ([p454_initial_via_gaft]; [p454_zero_module], at a [Set] carrier), and
    [initial_unique] between two copies of the first
    ([p454_initial_unique_gaft]); between the two, at an unannotated ring:
      The term "R" has type "RingObject@{<1> <2> <3>}" while it is expected
      to have type "RingObject@{<4> Set <4>}" (universe inconsistency:
      Cannot enforce Set = <2> because Set < <2>).

    ** Instance/Mod/Watts.v

    N16 (CONVERSION).  Exercise 3's witness at the forgetful functor has
    the ring as its representing object up to isomorphism
    ([p454_ex3_forget_obj], restating [watts_ex3_forget_obj]), not by
    conversion:
      The term "eq_refl" has type "projT1 (watts_ex3_forget R G U) = projT1
      (watts_ex3_forget R G U)" while it is expected to have type "projT1
      (watts_ex3_forget R G U) = Ring_RMod R" (cannot unify "projT1
      (watts_ex3_forget R G U)" and "Ring_RMod R").
    [watt_at_forget], with no hypothesis, names [Ring_RMod R] in its
    statement ([p454_watt_at_forget]).

    N17, N18 (UNIVERSE).  The text form's [RingObject@{c c c}].
    [watts_theorem_sets]'s body is accepted at [RingObject@{c c c}]
    ([p454_sets_ccc]) and with the ring's universes named apart and no
    constraint among them ([p454_sets_apart_free], its [About] reading
    "a = c" and "a = p"), and Exercise 3's form keeps them strictly apart
    ([p454_ex3_apart], at [c < a] and [p < a]).  N17, the body at [c < a]:
      The term "R" has type "RingObject@{a c p}" while it is expected to
      have type "RingObject@{<1> <1> <1>}" (universe inconsistency: Cannot
      enforce c = a because c < a).
    N18 peels it to [RModop_Cogenerator], formed at [RingObject@{c c c}]
    ([p454_rmodop_cog_ccc]) and refused at [c < a] with the same text; N11
    peels it once more, to [Ring_RMod].

    N19, N29 (UNIVERSE).  The Sets level of the text form is the
    continuity hypothesis's auxiliary universe pa ([p454_sets_ccc]); with
    a separate s for [Ab_Forget] and [pa < s], N19:
      The term "continuous_Set_functor_representable (Ab_Forget ◯ T)
      (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
      (Continuous_PreservesImageLimit (continuous_compose
      (PreservesImageLimit_Continuous contT) Ab_Forget_creates_continuous))
      (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U)" has type
      "Representable@{<1> <2> pa o c} (Ab_Forget@{a pa c} ◯ T)" while it is
      expected to have type "Representable@{ra rt s o c} (Ab_Forget@{a s c}
      ◯ T)" (universe inconsistency: Cannot enforce pa = s because pa < s).
    N29, at [s < pa], is refused with the same text but its clause,
    "Cannot enforce pa = s because s < pa".

    N20, N30 (UNIVERSE).  The witness's intermediate [Ab] sits at RMod's
    object universe o.  The header measures that on the continuity of the
    whole composite [HomAbForget] (N31 and N32 below); N20 restates it at
    the composite's first factor, the opposite of [RMod_Forget_Ab R],
    continuous as a right adjoint by [coex_adjunction]: accepted with that
    [Ab] at o ([p454_forget_op_cont]), and at [o < m]
      The term "right_adjoint_Continuous (coex_adjunction R)^op" has type
      "ContinuousFunctor@{<1> <2> <3> <4> <5> <6> c o o <7>}
      (RMod_Forget_Ab@{x o o c c c} R)^op" while it is expected to have
      type "ContinuousFunctor@{<8> <9> <3> <4> <10> <6> c m o <11>}
      (RMod_Forget_Ab@{x o m c c c} R)^op" (universe inconsistency: Cannot
      enforce m = o because o < m).
    N30, at [m < o], is refused with the same text but its clause,
    "Cannot enforce m = o because m < o".

    N31, N32 (CONVERSION).  The header's own form of that measurement:
    [HomAbForget_continuous]'s body, [continuous_compose] of that first
    factor with Functor/Representable/Additive.v's [CoHomAb_continuous],
    stated for the composite with its intermediate [Ab] at its own m.  It
    is accepted at m := o ([p454_hafc_body_at_o]); at [o < m] (N31) and at
    [m < o] (N32) each is refused with
      The term "continuous_compose (right_adjoint_Continuous
      (coex_adjunction R)^op) (CoHomAb_continuous Ab_AbEnriched A)" has
      type "ContinuousFunctor@{<1> <2> <3> <4> <5> <6> c b o <7>}
      (CoHomAb@{o c b} Ab_AbEnriched@{o <8> c} A ◯ (RMod_Forget_Ab@{x o o
      c c c} R)^op)" while it is expected to have type
      "ContinuousFunctor@{<9> <10> <3> <4> <11> <6> c b o <12>}
      (CoHomAb@{m c b} Ab_AbEnriched@{m <8> c} A ◯ (RMod_Forget_Ab@{x o m
      c c c} R)^op)" (cannot unify "@padd_respects _
      (@abenriched_preadditive _ (@AbEnriched_op@{m c} Ab@{m c}
      Ab_AbEnriched@{m <8> c})) A (fobj[(RMod_Forget_Ab@{x o m c c c}
      R)^op] (fobj[K] x0))" and "@padd_respects _ (@abenriched_preadditive
      _ (@AbEnriched_op@{o c} Ab@{o c} Ab_AbEnriched@{o <8> c})) A
      (fobj[(RMod_Forget_Ab@{x o o c c c} R)^op] (fobj[K] x0))"),
    whose parenthetical the header quotes.  With m left free the same
    definition is accepted and its [About] reads "o = m" (measured in a
    scratch file with this file's import list).

    N21, N22 (CONVERSION).  [HomAbForget_continuous]'s tenth slot is x:
    named x the constant is accepted ([p454_hafc_at_x]); named k6, with
    [x < k6] (N21) or [k6 < x] (N22), each is refused with
      The term "HomAbForget_continuous R A" has type "ContinuousFunctor@{<1>
      <2> <3> <4> <5> <6> c <7> o x} (HomAbForget@{c o x <7>} R A)" while
      it is expected to have type "ContinuousFunctor@{<8> <9> <3> <4> <10>
      <6> c b o k6} (HomAbForget@{c o x b} R A)" (cannot unify
      "Cone@{<6> c c b c c} (HomAbForget@{c o x b} R A ◯ K)" and
      "Cone@{<6> c c <7> c c} (HomAbForget@{c o x <7>} R A ◯ K)").
    The parenthetical sets the [Ab] universe b against a generated one,
    the reading of the mismatch the unifier chose; each command differs
    from its control in the tenth slot alone, and with k6 left free the
    same definition is accepted and its [About] reads "x = k6" (measured
    in a scratch copy of this file).  The header quotes the refusal of the
    constant's BODY at that slot, and N33 and N34 pin that form; both
    forms are pinned.

    N33, N34 (CONVERSION).  [HomAbForget_continuous]'s body is accepted at
    the constant's own tenth slot x ([p454_hafc_body_at_x]); at k6, with
    [x < k6] (N33) or [k6 < x] (N34), each is refused with the header's
    text:
      The term "continuous_compose (right_adjoint_Continuous
      (coex_adjunction R)^op) (CoHomAb_continuous Ab_AbEnriched A)" has
      type "ContinuousFunctor (CoHomAb Ab_AbEnriched A ◯ (RMod_Forget_Ab
      R)^op)" while it is expected to have type "ContinuousFunctor
      (HomAbForget R A)" (cannot unify "Functor.Compose_obligation_1 J
      (RMod R)^op Ab (HomAbForget R A) K" and "Functor.Compose_obligation_1
      J (RMod R)^op Ab (CoHomAb Ab_AbEnriched A ◯ (RMod_Forget_Ab R)^op)
      K").

    N23 (CONVERSION).  Mac Lane's last step: the representing object of
    the text form is F ℤ up to isomorphism ([p454_watts_Fz], restating
    [watts_theorem_Fz]); at [eq_refl]:
      The term "eq_refl" has type "projT1 (watts_theorem T AF contT U) =
      projT1 (watts_theorem T AF contT U)" while it is expected to have
      type "projT1 (watts_theorem T AF contT U) = fobj[projT1
      (watts_theorem_adjoint T contT U)] (fobj[FreeAb] SetsOne)" (cannot
      unify "projT1 (watts_theorem T AF contT U)" and "fobj[projT1
      (watts_theorem_adjoint T contT U)] (fobj[FreeAb] SetsOne)").
    Both sides are stuck at a [Qed]: by [eval hnf] each reduces to an
    object [fobj[projT1 P] X] whose P has head Adjunction/GAFT.v's
    [GAFT], which [About] reports opaque (measured in a scratch file with
    this file's import list).  So N23 pins that the representing object
    is not that term by conversion while [GAFT] is opaque, not that the
    two objects would differ were it transparent; any right-hand side
    other than the left side's own readback would be refused alike.

    CONTROLS of the rest of the file: [p454_watts_obj] and
    [p454_ex3_qz_cog] restate [watts_theorem_obj] and
    [watts_ex3_QZ_cogenerator] at [eq_refl]; [p454_ab_hom_Z] restates
    [ab_hom_Z_iso]; [p454_ex3_twice] is the draft of [watts_ex3] that
    elaborates [watts_ex3_sets] twice, accepted with [s < x] declared, so
    the "x = s" that draft read back is not forced.  Of section 6,
    [p454_via_unconditional] restates [watts_theorem_via_unconditional],
    and [p454_via_unconditional_body] its body at [eq_refl],
    [watts_theorem_unconditional T AF (PreservesImageLimit_Continuous
    contT)], which does not mention [U]; [p454_unc_coext] and
    [p454_unc_coext_2a] restate [watts_unconditional_coext] and
    [watts_unconditional_coext_2a], the module the unconditional theorem
    returns at [HomAbForget R A] ≅ [CoextObj R A] and ≅ hom_ℤ(R, A) with
    no [Untruncate].

    ** Instance/Mod/Watts/Unconditional.v

    N24, N25 (UNIVERSE).  The theorem asks [Set < c] and nothing else.  At
    ℤ above [Set] it holds with the ring's universes collapsed
    ([p454_unc_Z_ccc]) and apart ([p454_unc_Z_apart], at [Int_Ring@{c p
    a}]); at a generic ring it holds with the three STRICTLY apart
    ([p454_unc_apart], [c < a], [p < a]), where the special adjoint
    functor theorem's route is refused (N17); and the category of
    ℤ-modules at a [Set] carrier is formed ([p454_rmod_at_set]), so the
    refusals below are the theorem's.  N24, the witness at a [Set]
    carrier:
      The term "A" has type "obj[RMod@{o x Set Set Set} Int_Ring@{Set Set
      Set}]" while it is expected to have type "obj[RMod@{<1> <2> <3> <4>
      <5>} Int_Ring@{<5> <4> <3>}]" (universe inconsistency: Cannot enforce
      Set = <3> because Set < <5> <= <3>).
    N25, the theorem itself at [RingObject@{Set Set Set}]:
      The term "T" has type "(RMod@{o x Set Set Set} R)^op ⟶ Ab@{b Set}"
      while it is expected to have type "(RMod@{<1> <2> <3> <4> <5>} ?R)^op
      ⟶ Ab@{<6> <5>}" (universe inconsistency: Cannot enforce Set = <5>
      because Set < <5>).
    [p454_unc_x_below_s] and [p454_unc_s_below_x] accept the theorem with
    RMod's second universe x and the target's s apart in both orders: the
    "x = s" the header records as removed by its three pinned auxiliary
    universes stays removed.

    N26, N27 (CONVERSION).  The file's readbacks at [eq_refl]: the covering
    map on the nose ([p454_t_at], restating [ew_t_at]; [p454_ev_g0],
    restating [ew_ev_g0]) and the representing module ([p454_unc_obj],
    restating [watts_theorem_unconditional_obj]).  Each negative compares
    the readback with another term of the right type ([p454_cop_zero],
    [p454_cop_obj]); N26, the zero of the fixed coproduct:
      The term "eq_refl" has type "ew_t K M x0 m = ew_t K M x0 m" while it
      is expected to have type "ew_t K M x0 m = cmon_zero (ew_Cop K)"
      (cannot unify "ew_t K M x0 m" and "cmon_zero (ew_Cop K)"),
    and N27, the fixed coproduct itself:
      The term "eq_refl" has type "projT1 (watts_theorem_unconditional T AF
      contT) = projT1 (watts_theorem_unconditional T AF contT)" while it is
      expected to have type "projT1 (watts_theorem_unconditional T AF
      contT) = ew_Cop (Ab_Forget ◯ T)" (cannot unify "projT1
      (watts_theorem_unconditional T AF contT)" and "ew_Cop (Ab_Forget ◯
      T)").
    The compared terms are stuck at a [Qed], measured by [eval hnf] in a
    scratch file with this file's import list.  [ew_Cop K] reduces to an
    object [fobj[projT1 P] X] whose P has head [GAFT], so N26 compares two
    elements of that object's carrier and N27's right side is that
    object; N27's left side reduces to a component of an initial object
    whose [Initial] has head Theory/WeaklyInitial.v's
    [initial_from_weakly_initial]; [About] reports both heads opaque.  So
    each refusal pins that the value is not the compared term by
    conversion while those two are opaque, not which value it is: any
    right-hand side other than the left side's own readback would be
    refused alike.

    NOT PINNED HERE.  (a) Watts.v's draft of
    [coext_representable] at a separate [Sets@{c s}], accepted with
    [x < s]: a restatement of a whole proof, left to that header.  (b)
    Colimit.v's [left_adjoint_iso] refusal over the two
    [Diagonal_Coproduct_Adjunction]s, which needs Instance/Mod/Coproduct.v,
    an import no target carries.  (c) WellPowered.v's closed-binder form
    of the ring collapse (N11 says why).  (d) Unconditional.v's measurement
    that [Set < c], deleted from a binder, is re-inferred: a readback, of
    which N24 and N25 pin the consequence.  (e) Flip censuses ([Defined]
    against [Qed]) and the closure of the targets under [Print
    Assumptions]: measurements of the build rather than of commands; the
    Makefile's print-assumptions gate is where closure is kept.

    The guard block at the end names 359 constants of the seven target
    files, so that a rename breaks this file: thirty-five of Additive.v,
    seventy-four of HomTensor.v, eighty-four of Cogenerator.v, thirty-seven
    of WellPowered.v, forty-one of Colimit.v, twenty-seven of Watts.v and
    sixty-one of Unconditional.v.  They are the [def], [prf], [rec],
    [proj], [ind], [constr] and [scheme] entries of the targets' .glob
    files with the [Build_] constructor of each [rec] (three), and not
    their ten [abbrev] entries, which are notations (seven in HomTensor.v,
    one in Cogenerator.v and two in Unconditional.v); and they are the
    names [Print Module] lists for each, the constructors inside its
    record and inductive entries counted, other than [Program]
    obligations.  Left out: the 113 [Program] obligation constants (3, 85,
    16 and 9 of Additive.v, HomTensor.v, Cogenerator.v and
    Unconditional.v, by [Print Module]), whose names are generated from
    their heads.  Under the full import list, [Locate] lists exactly one object for 358
    of the 359 names, the target's; for Colimit.v's [MGen] it lists
    Instance/Mod/Spanning.v's inductive first, and the block writes
    [Colimit.MGen]. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Functor.Representable.Additive.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Projective.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Character.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.WellPowered.
Require Import Category.Instance.Mod.Colimit.
Require Import Category.Instance.Mod.HomTensor.
Require Import Category.Instance.Mod.Cogenerator.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mod.Watts.Unconditional.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Mod.Free.
Require Import Category.Instance.Mod.TensorAFT.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Structure.Cone.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Mod.Watts.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe454_absent_name.

(** ** N1 (INSTANCE): Functor/Representable/Additive.v *)

(* CONTROL: [LocallyPropositional_op_at], restated. *)
Example p454_lp_op_at@{o h +} {C : Category@{o h h}}
  (LP : LocallyPropositional C) (x y : C) :
  @locally_prop (C^op) (LocallyPropositional_op LP) x y
    = @locally_prop C LP y x := eq_refl.

(* CONTROL: [HomAb_fmap_at] and [CoHomAb_fmap_at], restated. *)
Example p454_homab_fmap_at@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) {x y : C}
  (f : x ~{C}~> y) (g : A0 ~{C}~> x) :
  cmon_map (fmap[HomAb AC A0 : C ⟶ Ab@{a h}] f) g = f ∘ g := eq_refl.

Example p454_cohomab_fmap_at@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) {x y : C}
  (f : y ~{C}~> x) (g : x ~{C}~> A0) :
  cmon_map (fmap[CoHomAb AC A0 : C^op ⟶ Ab@{a h}] f) g = g ∘ f := eq_refl.

(* CONTROL: the two components of [watt_ab_iso] ARE the representation's
   ([watt_ab_iso_to_at] and [watt_ab_iso_from_at], restated). *)
Example p454_watt_to_at@{o h a s +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (T : C ⟶ Ab@{a h})
  (AF : @AdditiveFunctor C Ab@{a h} AC Ab_AbEnriched T)
  (Rp : Representable (Ab_Forget@{a s h} ◯ T)) (x : C)
  (f : wab_obj Rp ~{C}~> x) :
  cmon_map (transform[to (watt_ab_iso AC T AF Rp)] x) f
    = transform[to (@represented _ _ Rp)] x f := eq_refl.

Example p454_watt_from_at@{o h a s +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (T : C ⟶ Ab@{a h})
  (AF : @AdditiveFunctor C Ab@{a h} AC Ab_AbEnriched T)
  (Rp : Representable (Ab_Forget@{a s h} ◯ T)) (x : C)
  (t : carrier (cmon_setoid (T x))) :
  cmon_map (transform[from (watt_ab_iso AC T AF Rp)] x) t
    = transform[from (@represented _ _ Rp)] x t := eq_refl.

(* CONTROL: at (RMod R)^op the local propositionality passed
   explicitly. *)
Definition p454_lp_explicit (R : RingObject) (T : (RMod R)^op ⟶ Ab)
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (Rp : Representable (Ab_Forget ◯ T)) :=
  @watt_ab_iso _ (LocallyPropositional_op _)
    (AbEnriched_op (RMod_AbEnriched R)) T AF Rp.

Fail Definition p454_n1_lp_by_resolution (R : RingObject)
  (T : (RMod R)^op ⟶ Ab)
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (Rp : Representable (Ab_Forget ◯ T)) :=
  watt_ab_iso (AbEnriched_op (RMod_AbEnriched R)) T AF Rp.

(* CONTROL: [HomAb_continuous] and [CoHomAb_continuous], restated; the
   second IS the first at the opposite category. *)
Definition p454_homab_cont@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  ContinuousFunctor (HomAb AC A0 : C ⟶ Ab@{a h}) :=
  HomAb_continuous AC A0.

Definition p454_cohomab_cont@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  ContinuousFunctor (CoHomAb AC A0 : C^op ⟶ Ab@{a h}) :=
  CoHomAb_continuous AC A0.

Example p454_cohomab_cont_is_op@{o h a +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (AC : AbEnriched C) (A0 : C) :
  (CoHomAb_continuous AC A0
     : ContinuousFunctor (CoHomAb AC A0 : C^op ⟶ Ab@{a h}))
    = @HomAb_continuous (C^op) (LocallyPropositional_op LP)
        (AbEnriched_op AC) A0 := eq_refl.

(** ** N2, N3 (CONVERSION, UNIVERSE): Instance/Mod/HomTensor.v *)

(* CONTROL: [homzl_ring_group] and [homzl_ring_act], restated. *)
Example p454_homzl_group@{ra +} (R : RingObject@{ra ra ra}) (G : AbObject) :
  rm_ab (HomZL (Ring_RMod (Ring_op R)) G) = rm_ab (CoextObj R G) :=
  eq_refl.

Example p454_homzl_act@{ra +} (R : RingObject@{ra ra ra}) (G : AbObject)
  r f s :
  cmon_map (rm_smul (HomZL (Ring_RMod (Ring_op R)) G) r f) s
    = cmon_map (rm_smul (CoextObj R G) r f) s := eq_refl.

(* CONTROL: the identity-map isomorphism [homzl_coext_iso]. *)
Definition p454_homzl_coext_iso@{r +} (R : RingObject@{r r r})
  (G : AbObject@{r r r}) :
  HomZL (Ring_RMod (Ring_op R)) G ≅[RMod R] CoextObj R G :=
  homzl_coext_iso G.

Fail Example p454_n2_homzl_is_coext@{ra +} (R : RingObject@{ra ra ra})
  (G : AbObject) :
  HomZL (Ring_RMod (Ring_op R)) G = CoextObj R G := eq_refl.

(* CONTROL: the first leg keeps the ring's three universes apart. *)
Definition p454_tensor_homZ_apart@{ra rc rp +| rc < ra, rp < ra +}
  {R : RingObject@{ra rc rp}} (B : RModObject (Ring_op R)) :=
  tensor_homZ_adjunction B.

(* CONTROL: [homzl_ring_adjunction] at [RingObject@{r r r}]. *)
Definition p454_homzl_ring_adj@{r +} {R : RingObject@{r r r}} :=
  @homzl_ring_adjunction R.

Fail Definition p454_n3_homzl_ring_apart@{ra rc rp +| rc < ra, rp < ra +}
  {R : RingObject@{ra rc rp}} :=
  @homzl_ring_adjunction R.

(** ** N4, N5 (UNIVERSE, BINDER): Instance/Mod/Cogenerator.v *)

(* CONTROL: [RMod_Cogenerator_large] is a cogenerator, indexed at the
   object universe. *)
Definition p454_large_cog@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) : Cogenerator@{o o c} (RMod@{o x a p c} R) :=
  RMod_Cogenerator_large R.

(* CONTROL: [cogen_prod] at [RMod_Complete R] takes a cogenerator indexed
   at the carrier universe. *)
Definition p454_small_cog_prod@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) (G : Cogenerator@{c o c} (RMod@{o x a p c} R)) :
  RMod@{o x a p c} R :=
  cogen_prod (RMod_Complete R) G.

(* CONTROL: [QZ_cogen_prod], restated. *)
Definition p454_qz_cogen_prod@{r a +} (R : RingObject@{r r r})
  (HC : QZ_family_cogenerates@{a r r _ _}) : RMod R :=
  cogen_prod (RMod_Complete R) (coext_cogenerator R (QZ_Cogenerator HC)).

Fail Definition p454_n4_large_cog_prod@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  (R : RingObject@{a c p}) : RMod@{o x a p c} R :=
  cogen_prod (RMod_Complete R) (RMod_Cogenerator_large R).

(* CONTROL: an adjunction whose two categories share their hom
   universe. *)
Definition p454_adj_one_hom@{co do h +}
  (C : Category@{co h h}) (D : Category@{do h h})
  (F : D ⟶ C) (U : C ⟶ D) : Type :=
  F ⊣ U.

Fail Definition p454_n5_adj_two_homs@{co hc do hd +| hc < hd +}
  (C : Category@{co hc hc}) (D : Category@{do hd hd})
  (F : D ⟶ C) (U : C ⟶ D) : Type :=
  F ⊣ U.

(* CONTROL: the transferred cogenerator's member at [eq_refl]
   ([right_adjoint_cogenerator_obj] and [QZ_injective_cogenerator_member],
   restated). *)
Example p454_ra_cog_obj@{co do h c +}
  {C : Category@{co h h}} {D : Category@{do h h}} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (HF : Faithful F) (G : Cogenerator@{c co h} C)
  (j : cog_index G) :
  cog_obj (right_adjoint_cogenerator A HF G) j = fobj[U] (cog_obj G j) :=
  eq_refl.

Example p454_qz_member@{r a c +} (R : RingObject@{r r r})
  (HI : @Injective Ab@{a r} QZ) (HC : QZ_family_cogenerates@{a r c _ _})
  (u : poly_unit@{c}) :
  cog_obj (snd (QZ_injective_cogenerator R HI HC)) u = CoextObj R QZ :=
  eq_refl.

(* CONTROL: the metatheorems at their stated types. *)
Definition p454_qz_dne@{a h c +} (HC : QZ_family_cogenerates@{a h c _ _}) :
  ∀ P : Prop, ~~P → P :=
  QZ_cogenerates_Ab_DNE HC.

Definition p454_qz_wlem@{a h +} (HI : @Injective Ab@{a h} QZ) :
  ∀ P : Prop, (~ P) + (~~ P) :=
  QZ_injective_WLEM HI.

Definition p454_stable_dne@{c a h +} (G : Cogenerator@{c a h} Ab@{a h})
  (stable : ∀ j (a b : carrier (cmon_setoid (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  cogenerator_stable_DNE G stable.

Definition p454_stable_dne_Z@{c m h +}
  (G : Cogenerator@{c m h} (RMod Int_Ring))
  (stable : ∀ j (a b : carrier (cmon_setoid (rm_ab (cog_obj G j)))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  cogenerator_stable_DNE_Z G stable.

Definition p454_coext_dne@{r c +}
  (HC : ∀ (x y : RMod Int_Ring@{r r r}) (f g : x ~{RMod Int_Ring}~> y),
          (∀ (u : poly_unit@{c})
             (k : y ~{RMod Int_Ring}~> CoextObj Int_Ring@{r r r} QZ),
             k ∘ f ≈ k ∘ g) → f ≈ g) :
  ∀ P : Prop, ~~P → P :=
  coext_QZ_cogenerates_DNE HC.

Definition p454_coext_wlem@{r +}
  (HI : @Injective (RMod Int_Ring) (CoextObj Int_Ring@{r r r} QZ)) :
  ∀ P : Prop, (~ P) + (~~ P) :=
  coext_QZ_injective_WLEM HI.

(** ** N6-N13, N28 (UNIVERSE, TYPING, BINDER): Instance/Mod/WellPowered.v *)

(* CONTROL: (2) at the pin, under [U]. *)
Definition p454_wp_pin_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c}) :
  WellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_WellPoweredAt_untruncate U W.

(* CONTROL: (1) one universe up, with nothing assumed; its fifth slot
   is x. *)
Definition p454_wp_up@{a c p o x w +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o, c < w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  WellPoweredAt@{w o o c x} W :=
  RMod_WellPoweredAt_up W.

Fail Definition p454_n6_wp_up_at_pin@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} :
  WellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_WellPoweredAt_up W.

Fail Definition p454_n7_wp_up_fifth_slot@{a c p o x w +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o, c < w, x < w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  WellPoweredAt@{w o o c w} W :=
  RMod_WellPoweredAt_up W.

Fail Definition p454_n28_wp_up_fifth_slot_below@{a c p o x w +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o, c < w, w < x +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  WellPoweredAt@{w o o c w} W :=
  RMod_WellPoweredAt_up W.

(* CONTROL: (3) at the pin, under [U]. *)
Definition p454_cwp_pin_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c}) :
  CoWellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_CoWellPoweredAt_untruncate U W.

(* CONTROL: (5) one universe up, with nothing assumed, and at
   [RingObject@{c c c}] with [c < w] alone. *)
Definition p454_cwp_up@{a c p o x w +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o, c < w, a <= w +}
  {R : RingObject@{a c p}} :
  ∀ W : obj[RMod@{o x a p c} R],
    @WellPoweredAt@{w o o c x} ((RMod@{o x a p c} R)^op) W :=
  RMod_CoWellPowered_up.

Definition p454_cwp_up_ccc@{c o x w +| Set < o, c < o, c < x, c < w +}
  {R : RingObject@{c c c}} :
  ∀ W : obj[RMod@{o x c c c} R],
    @WellPoweredAt@{w o o c x} ((RMod@{o x c c c} R)^op) W :=
  fun W => RMod_CoWellPoweredAt_up W.

Fail Definition p454_n8_cwp_up_at_pin@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} :
  CoWellPowered@{o c c o x} (RMod@{o x a p c} R) :=
  fun W => RMod_CoWellPoweredAt_up W.

(* CONTROL: [pim_fn]'s body, restated, spending [U]. *)
Definition p454_pim_fn_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  {W : obj[RMod@{o x a p c} R]} (m : @SubObj (RMod@{o x a p c} R) W)
  (p : smod_carrier (psm_sub (pimage (Subobject.sub_mono m)))) :
  smod_carrier (subobj_smod m) :=
  existT (fun b => smod_mem (subobj_smod m) b) (`1 p) (U _ (`2 p)).

Fail Definition p454_n9_pim_fn_no_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}}
  {W : obj[RMod@{o x a p c} R]} (m : @SubObj (RMod@{o x a p c} R) W)
  (p : smod_carrier (psm_sub (pimage (Subobject.sub_mono m)))) :
  smod_carrier (subobj_smod m) :=
  existT (fun b => smod_mem (subobj_smod m) b) (`1 p) ((`2 p) _ (fun x => x)).

(* CONTROL: [pre_fn]'s body, restated, spending [U]. *)
Definition p454_pre_fn_U@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  {W : obj[RMod@{o x a p c} R]} (u : @QuotObj (RMod@{o x a p c} R) W)
  (q : carrier (cmon_setoid (quot_cod u))) : carrier (cmon_setoid W) :=
  `1 (U _ (squash_of_ex
             (rmod_epic_surjective (quot_epi u) (quot_is_epic u) q))).

Fail Definition p454_n10_pre_fn_match@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}}
  {W : obj[RMod@{o x a p c} R]} (u : @QuotObj (RMod@{o x a p c} R) W)
  (q : carrier (cmon_setoid (quot_cod u))) : carrier (cmon_setoid W) :=
  match rmod_epic_surjective (quot_epi u) (quot_is_epic u) q with
  | ex_intro _ a _ => a
  end.

(* CONTROL: the ring as a module over itself at [RingObject@{c c c}]. *)
Definition p454_ring_obj_ccc@{c o x +| Set < o, c < o, c < x +}
  (R : RingObject@{c c c}) : obj[RMod@{o x c c c} R] :=
  Ring_RMod R.

Fail Definition p454_n11_ring_obj_apart@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c < a, a <= o +}
  (R : RingObject@{a c p}) : obj[RMod@{o x a p c} R] :=
  Ring_RMod R.

(* CONTROL: (2)'s record under a CLOSED universe list: its universes
   are exactly the five named. *)
Definition p454_wp_record_closed@{a c p o x |
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  (W : obj[RMod@{o x a p c} R]) : WellPoweredAt@{c o o c x} W :=
  {| wp_index   := PSubmodule W;
     wp_to      := fun P => smod_subobj (psm_sub P);
     wp_from    := fun m => pimage (Subobject.sub_mono m);
     wp_to_from := pim_to_from U |}.

(* CONTROL: (3)'s record under an extensible universe list. *)
Definition p454_cwp_record@{a c p o x +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{c o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index   := PSubmodule W;
     wp_to      := pquot;
     wp_from    := fun u => pker (quot_epi u);
     wp_to_from := cwp_to_from U |}.

Fail Definition p454_n12_cwp_record_closed@{a c p o x |
    Set < c, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} (U : Untruncate@{c})
  (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{c o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index   := PSubmodule W;
     wp_to      := pquot;
     wp_from    := fun u => pker (quot_epi u);
     wp_to_from := cwp_to_from U |}.

(* CONTROL: (5)'s construction with [RModPropSurjective] unfolded into
   its [Prop], as one term, under an extensible universe list. *)
Definition p454_cwp_up_unfolded@{a c p o x w +| c < w, a <= w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{w o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index := { Q : RModObject@{c a c c c a c p} R
                 & { e : W ~{RMod@{o x a p c} R}~> Q &
                     ∀ b : carrier (cmon_setoid Q),
                       (exists a0 : carrier (cmon_setoid W),
                          @pequiv _ _ (cmon_prop Q)
                            (cmon_map (rm_hom e) a0) b)%type } };
     wp_to := fun i => @mk_quot (RMod@{o x a p c} R) W (`1 i) (`1 (`2 i))
                         (rmod_prop_surjective_epic _ (`2 (`2 i)));
     wp_from := fun u => existT _ (quot_cod u)
                  (existT _ (quot_epi u)
                     (rmod_epic_surjective _ (quot_is_epic u)));
     wp_to_from := ltac:(intro u; exists iso_id; simpl; cat) |}.

Fail Definition p454_n13_cwp_up_closed@{a c p o x w | c < w, a <= w +}
  {R : RingObject@{a c p}} (W : obj[RMod@{o x a p c} R]) :
  @WellPoweredAt@{w o o c x} ((RMod@{o x a p c} R)^op) W :=
  {| wp_index := { Q : RModObject@{c a c c c a c p} R
                 & { e : W ~{RMod@{o x a p c} R}~> Q &
                     ∀ b : carrier (cmon_setoid Q),
                       (exists a0 : carrier (cmon_setoid W),
                          @pequiv _ _ (cmon_prop Q)
                            (cmon_map (rm_hom e) a0) b)%type } };
     wp_to := fun i => @mk_quot (RMod@{o x a p c} R) W (`1 i) (`1 (`2 i))
                         (rmod_prop_surjective_epic _ (`2 (`2 i)));
     wp_from := fun u => existT _ (quot_cod u)
                  (existT _ (quot_epi u)
                     (rmod_epic_surjective _ (quot_is_epic u)));
     wp_to_from := ltac:(intro u; exists iso_id; simpl; cat) |}.

(** ** N14, N15 (UNIVERSE): Instance/Mod/Colimit.v *)

(* CONTROL: the solution set at a [Set] carrier. *)
Definition p454_sols_at_set@{go gx ga gp +|
    Set < go, Set < gx, gp <= ga, ga <= go +}
  (R : RingObject@{ga Set gp}) (J : Category@{Set Set Set})
  (D : J ⟶ RMod@{go gx ga gp Set} R) :=
  @Diagonal_RMod_solution_set R J D.

(* CONTROL: the colimit above [Set]. *)
Definition p454_colim_above_set@{a c p o x jo +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, jo <= c +}
  (R : RingObject@{a c p}) (J : Category@{jo c c}) :=
  RMod_colim_via_GAFT R J.

Fail Definition p454_n14_colim_at_set@{go gx ga gp +|
    Set < go, Set < gx, gp <= ga, ga <= go +}
  (R : RingObject@{ga Set gp}) (J : Category@{Set Set Set}) :=
  RMod_colim_via_GAFT R J.

(* CONTROL: each initial object alone, the adjoint functor theorem's and
   Instance/Mod.v's zero module, the latter at a [Set] carrier. *)
Definition p454_initial_via_gaft (R : RingObject) :=
  RMod_Initial_via_GAFT R.

Definition p454_zero_module@{a +} (R : RingObject@{a Set a}) :=
  RMod_Initial R.

(* CONTROL: [initial_unique] between two copies of the adjoint functor
   theorem's initial module. *)
Definition p454_initial_unique_gaft (R : RingObject) :=
  initial_unique (RMod_Initial_via_GAFT R) (RMod_Initial_via_GAFT R).

Fail Definition p454_n15_initial_vs_zero (R : RingObject) :=
  initial_unique (RMod_Initial_via_GAFT R) (RMod_Initial R).

(** ** N16-N23, N29-N34 (CONVERSION, UNIVERSE): Instance/Mod/Watts.v *)

(* CONTROL: [watts_ex3_forget_obj], restated: the representing object is
   the ring up to isomorphism. *)
Definition p454_ex3_forget_obj@{c o x b g +} (R : RingObject@{c c c})
  (G : Cogenerator@{g o c} (RMod@{o x c c c} R)) (U : Untruncate@{c}) :
  projT1 (watts_ex3_forget R G U
           : { A : RMod@{o x c c c} R &
               @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
                 (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) })
    ≅[RMod@{o x c c c} R] Ring_RMod R :=
  watts_ex3_forget_obj R G U.

Fail Example p454_n16_ex3_forget_obj_refl@{c o x b g +}
  (R : RingObject@{c c c})
  (G : Cogenerator@{g o c} (RMod@{o x c c c} R)) (U : Untruncate@{c}) :
  projT1 (watts_ex3_forget R G U
           : { A : RMod@{o x c c c} R &
               @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
                 (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) })
    = Ring_RMod R := eq_refl.

(* CONTROL: [watt_at_forget], restated: no hypothesis, and the
   representing object [Ring_RMod R] by conversion. *)
Definition p454_watt_at_forget@{c o x b +} (R : RingObject@{c c c}) :
  @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
    (HomAb (RMod_AbEnriched R) (Ring_RMod R)) (RMod_Forget_Ab R) :=
  watt_at_forget R.

(* CONTROL: [watts_theorem_sets]'s body at [RingObject@{c c c}]. *)
Definition p454_sets_ccc@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* CONTROL: the same body with the ring's three universes named apart and
   no constraint among them. *)
Definition p454_sets_apart_free@{a c p o x b pk pa ra rt +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             ((RMod@{o x a p c} R)^op) Ab@{b c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget@{b pa c} ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* CONTROL: Exercise 3's form keeps the ring's universes strictly
   apart. *)
Definition p454_ex3_apart@{a c p o x b g pk pa ra rt +| c < a, p < a +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (AF : @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             (RMod@{o x a p c} R) Ab@{b c} T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :=
  watts_ex3 T AF contT G U.

Fail Definition p454_n17_sets_apart@{a c p o x b pk pa ra rt +| c < a +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             ((RMod@{o x a p c} R)^op) Ab@{b c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget@{b pa c} ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* CONTROL: R as a cogenerator of (RMod R)^op at [RingObject@{c c c}]. *)
Definition p454_rmodop_cog_ccc@{c o x +| Set < o, c < o, c < x +}
  (R : RingObject@{c c c}) : Cogenerator ((RMod@{o x c c c} R)^op) :=
  RModop_Cogenerator R.

Fail Definition p454_n18_rmodop_cog_apart@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c < a, a <= o +}
  (R : RingObject@{a c p}) : Cogenerator ((RMod@{o x a p c} R)^op) :=
  RModop_Cogenerator R.

Fail Definition p454_n19_sets_level_above_pa@{c o x a s pk pa ra rt +|
    pa < s +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt s o c} (Ab_Forget@{a s c} ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

Fail Definition p454_n29_sets_level_below_pa@{c o x a s pk pa ra rt +|
    s < pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt s o c} (Ab_Forget@{a s c} ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* CONTROL: the opposite of the forgetful functor is continuous, a right
   adjoint by [coex_adjunction], with its [Ab] at RMod's object
   universe. *)
Definition p454_forget_op_cont@{c o x +| Set < o, c < o, c < x +}
  (R : RingObject@{c c c}) :
  ContinuousFunctor
    (Opposite_Functor (RMod_Forget_Ab R : RMod@{o x c c c} R ⟶ Ab@{o c})) :=
  right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)).

Fail Definition p454_n20_forget_op_cont_above@{c o x m +|
    Set < o, c < o, c < x, o < m +}
  (R : RingObject@{c c c}) :
  ContinuousFunctor
    (Opposite_Functor (RMod_Forget_Ab R : RMod@{o x c c c} R ⟶ Ab@{m c})) :=
  right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)).

Fail Definition p454_n30_forget_op_cont_below@{c o x m +|
    Set < o, c < o, c < x, m < o +}
  (R : RingObject@{c c c}) :
  ContinuousFunctor
    (Opposite_Functor (RMod_Forget_Ab R : RMod@{o x c c c} R ⟶ Ab@{m c})) :=
  right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)).

(* CONTROL: [HomAbForget_continuous]'s body, the header's composite form,
   with the composite's intermediate [Ab] at RMod's object universe. *)
Definition p454_hafc_body_at_o@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  ContinuousFunctor (@CoHomAb Ab@{o c} _ Ab_AbEnriched A
                       ◯ Opposite_Functor (RMod_Forget_Ab@{x o o c c c} R)
                     : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Fail Definition p454_n31_hafc_body_above_o@{c o x m b +| o < m +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor (@CoHomAb Ab@{m c} _ Ab_AbEnriched A
                       ◯ Opposite_Functor (RMod_Forget_Ab@{x o m c c c} R)
                     : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Fail Definition p454_n32_hafc_body_below_o@{c o x m b +| m < o +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor (@CoHomAb Ab@{m c} _ Ab_AbEnriched A
                       ◯ Opposite_Functor (RMod_Forget_Ab@{x o m c c c} R)
                     : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

(* CONTROL: [HomAbForget_continuous] with its tenth slot at x. *)
Definition p454_hafc_at_x@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ x}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  HomAbForget_continuous R A.

Fail Definition p454_n21_hafc_above_x@{c o x b k6 +| x < k6 +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ k6}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  HomAbForget_continuous R A.

Fail Definition p454_n22_hafc_below_x@{c o x b k6 +| k6 < x +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ k6}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  HomAbForget_continuous R A.

(* CONTROL: [HomAbForget_continuous]'s body with its tenth slot at x. *)
Definition p454_hafc_body_at_x@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ x}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Fail Definition p454_n33_hafc_body_above_x@{c o x b k6 +| x < k6 +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ k6}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Fail Definition p454_n34_hafc_body_below_x@{c o x b k6 +| k6 < x +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor@{_ _ _ _ _ _ _ _ _ k6}
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

(* CONTROL: a draft of [watts_ex3] that elaborates [watts_ex3_sets]
   twice, accepted with [s < x] declared. *)
Definition p454_ex3_twice@{a c p o x b s g +| s < x +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (AF : @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : ContinuousFunctor T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun (RMod@{o x a p c} R) Ab@{b c})
      (HomAb (RMod_AbEnriched R) A) T }.
Proof.
  exists (wab_obj (watts_ex3_sets T (Continuous_PreservesImageLimit contT) G U
                    : Representable (Ab_Forget@{b s c} ◯ T))).
  exact (watt_ab_iso (RMod_AbEnriched R) T AF
           (watts_ex3_sets T (Continuous_PreservesImageLimit contT) G U)).
Defined.

(* CONTROL: [watts_theorem_obj] and [watts_ex3_QZ_cogenerator],
   restated. *)
Example p454_watts_obj@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    = @repr_obj _ _ (watts_theorem_sets T contT U
                      : Representable@{ra rt pa o c} (Ab_Forget ◯ T)) :=
  eq_refl.

Example p454_ex3_qz_cog@{r o x +}
  {R : RingObject@{r r r}} (HI : @Injective Ab@{o r} QZ)
  (HC : QZ_family_cogenerates) :
  snd (QZ_injective_cogenerator R HI HC)
    = coext_cogenerator R (QZ_Cogenerator HC) := eq_refl.

(* CONTROL: [watts_theorem_Fz], restated: the representing object is F ℤ
   up to isomorphism. *)
Definition p454_watts_Fz@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    ≅[RMod@{o x c c c} R]
  fobj[projT1 (watts_theorem_adjoint T contT U)] (FreeAb SetsOne) :=
  watts_theorem_Fz T AF contT U.

Fail Example p454_n23_Fz_refl@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    = fobj[projT1 (watts_theorem_adjoint T contT U)] (FreeAb SetsOne) :=
  eq_refl.

(* CONTROL: [ab_hom_Z_iso], restated. *)
Definition p454_ab_hom_Z@{a c +} :
  @Isomorphism (@Fun Ab@{a c} Ab@{a c})
    (HomAb Ab_AbEnriched (FreeAb SetsOne)) Id[Ab@{a c}] :=
  ab_hom_Z_iso.

(* CONTROL: [watts_theorem_via_unconditional], restated, and its body at
   [eq_refl], which does not mention [U]. *)
Definition p454_via_unconditional@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { A : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{a c})
      (CoHomAb (RMod_AbEnriched R) A) T } :=
  watts_theorem_via_unconditional T AF contT U.

Example p454_via_unconditional_body@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  watts_theorem_via_unconditional T AF contT U
    = watts_theorem_unconditional T AF (PreservesImageLimit_Continuous contT) :=
  eq_refl.

(* CONTROL: [watts_unconditional_coext] and its [_2a], restated: with no
   [Untruncate], the module the unconditional theorem returns at
   [HomAbForget R A] is the coextension, and hom_ℤ(R, A). *)
Definition p454_unc_coext@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] CoextObj R A :=
  watts_unconditional_coext R A.

Definition p454_unc_coext_2a@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] HomZL (Ring_RMod (Ring_op R)) A :=
  watts_unconditional_coext_2a R A.

(** ** N24-N27 (UNIVERSE, CONVERSION): Instance/Mod/Watts/Unconditional.v *)

(* CONTROL: the theorem at ℤ above [Set], the ring's universes collapsed
   and apart. *)
Definition p454_unc_Z_ccc@{c o x b +|
    Set < c, c < o, c < x, Set < b, c < b +}
  (A : RMod@{o x c c c} Int_Ring@{c c c}) :=
  watts_unconditional_at_Z A.

Definition p454_unc_Z_apart@{c p a o x b +|
    Set < c, c <= a, p <= a, a <= o, c < o, c < x, Set < b, c < b +}
  (A : RMod@{o x a p c} Int_Ring@{c p a}) :=
  watts_unconditional_at_Z A.

(* CONTROL: the category of ℤ-modules at a [Set] carrier is formed. *)
Definition p454_rmod_at_set@{o x +| Set < o, Set < x +} :=
  RMod@{o x Set Set Set} Int_Ring@{Set Set Set}.

Fail Definition p454_n24_unc_Z_at_set@{o x b +}
  (A : RMod@{o x Set Set Set} Int_Ring@{Set Set Set}) :=
  watts_unconditional_at_Z A.

(* CONTROL: the theorem with the ring's carrier above [Set] and its three
   universes strictly apart. *)
Definition p454_unc_apart@{a c p o x b s +|
    Set < c, c < o, c < x, p < a, c < a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :=
  watts_theorem_unconditional T AF contT.

Fail Definition p454_n25_unc_at_set@{o x b s +}
  (R : RingObject@{Set Set Set})
  (T : (RMod@{o x Set Set Set} R)^op ⟶ Ab@{b Set})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor T) :=
  watts_theorem_unconditional T AF contT.

(* CONTROL: RMod's second universe x and the target's s apart, in both
   orders. *)
Definition p454_unc_x_below_s@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b,
    x < s +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :=
  watts_theorem_unconditional T AF contT.

Definition p454_unc_s_below_x@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b,
    s < x +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :=
  watts_theorem_unconditional T AF contT.

(* CONTROL: [ew_ev_g0] and [ew_t_at], restated. *)
Example p454_ev_g0@{a c p o x +|
    Set < o, c < o, c < x, p <= a, c <= a, a <= o +}
  {R : RingObject@{a c p}} {M : obj[RMod@{o x a p c} R]}
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_ev@{a c p o x} m)) ew_g0 = m := eq_refl.

Example p454_t_at@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s})
  (M : obj[RMod@{o x a p c} R]) (x0 : carrier (K M))
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_t K M x0)) m
    = cmon_map (rm_hom (ew_inj K (ew_am K M x0 m))) ew_g0 := eq_refl.

(* CONTROL: the value N26 compares with is an element of the fixed
   coproduct, and the object N27 compares with is a module. *)
Definition p454_cop_zero@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s}) :
  carrier (cmon_setoid (ew_Cop K)) :=
  cmon_zero (ew_Cop K).

Definition p454_cop_obj@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c}) :
  obj[RMod@{o x a p c} R] :=
  ew_Cop (Ab_Forget@{b s c} ◯ T).

Fail Example p454_n26_t_at_zero@{a c p o x s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s +}
  {R : RingObject@{a c p}} (K : (RMod@{o x a p c} R)^op ⟶ Sets@{c s})
  (M : obj[RMod@{o x a p c} R]) (x0 : carrier (K M))
  (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (ew_t K M x0)) m = cmon_zero (ew_Cop K) := eq_refl.

(* CONTROL: [watts_theorem_unconditional_obj], restated. *)
Example p454_unc_obj@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  projT1 (watts_theorem_unconditional T AF contT)
    = wab_obj (RModop_continuous_representable (Ab_Forget@{b s c} ◯ T)
                 (continuous_compose contT Ab_Forget_creates_continuous)) :=
  eq_refl.

Fail Example p454_n27_unc_obj_is_cop@{a c p o x b s +|
    Set < c, c < o, c < x, p <= a, c <= a, a <= o, c < s, Set < b, c < b +}
  {R : RingObject@{a c p}} (T : (RMod@{o x a p c} R)^op ⟶ Ab@{b c})
  (AF : @AdditiveFunctor _ _ (AbEnriched_op (RMod_AbEnriched R))
          Ab_AbEnriched T)
  (contT : ContinuousFunctor@{_ _ _ _ _ _ _ _ _ s} T) :
  projT1 (watts_theorem_unconditional T AF contT)
    = ew_Cop (Ab_Forget@{b s c} ◯ T) :=
  eq_refl.

(** ** Guard block *)

(* Functor/Representable/Additive.v: 35 names *)
Check @LocallyPropositional_op.
Check @LocallyPropositional_op_at.
Check @HomAb_fmap.
Check @HomAb.
Check @HomAb_obj.
Check @HomAb_fmap_at.
Check @HomAb_additive.
Check @HomAb_forget_to.
Check @HomAb_forget_from.
Check @HomAb_forget_iso.
Check @HomAb_representable.
Check @CoHomAb.
Check @CoHomAb_fmap_at.
Check @wab_obj.
Check @wab_to.
Check @wab_from.
Check @wab_elem.
Check @wab_to_elem.
Check @wab_to_padd.
Check @wab_to_pzero.
Check @wab_to_from.
Check @wab_from_to.
Check @wab_to_hom.
Check @wab_from_hom.
Check @wab_to_nat.
Check @wab_from_nat.
Check @watt_ab_iso.
Check @watt_ab_iso_to_at.
Check @watt_ab_iso_from_at.
Check @watt_ab_repr.
Check @watt_ab_iso_HomAb.
Check @watt_ab_iso_HomAb_obj.
Check @watt_ab_iso_at_Ab.
Check @HomAb_continuous.
Check @CoHomAb_continuous.
(* Instance/Mod/HomTensor.v: 74 names *)
Check @hzl_group.
Check @hzl_act.
Check @hzl_act_respects.
Check @hzl_act_distr_l.
Check @hzl_act_distr_r.
Check @hzl_act_assoc.
Check @hzl_act_one.
Check @HomZL.
Check @hzl_map_ab.
Check @HomZLMap.
Check @HomZLF.
Check @tb_bal.
Check @TensorBF.
Check @ht_to_inner.
Check @ht_to_ab.
Check @ht_to.
Check @ht_bal.
Check @ht_from.
Check @ht_adj.
Check @tensor_homZ_adjunction.
Check @ht_to_at.
Check @hzr_group.
Check @hzr_act.
Check @hzr_act_respects.
Check @hzr_act_distr_l.
Check @hzr_act_distr_r.
Check @hzr_act_assoc.
Check @hzr_act_one.
Check @HomZR.
Check @hzr_map_ab.
Check @HomZRMap.
Check @HomZRF.
Check @ta_bal.
Check @TensorAF.
Check @th_to_inner.
Check @th_to_ab.
Check @th_to.
Check @th_bal.
Check @th_adj.
Check @homZ_tensor_adjunction.
Check @hom_hom_swap.
Check @hom_hom_swap_at.
Check @hom_hom_swap_iso.
Check @hom_hom_swap_iso_to.
Check @hom_hom_swap_iso_from_at.
Check @hom_hom_swap_natural.
Check @TensorBF_AFT_obj.
Check @TensorBF_AFT_fmap.
Check @TensorBF_AFT.
Check @TensorBF_AFT_iso.
Check @hom_tensor_adjunction.
Check @hom_tensor_adjunction_to_at.
Check @TensorAF_AFT_obj.
Check @TensorAF_AFT_fmap.
Check @TensorAF_AFT.
Check @TensorAF_AFT_iso.
Check @hom_tensor_adjunction_right.
Check @hom_tensor_adjunction_right_to_at.
Check @homzl_ring_group.
Check @homzl_ring_act.
Check @runit_bal.
Check @runit_to.
Check @runit_from.
Check @runit_gen.
Check @ring_unit_iso.
Check @ring_unit_iso_to_at.
Check @ring_unit_iso_from_at.
Check @ring_unit_nat.
Check @homzl_ring_adjunction.
Check @homzl_ring_adjunction_to_at.
Check @homzl_ring_adjunction_is_coex_at.
Check @homzl_coext_to.
Check @homzl_coext_from.
Check @homzl_coext_iso.
(* Instance/Mod/Cogenerator.v: 84 names *)
Check @right_adjoint_injective.
Check @right_adjoint_cogenerator.
Check @right_adjoint_cogenerator_obj.
Check @forget_ab_monic.
Check @forget_ab_faithful.
Check @coext_injective.
Check @coext_cogenerator.
Check @QZ_family_cogenerates.
Check @QZ_Cogenerator.
Check @QZ_injective_cogenerator.
Check @QZ_injective_cogenerator_member.
Check @QZ_injective_cogenerator_via_2a.
Check @QZ_injective_cogenerator_via_2a_member.
Check @ML_cogenerates.
Check @right_adjoint_ML.
Check @QZ_injective_cogenerator_ML.
Check @QZ_cogen_prod.
Check @RMod_Cogenerator_large.
Check @QZ_divisible.
Check @qz_sum_cong.
Check @q_add_mul.
Check @q_one_mul.
Check @q_zero_mul.
Check @q_succ_mul.
Check @q_neg_mul.
Check @zchar_pos.
Check @zchar_determined.
Check @q_baer_step.
Check @zchar.
Check @QZ_extends_along_mul.
Check @QZ_extends_along_mul_is_zchar.
Check @AbZMod.
Check @AbZModMap.
Check @Ab_to_ZMod.
Check @Ab_to_ZMod_group.
Check @Ab_to_ZMod_smul.
Check @Ab_to_ZMod_fmap.
Check @yp_eq.
Check @yp_equiv.
Check @yp_setoid.
Check @yp_prop.
Check @yp_plus_respects_prop.
Check @yp_plus_respects.
Check @YP.
Check @yp_zero.
Check @yp_true_false_prop.
Check @yp_true_false.
Check @bp_xor.
Check @bp_kill.
Check @bp_kill_xor.
Check @bp_eq.
Check @bp_xor_self.
Check @bp_xor_comm.
Check @bp_xor_trans.
Check @bp_equiv.
Check @bp_setoid.
Check @bp_prop.
Check @bp_plus_respects_prop.
Check @bp_eq_of_eq.
Check @bp_xor_assoc.
Check @bp_xor_zero_l.
Check @BP.
Check @bp_incl_respects_prop.
Check @bp_incl.
Check @bp_incl_injective_prop.
Check @bp_incl_monic.
Check @qz_half.
Check @qz_half_nonzero.
Check @z2_eq_bool.
Check @z2_half.
Check @cogenerator_stable_DNE.
Check @qz_stable.
Check @QZ_cogenerates_Ab_DNE.
Check @QZ_injective_WLEM.
Check @YPZ.
Check @BPZ.
Check @ypz_zero.
Check @bpz_incl.
Check @bpz_incl_monic.
Check @cogenerator_stable_DNE_Z.
Check @coext_QZ_stable.
Check @coext_QZ_cogenerates_DNE.
Check @z2_half_Z.
Check @coext_QZ_injective_WLEM.
(* Instance/Mod/WellPowered.v: 37 names *)
Check @RMod_WellPoweredAt_up.
Check @PSubmodule.
Check @Build_PSubmodule.
Check @psm_mem.
Check @psm_resp.
Check @psm_zero.
Check @psm_plus.
Check @psm_smul.
Check @psm_sub.
Check @pimage.
Check @pim_fn.
Check @tim_fn.
Check @pim_to_tim.
Check @tim_to_pim.
Check @pim_le.
Check @pim_ge.
Check @pim_to_from.
Check @RMod_WellPoweredAt_untruncate.
Check @RMod_WellPowered_untruncate.
Check @pker.
Check @pquot.
Check @squash_of_ex.
Check @pre_fn.
Check @pre_spec.
Check @rel_of_image.
Check @image_of_rel.
Check @pre_map.
Check @ev_map.
Check @pre_iso.
Check @cwp_to_from.
Check @RMod_CoWellPoweredAt_untruncate.
Check @RMod_CoWellPowered_untruncate.
Check @RMod_ring_separates.
Check @RMod_Generator.
Check @RModop_Cogenerator.
Check @RMod_CoWellPoweredAt_up.
Check @RMod_CoWellPowered_up.
(* Instance/Mod/Colimit.v: 41 names *)
Check @Colimit.MGen.
Check @mins.
Check @IsModCongruence.
Check @Build_IsModCongruence.
Check @mc_refl.
Check @mc_sym.
Check @mc_trans.
Check @mc_gen.
Check @mc_plus.
Check @mc_neg.
Check @mc_smul.
Check @IsModCoconeCong.
Check @Build_IsModCoconeCong.
Check @mcc_mod.
Check @mcc_resp.
Check @mcc_zero.
Check @mcc_plus.
Check @mcc_smul.
Check @mcc_nat.
Check @MDCongIdx.
Check @MDQ_Setoid.
Check @MDQ_smul_respects.
Check @MDQ.
Check @mdq_leg.
Check @mdq_arr.
Check @mflat.
Check @mker.
Check @mker_cocone.
Check @mker_idx.
Check @mker_med.
Check @Diagonal_RMod_solution_set.
Check @RMod_colim_via_GAFT.
Check @RMod_Cocomplete_via_GAFT.
Check @RMod_FinitelyCocomplete_via_GAFT.
Check @RMod_Cocartesian_via_GAFT.
Check @RMod_HasCoequalizers_via_GAFT.
Check @RMod_Initial_via_GAFT.
Check @RMod_initial_via_GAFT_trivial.
Check @RMod_inl_via_GAFT_retract.
Check @RMod_inl_via_GAFT_injective.
Check @RMod_coproduct_via_GAFT_nontrivial.
(* Instance/Mod/Watts.v: 27 names *)
Check @RMod_Forget_Ab_additive.
Check @watts_theorem_sets.
Check @watts_theorem_adjoint.
Check @watts_theorem.
Check @watts_theorem_obj.
Check @watts_theorem_to_at.
Check @watts_ex3_sets.
Check @watts_ex3.
Check @watts_ex3_QZ.
Check @watts_ex3_QZ_cogenerator.
Check @watts_ex3_forget.
Check @RMod_Forget_equiv.
Check @watt_at_forget.
Check @watts_ex3_forget_obj.
Check @HomAbForget.
Check @HomAbForget_additive.
Check @HomAbForget_continuous.
Check @watts_theorem_coext.
Check @coext_representable.
Check @watts_theorem_coext_obj.
Check @watts_theorem_coext_obj_2a.
Check @Ab_Forget_Id_equiv.
Check @ab_hom_Z_iso.
Check @watts_theorem_Fz.
Check @watts_theorem_via_unconditional.
Check @watts_unconditional_coext.
Check @watts_unconditional_coext_2a.
(* Instance/Mod/Watts/Unconditional.v: 61 names *)
Check @MSObj.
Check @ms_mod.
Check @ms_free.
Check @ms_gen.
Check @MSObj_rect.
Check @MSObj_ind.
Check @MSObj_rec.
Check @MSObj_sind.
Check @MSHom.
Check @ms_id.
Check @ms_comp.
Check @MultiSpan.
Check @ms_fobj.
Check @ms_fmap.
Check @ms_diagram.
Check @sets_limit_point.
Check @ew_Gen.
Check @ew_g0.
Check @ew_ev.
Check @ew_ev_g0.
Check @ew_Idx.
Check @ew_CopD.
Check @ew_CC.
Check @ew_CopL.
Check @ew_Cop.
Check @ew_inj.
Check @ew_y0_ex.
Check @ew_y0.
Check @ew_y0_leg.
Check @ew_am.
Check @ew_PD.
Check @ew_PL.
Check @ew_P.
Check @ew_pM.
Check @ew_pF.
Check @ew_pG.
Check @ew_pM_ev.
Check @ew_pF_inj.
Check @ew_key.
Check @ew_efam.
Check @ew_e_ex.
Check @ew_e.
Check @ew_e_leg.
Check @ew_N.
Check @ew_Q.
Check @ew_k.
Check @ew_qrel_of.
Check @ew_tfun.
Check @ew_t.
Check @ew_t_at.
Check @ew_k_t.
Check @ew_eQ.
Check @ew_t_covers.
Check @ew_WIdx.
Check @RModop_esols.
Check @RModop_continuous_representable.
Check @watts_theorem_unconditional.
Check @watts_theorem_unconditional_obj.
Check @watts_unconditional_CoHomAb_obj.
Check @RModop_hom_representable_obj.
Check @watts_unconditional_at_Z.
