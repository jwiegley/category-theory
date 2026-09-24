(** * Probe for Stone–Čech and Mac Lane V.8 Exercise 4 (issue #455)

    Pins the measured boundaries of the two files #455 adds for Mac Lane
    §V.6, printed p. 125, and §V.8, printed pp. 131–132 (the Stone–Čech
    compactification through the adjoint functor theorems, and Exercise
    4): Instance/Top/StoneCech.v (the finite case of §V.6 as a universal
    arrow with its [eq_refl] readbacks, GAFT at the underlying-set functor
    reduced to completeness, and Exercise 4 at the level of universal
    arrows) and Instance/Top/StoneCech/Refutations.v (completeness of
    [CompHaus] and of [Top], and the adjunction at [CompHaus_Forget],
    refuted under an arrow index or [IEM], above the hom universe through
    an index of [Top]; the vacuity pairs; SAFT at the inclusion reduced to
    three hypotheses; [big_inj]; the cost of a cogenerator with stable
    members, and of a single point-separating space).  N2, N6-N14 and
    N18-N22 restate a readback or a refusal that a target header records,
    N2 and N12 first measured by #455's review; N1, N3-N5 and N15-N17 are
    this file's own.  The positive controls restate the files' claims
    independently.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    First Instance/Top/StoneCech/Refutations.v's twenty lines verbatim and
    in order, one of them the target Instance/Top/StoneCech.v; then the
    five lines Instance/Top/StoneCech.v adds, in its order
    (Structure/Cone.v, Structure/Limit.v, Structure/Limit/Preservation.v,
    Instance/Sets/Classifier.v and the standard library's [PeanoNat]);
    then the one target Refutations.v's list does not carry, itself.
    Twenty-six lines, with no addition for any section.  Instance/Sets.v
    and Instance/Top.v each define a [bool_setoid_object]; under this list
    the short name is Instance/Top.v's, the one the targets use, and
    Instance/Sets.v's is [Sets.bool_setoid_object] ([Locate]).  A shorter
    import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and each of the eighty-one
    definitions, examples, lemmas and records of this file that is not a
    refutation, wrapped in one in a copy of this WHOLE file, stops the
    build at that command with the report that the guarded command had
    been accepted (eighty-one of eighty-one, by a script over the
    copies).
    Every negative other than that instrument is a [Definition] or an
    [Example], never a [Check], so that an open evar or a missing instance
    cannot satisfy it.  Each negative was stripped of its refutation
    keyword in a copy of this WHOLE file, one at a time, compiled, and its
    error read; each of the twenty-three copies stops inside the stripped
    command (by the File line that precedes its error, compared by a
    script with the command's extent).  The kind recorded is the kind of
    that error, and each negative has positive controls beside it; every
    identifier a negative uses, its own name and the universes its binder
    names aside, is used by some positive control of this file (by a
    script over the identifiers of the commands).  In one further copy of
    this WHOLE file, each negative was followed by a BINDER INSTRUMENT, the
    same universe binder, arguments and return type with a trivial body
    (a hypothesis of the return type, or [Datatypes.unit] where the command
    states none): all twenty-two are accepted, so every negative is refused
    by its body.  Every UNIVERSE negative is a top-level definition whose
    universes are declared in its own binder, never a [Section]'s.
    Quotations are Rocq 9.1.1's under this file's import list, with the
    error's environment block left out; Rocq prints the "cannot unify"
    parenthetical with the short names in scope, and a universe the
    stripped copy names after itself and a serial number is written <1>,
    <2>, ..., numbered afresh in each quotation in order of first
    appearance.  The file also compiles on Coq 8.19.2 and 8.20.1, against
    the prebuilt trees of this library for those versions with the two
    targets compiled beside them from this tree; over the 152 files of
    the targets' dependency closure other than the targets, the sources of
    those trees are this tree's byte for byte but for Instance/Top.v and
    Instance/Top/CompHaus.v, which differ in comment blocks alone
    (compared by [cmp] and [diff]).  The stripped copies were compiled
    there as well, and every one is refused on both at the line and
    character range of its Rocq 9.1.1 refusal.  Under 8.20.1 every error
    but N13's is the Rocq 9.1.1 one up to the serial numbers (compared by
    a script over the copies); N13's clause names a generated universe
    where Rocq 9.1.1 names c.  Under 8.19.2 eleven are (the instrument,
    N1-N6, N8 and N20-N22); N15 keeps its clause with serial names in
    place of c and h, N7, N9-N11, N13, N14, N16, N18 and N19 print a
    "cannot unify" parenthetical in place of theirs, and N12 and N17
    print the type mismatch with no parenthetical.

    KINDS.  Twenty-three refutations, counted as the lines that open with
    the refutation keyword: NAME-ABSENCE (the instrument), CONVERSION
    (N1-N4), TYPING (N5) and UNIVERSE (N6-N22): one, four, one and
    seventeen.  No refusal is an INSTANCE or a BINDER one: every binder
    instrument is accepted.  N15 is reported over the whole command rather
    than at a subterm; the type it forms is its body, and its binder
    instrument is accepted.  N20, N21 and N22 carry no universe clause:
    each is reported as a mismatch whose two sides differ in universe
    instances alone, and in universes their binders name only at the
    slots of [CompHaus] their paragraphs give (the fourth for N20, the
    third for N21, the fourteenth and fifteenth for N22); every other
    slot that differs is one the binder leaves to inference ([_]).

    LABELS.  The pins carry the N-numbers of this file; #455's builder and
    review measured several of them in scratch files under other names,
    recorded here so that the target headers can cite either.  The
    review's p1 is the control [p455_fin_obj_bool], its p2 is N2 (its
    [bool_FinEnum'] is [p455_bool_FinEnum_rev]) and its p2pos the control
    [p455_fin_obj_bool_enum]; its p3 is [p455_refutes_gaft_output], its
    p6 is N12, its p8_big_inj is [p455_big_inj_unsplit], its p9_iff is
    [p455_compact_iff] and its w1 is [p455_saft_incl_apart].  The
    builder's and the review's [TopP], [ContHom] and [ContHomT] are
    [p455_TopP], [p455_ContHom] and N6, and the builder's
    [t_bool_FinEnum] is [p455_bool_FinEnum_bare].  The review of this
    file named v_sub_index, v_adj_refuted_IEM_above,
    v_gaft_shape_refuted_above and v_not_complete_IEM_below, which
    Refutations.v now carries as [CompHaus_ArrowIndex_of_Top],
    [StoneCech_adjunction_refuted_IEM_above],
    [CompHaus_not_complete_IEM_above] and
    [CompHaus_not_complete_IEM_below]; its v_saft_wp_below is N19, its
    v_n8_at_set [p455_bool_ch_bare_at_set], its v_ts_free
    [p455_trivial_small_free], its v_n1_wrong [p455_n1_wrong_value] and
    its v_n2_same_space [p455_n2_same_space].  A later review's adj14 is
    N22 and its s14ctl [p455_adj_above_hausdorff_at_o].  The labels are
    not constants.

    ** Instance/Top/StoneCech.v

    N1, N2 (CONVERSION).  The universal object of [StoneCech_finite] is
    [Discrete_CH X FX] at [eq_refl] ([p455_fin_obj_at], restating
    [StoneCech_finite_obj]).  At the two-point set a wrong value has to be
    chosen with care: [Bool_CH] is NOT one, being by definition
    [Discrete_CH] of [bool_setoid_object] at [bool_FinEnum], and the
    equation with it is accepted ([p455_fin_obj_bool], the trap).  N1
    compares the universal object with the one-point space, whose carrier
    differs:
      The term "eq_refl" has type "arrow_obj = arrow_obj" while it is
      expected to have type "arrow_obj = Point_CH" (cannot unify
      "arrow_obj" and "Point_CH").
    N2 compares it with [Discrete_CH] at a second enumeration of the same
    set, [p455_bool_FinEnum_rev], whose list is reversed and whose object
    is formed ([p455_bool_ch_rev]):
      The term "eq_refl" has type "arrow_obj = arrow_obj" while it is
      expected to have type "arrow_obj = Discrete_CH bool_setoid_object
      p455_bool_FinEnum_rev" (cannot unify "arrow_obj" and "Discrete_CH
      bool_setoid_object p455_bool_FinEnum_rev").
    The same statement at [bool_FinEnum] is accepted
    ([p455_fin_obj_bool_enum]).  Both enumerations end [Qed], so N2 would
    be refused for ANY second enumeration, one with the same list under
    another name among them: it pins that the universal object carries the
    enumeration it was built from.  Whether the value compared is wrong is
    meta-level: the two objects have one space ([p455_n2_same_space], at
    [eq_refl]) and differ only in their compactness proofs, [Qed] terms
    whose values no lemma of the tree exposes, so the wrongness is of the
    normal forms behind [Qed], not a theorem.  A draft of this paragraph
    said that reversing the list made the value wrong as well as
    unconvertible; #455's review measured it unconvertible only.
    N1 is refused at the carrier, where no opacity is involved, and its
    value is wrong as a theorem: [p455_n1_wrong_value] derives [False] from
    the equation, carrying [true] and [false] of the two-point carrier to
    the point.

    N3 (CONVERSION).  The unit is [sc_fin_unit X FX] at [eq_refl]
    ([p455_fin_unit_at], restating [StoneCech_finite_unit]); it does not
    see the enumeration ([p455_fin_unit_other_enum]: at [FX] it IS
    [sc_fin_unit X FX'] for any [FX']), and at the two-point set it is the
    identity of [Sets] ([p455_fin_unit_bool_id]).  N3 compares it with the
    negation [p455_negb_lift], an arrow of the same type, ending [Defined],
    that differs from the unit at the point [true] ([p455_negb_not_unit]):
      The term "eq_refl" has type "arrow = arrow" while it is expected to
      have type "arrow = p455_negb_lift" (cannot unify "arrow" and
      "p455_negb_lift").

    N4 (CONVERSION).  At a compact Hausdorff [K] the identity universal
    arrow has [K] as its universal object ([p455_incl_obj_at], restating
    [CompHaus_Incl_universal_obj]); at [K] := [Point_CH] the equation with
    [Point_CH] is accepted ([p455_incl_obj_point]), and at a variable [K]:
      The term "eq_refl" has type "arrow_obj = arrow_obj" while it is
      expected to have type "arrow_obj = Point_CH" (cannot unify
      "arrow_obj" and "Point_CH").

    N5 (TYPING).  Why every universal arrow of the two targets is written
    [UniversalArrow (C:=Sets) ...] or [(C:=Top@{h o})], and every readback
    [@arrow_obj Sets _ ...]: Theory/Universal/Arrow.v's [UniversalArrow]
    elaborates its object before its category, so without [C] the object
    is refused, and with it the type is formed ([p455_ua_with_C]):
      The term "Setoid_Lift X" has type "SetoidObject" while it is expected
      to have type "obj[?C]".
    The same refusal meets [@arrow_obj _ _ (Setoid_Lift X) ...] and
    [UniversalArrow (KSet AI) ...], both recorded by #455's builder and
    scouts (measured in scratch files with this file's import list).

    N6 (UNIVERSE).  StoneCech.v's header, WHY: THE UNIVERSE OF TOP'S HOMS,
    records that a Prop-valued topology puts continuous maps at the
    universe of the points, and cites this file's [p455_TopP] (a setoid
    with Prop-valued opens closed under unions indexed at the points'
    universe, and no other field) and [p455_ContHom], both accepted under
    the CLOSED binder [@{o}], so [p455_ContHom@{o}] lands in [Type@{o}]
    with no constraint at all.  The tree's
    [ContinuousMorphism] is accepted at [Type@{h}] with [o < h]
    ([p455_conthom_at_h]); at [Type@{o}], N6:
      The term "ContinuousMorphism X Y" has type "Type@{<1>}" while it is
      expected to have type "Type@{o}" (universe inconsistency: Cannot
      enforce <1> <= o because o < <1>).
    The header's quotation, from a closed binder [@{o}], carries the same
    clause; N6's binder is extensible, so the refusal is not the binder's.

    N7 (UNIVERSE).  Instance/Top.v's [Point_Hausdorff] is monomorphised at
    a [Set] carrier ([About]: [IsHausdorff@{u Set Set Set}
    Point_Top@{Set}]; that file's CORRECTION (#455) comment).  It is
    accepted there ([p455_point_hausdorff_set]); above [Set] the one-point
    space is separated by [Discrete_Hausdorff] ([p455_point_hausdorff_o])
    and compact by Instance/Top.v's universe-general [Point_Compact]
    ([p455_point_compact_o]), and [Point_CH]'s space is [Point_Top@{o}] at
    [Set < o] ([p455_point_ch_above_set]).  [Point_Hausdorff] at that
    type, N7:
      The term "Point_Hausdorff" has type "IsHausdorff@{<1> Set Set Set}
      Point_Top@{Set}" while it is expected to have type "IsHausdorff@{h o
      o o} Point_Top@{o}" (universe inconsistency: Cannot enforce Set =
      o).

    N8 (UNIVERSE).  StoneCech.v's header, UNIVERSES: without a binder,
    [bool_FinEnum] elaborates at [FinEnum@{Set} bool_setoid_object@{Set
    Set}], "which would force [Bool_CH], built from it, and so the
    refutations that use [Bool_CH], to a [Set] carrier".  Restated as
    [p455_bool_FinEnum_bare], the same proof with no binder, whose [About]
    reads the same (measured in a scratch copy of this file).  N8's own
    body at [Set] is accepted ([p455_bool_ch_bare_at_set]), so that "forces
    a [Set] carrier" is measured rather than read off the clause.  What it
    forces is narrower than the lemma: it is accepted at [Set]
    ([p455_bare_at_set]); at [FinEnum bool_setoid_object@{o o}] with [Set
    < o] it is accepted too, by conversion ([p455_bare_at_o]); and so is an
    object of [CompHaus] above [Set] built from it once the setoid is named
    at [o] ([p455_bare_named_setoid]).  What is refused is [Bool_CH]'s own
    body, which leaves the setoid to inference, so that the placeholder is
    solved from the lemma's type, at [Set].  That body with the file's
    [bool_FinEnum] is accepted under an extensible binder
    ([p455_bool_ch_body]), and [Bool_CH] itself lives above [Set]
    ([p455_bool_ch_above_set]); with [p455_bool_FinEnum_bare], N8:
      The term "(Bool_Discrete; (Discrete_Compact_of_FinEnum
      bool_setoid_object p455_bool_FinEnum_bare, Discrete_Hausdorff ?A))"
      has type "∃ x : obj[Top], Subcategory.sobj _
      CompactHausdorff_Subcategory x" while it is expected to have type
      "obj[CompHaus]" (cannot satisfy constraint "IsCompact (Discrete_Top
      bool_setoid_object) ∧ IsHausdorff (Discrete_Top ?A)" == "(λ x :
      obj[Top], Subcategory.sobj _ CompactHausdorff_Subcategory x)
      Bool_Discrete"; universe inconsistency: Cannot enforce Set = o).
    With [Set < o] declared the same body is refused with the same clause
    (measured in a scratch file with this file's import list).  So the
    header's sentence holds of [Bool_CH] as written, where the binder is
    load-bearing; the lemma itself converts to any carrier.

    N9 (UNIVERSE).  StoneCech.v's header, (3) and UNIVERSES: the
    tautological solution set is legal because the whole object type of
    [CompHaus] sits at its hom universe, and all four universes of GAFT's
    completeness hypothesis are h.  [taut_sols] itself is not bound to
    that: its index is the universe of the objects of the [CompHaus] its
    [CompHaus_Forget] starts from ([About]), and with those objects at c
    above h it is accepted ([p455_taut_sols_above]).  Adjunction/GAFT.v's
    [GAFT] takes solution sets indexed at the hom universe
    ([SolutionSet@{h dobj cobj h}]), so
    GAFT at [CompHaus_Forget] with [taut_sols] is accepted with the objects
    at h ([p455_gaft_body], [GAFT_CompHaus_only_complete]'s body restated,
    and [p455_gaft_only_complete]), and at [h < c] N9 is refused at
    [taut_sols], whose type, a solution set indexed at the objects'
    universe, is expected to be one indexed at h:
      (universe inconsistency: Cannot enforce c = h because h < c).
    The placement of the objects at h is what GAFT's use of the
    tautological solution set costs; with the objects above h GAFT would
    need another solution set, which neither target builds.

    ** Instance/Top/StoneCech/Refutations.v

    N10 (UNIVERSE).  Refutations.v's UNIVERSES: the index form
    [CompHaus_not_complete] ties nothing between the shape s and the
    objects c, the [IEM] form needs [c <= s].  The index form is accepted
    at [s < c] ([p455_not_complete_index]), the [IEM] form at [c <= s] and
    [h <= s] ([p455_not_complete_IEM]) and at GAFT's instance
    ([p455_not_complete_IEM_gaft]).  The [IEM] form at [s < c], N10:
      The term "comp" has type "Complete@{r s h c}" while it is expected
      to have type "Complete@{<1> s h <2>}" (universe inconsistency:
      Cannot enforce <2> = c because <2> <= <3> < c).
    Structure/Complete/Freyd.v's [canonical_ArrowIndex], which
    [CompHaus_not_complete_IEM] applies to [CompHaus]'s own objects,
    indexes at or above the objects and the homs ([About]:
    [ArrowIndex@{u u0 u1}] under [u0 <= u] and [u1 <= u]).  So N10 pins
    the scope of that constant, not the reach of [IEM]:
    [CompHaus_ArrowIndex_of_Top] transports an index of [Top]
    ([p455_sub_index]), [IEM] supplies one at every [s] with [h <= s], and
    [CompHaus_not_complete_IEM_below] refutes N10's statement with
    [h <= s] added ([p455_not_complete_IEM_below]), GAFT's shape with the
    objects above the homs being its case
    [CompHaus_not_complete_IEM_above] ([p455_not_complete_IEM_above]).

    N11 (UNIVERSE).  The same for [Top]: [Top_not_complete] is accepted at
    [s < h] ([p455_top_not_complete_index]) and [Top_not_complete_IEM] at
    [h <= s] ([p455_top_not_complete_IEM]); the latter at [s < h], N11:
      The term "comp" has type "Complete@{r s h h}" while it is expected
      to have type "Complete@{<1> <2> <3> <3>}" (universe inconsistency:
      Cannot enforce <3> = h because <3> <= <2> < h).

    N12 (UNIVERSE).  The reach of [StoneCech_adjunction_refuted_IEM]: it
    is proved at [CompHaus@{h h h h ...}], the objects at the hom
    universe, which is the instance [GAFT_CompHaus_only_complete] produces
    ([p455_adj_refuted_IEM], restating it, and [p455_refutes_gaft_output],
    the refutation applied to GAFT's own output).  With the objects at c
    above h, N12 is refused at the argument [A], whose type, as written in
    the binder, is expected to be the one the constant quantifies over,
    with one universe in the object and hom slots of its [CompHaus]:
      (universe inconsistency: Cannot enforce c = h because h < c).
    The index form reaches that instance: given an arrow index at the hom
    universe, [large_universal_arrow_refuted] refutes the adjunction with
    the objects at c above h ([p455_adj_refuted_index_above]).  N12 pins
    the scope of [StoneCech_adjunction_refuted_IEM], which applies
    [canonical_ArrowIndex] to [CompHaus]'s own objects, not the reach of
    [IEM]: [IEM] supplies an index at the hom universe through [Top]'s,
    and [StoneCech_adjunction_refuted_IEM_above] refutes N12's very
    statement ([p455_adj_refuted_IEM_above]).  A draft of this paragraph
    said that [IEM] does not supply such an index; #455's review measured
    that it does, through [CompHaus_ArrowIndex_of_Top].

    N20-N22 (UNIVERSE).  Refutations.v's COVERAGE: the forms through
    [Top]'s index apply only at instances of [CompHaus] whose third slot,
    the hom universe of its [Top], is h, whose fourth, the universe of the
    proof that a space is compact Hausdorff, is c, and whose fourteenth
    and fifteenth, the universes of the separating opens of its Hausdorff
    proof, are the points' universe o.  With [CompHaus]
    written out slot by slot, [StoneCech_adjunction_refuted_IEM_above] is
    accepted with the fourth slot at c ([p455_adj_above_slots]); with it
    at h, N20 is refused at [A]:
      The term "A" has type "∃ F : Sets@{h s} ⟶ CompHaus@{c h h h ...},
      F ⊣ CompHaus_Forget@{...}" while it is expected to have type "∃ F :
      Sets@{h s} ⟶ CompHaus@{c h h c ...}, F ⊣ CompHaus_Forget@{...}".
    [CompHaus_not_complete_IEM_below] at GAFT's shape above the homs is
    accepted with the third slot at h ([p455_not_complete_below_slots]);
    with it at t below h, N21 is refused at [comp]:
      The term "comp" has type "@Complete@{h h h c} CompHaus@{c h t c
      ...}" while it is expected to have type "@Complete@{h h h c}
      CompHaus@{c h h c ...}" (cannot unify "D ⟶ CompHaus@{c h h c ...}"
      and "D ⟶ CompHaus@{c h t c ...}"),
    the last eleven slots of each [CompHaus], and the instances of
    [CompHaus_Forget], elided.  The older form reaches the third slot
    below h where its [c <= s] holds ([p455_not_complete_IEM_top_slot], at
    c = h = s); at an instance with t < h < c and a shape below c neither
    form applies, the older one needing [c <= s] (N10).
    [StoneCech_adjunction_refuted_IEM_above] is accepted with the
    fourteenth and fifteenth slots written out at o
    ([p455_adj_above_hausdorff_at_o]), o being where [Bool_CH] and
    [Point_CH] put them, from [Discrete_Hausdorff@{h o}]; with both at q
    below o, where the adjunction's type is still formed (N22's binder
    instrument), N22 is refused at [A]:
      The term "A" has type "∃ F : Sets@{h s} ⟶ CompHaus@{c h h c ...
      q q}, F ⊣ CompHaus_Forget@{...}" while it is expected to have type
      "∃ F : Sets@{h s} ⟶ CompHaus@{c h h c ... o o}, F ⊣
      CompHaus_Forget@{...}",
    the fifth through thirteenth slots of each [CompHaus], and the
    instances of [CompHaus_Forget], elided.  #455's review measured the
    same refusal with either slot alone below o, and a refusal of every
    other form, the index forms included, with both below o (in scratch
    files with this file's import list).

    N13, N14 (UNIVERSE).  Refutations.v's (3): discharging the
    well-poweredness of SAFT at the inclusion by [CompHaus_WellPowered]
    forces [c = h].  [SAFT_CompHaus_Incl] is restated ([p455_saft_incl]),
    and its body with c and h named apart and nothing declared between
    them is accepted ([p455_saft_incl_apart]; its [About] reads "c = h",
    measured in a scratch copy of this file).  At [h < c], N13 is refused
    at [CompHaus_WellPowered], whose type is expected at the instance the
    other arguments fix:
      (universe inconsistency: Cannot enforce h = <1> because h < c <=
      <1>),
    and at [c < h] N14 is refused at [comp], before the well-powering is
    reached, with the inclusion's clause (N17, N19):
      The term "comp" has type "Complete@{s s h c}" while it is expected
      to have type "Complete@{s s h <1>}" (universe inconsistency: Cannot
      enforce <1> = c because c < h <= <1>).
    With a well-powering hypothesis indexed at the objects' universe in
    place of [CompHaus_WellPowered], SAFT at the inclusion is accepted at
    [h < c] ([p455_saft_wp_hyp_above]), and so are the two vacuity pairs
    with theirs ([p455_saft_vacuous], [p455_saft_iem_vacuous]): the half
    [c <= h] of the equation is [CompHaus_WellPowered]'s, not SAFT's.
    The half [h <= c] is the inclusion's under ANY well-powering: with a
    well-powering hypothesis at [c < h], N19 is refused at [comp] with the
    same clause as N14:
      The term "comp" has type "Complete@{s s h c}" while it is expected
      to have type "Complete@{s s h <1>}" (universe inconsistency: Cannot
      enforce <1> = c because c < h <= <1>).
    A draft of this paragraph attributed the whole equation to
    [CompHaus_WellPowered]; #455's review measured that only [c <= h] is
    its (N19).  With
    the shape below the objects, which such a well-powering allows,
    [SAFT_Incl_IEM_vacuous_below] still pairs SAFT with the refutation
    ([p455_saft_iem_vacuous_below]).

    N15-N17 (UNIVERSE).  Where each half of [c = h] comes from.  [c <= h]:
    Structure/WellPowered.v's [WellPowered@{o h w s t}] declares [o <= s],
    and [trivial_small] fixes s at the hom universe ([WellPowered@{o h h h
    t}]).  [CompHaus_WellPowered] is restated ([p455_wellpowered]),
    [trivial_small] is accepted at [c < h] ([p455_trivial_small_below]),
    and a well-powering type indexed at c is formed at [h < c]
    ([p455_wp_type_at_c]); the one indexed at h is not, N15:
      Universe inconsistency. Cannot enforce c <= h because h < c.
    and [trivial_small] does not inhabit the one indexed at c, N16:
      The term "trivial_small CompHaus" has type "WellPowered@{<1> <2> <2>
      <2> <3>} CompHaus@{...}" while it is expected to have type
      "WellPowered@{c h h c t} CompHaus@{...}" (universe inconsistency:
      Cannot enforce c = h because h < c),
    the two instances of [CompHaus] elided; with c and h left unordered
    the same type is inhabited, at c = h ([p455_trivial_small_free], whose
    [About] reads "c = h").  [h <= c]: [CompHaus_Incl]
    carries its domain's hom universe below its objects' ([About]: the
    domain is [CompHaus@{u u0 u0 ...}] under [u0 <= u]).  The inclusion is
    accepted at [h < c] ([p455_incl_above]); at [c < h], N17 is refused at
    [CompHaus_Incl], whose type is expected at the ascribed [CompHaus]:
      (universe inconsistency: Cannot enforce <1> = h because <1> <= <2> <
      h).

    N18 (UNIVERSE).  Refutations.v's (4): [big_inj] ties its index to the
    objects of the very category [comp] is about, by the local definition
    [C := CompHaus], and its block carries [c <= s].
    [big_inj_injective] is restated ([p455_big_inj_injective]), and
    [big_inj]'s body with [obj[CompHaus]] written in both places is
    accepted at [s < c] ([p455_big_inj_unsplit]), the two [CompHaus] then
    separate instances; [big_inj] at [s < c], N18:
      The term "comp" has type "Complete@{r s h c}" while it is expected
      to have type "Complete@{<1> s h <2>}" (universe inconsistency:
      Cannot enforce <2> = c because <2> <= <3> < c).

    CONTROLS of the rest of the two files, each restating a constant at
    its stated type: the constructive pieces [p455_stonecech_finite],
    [p455_discrete_hausdorff], [p455_compact_iff] (compactness of a
    discrete space iff finite enumerability, both directions at one
    instance) and [p455_nat_not_compact]; the reduction [p455_pres] and
    [p455_taut_sols]; Exercise 4, [p455_ex4_separated],
    [p455_ex4_converse], [p455_ex4_dec], [p455_ex4_bool],
    [p455_ex4_incl], [p455_ex4_incl_converse], [p455_ex4_at_CompHaus],
    [p455_ex4_incl_local] and [p455_ex4_local_at_CompHaus]; and the
    metatheorems [p455_large_ua_refuted], [p455_gaft_vacuous],
    [p455_gaft_vacuous_above], [p455_cogen_dne] and [p455_point_sep_dne].
    Nothing here inhabits the premises of the completeness conditionals,
    of [p455_cogen_dne] or of [p455_point_sep_dne].

    NOT PINNED HERE.  (a) That the tree builds no unconditional binary
    product in [Top]: the two walls in front of the pairing's continuity
    are Test/ProbeCompHaus413.v's N1 and N2.  A draft of this item said
    that [Top] has no binary products without a hypothesis, and that that
    probe pins it; #455's review found that this is not a theorem
    (classically [Top] has them).  (b) The
    report of #455's scouts that [Section] [Context] binders over
    [CompHaus] are refused: it did not reproduce for #455's builder, and
    neither target rests on it.  (c) [About] readbacks as such, the
    [Set] of [p455_bool_FinEnum_bare], the "c = h" of
    [p455_saft_incl_apart] and the index of [taut_sols]: measured in
    scratch copies of this file, and pinned here by their consequences (N8,
    N13-N17 and N9); likewise the [h <= c] that [CompHaus_Forget] and
    [CompHaus_Incl] carry and the slots Refutations.v's COVERAGE names
    (N12, N17, N19-N22).  (d) Flip censuses ([Defined] against [Qed]) and the
    closure of the targets under [Print Assumptions]: measurements of the
    build rather than of commands; the Makefile's print-assumptions gate
    is where closure is kept.  An item (e), the review's p4 and p5, is
    retired: both are now constants of the targets, restated by
    [p455_ex4_incl_local], [p455_ex4_local_at_CompHaus] and
    [p455_point_sep_dne].

    The guard block at the end names the seventy-four constants of the
    two targets, so that a rename breaks this file: forty-one of
    Instance/Top/StoneCech.v and thirty-three of
    Instance/Top/StoneCech/Refutations.v.  They are the [def] and [prf]
    entries of the targets' .glob files, which carry no entry of any other
    kind (no [abbrev] among them), and exactly the names [Print Module]
    lists for each (compared by [diff]); neither target uses [Program], so
    there is no obligation constant.  Under the full import list, [Locate]
    lists exactly one object for each of the seventy-four, the target's. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Coq.Lists.List.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.Classifier.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Instance.Top.StoneCech.Refutations.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe455_absent_name.

(** ** N1-N5 (CONVERSION, TYPING): Instance/Top/StoneCech.v, the readbacks *)

(* CONTROL: [StoneCech_finite], restated at its stated type. *)
Definition p455_stonecech_finite@{o h +} (X : SetoidObject@{o o})
  (FX : FinEnum X) :
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget :=
  StoneCech_finite X FX.

(* CONTROL: [StoneCech_finite_obj] and [StoneCech_finite_unit], restated. *)
Example p455_fin_obj_at@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  @arrow_obj Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = Discrete_CH X FX := eq_refl.

Example p455_fin_unit_at@{o h +} (X : SetoidObject@{o o}) (FX : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX := eq_refl.

(* CONTROL: at the two-point set the universal object IS [Bool_CH], so
   [Bool_CH] is not a wrong value there; and it is [Discrete_CH] at the
   enumeration passed. *)
Example p455_fin_obj_bool@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Bool_CH :=
  eq_refl.

Example p455_fin_obj_bool_enum@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = Discrete_CH bool_setoid_object@{o o} bool_FinEnum := eq_refl.

(* CONTROL: the one-point space is an object of [CompHaus] at every
   carrier universe. *)
Example p455_point_ch_above_set@{o +| Set < o +} :
  `1 Point_CH = Point_Top@{o} := eq_refl.

Fail Example p455_n1_fin_obj_bool_point@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Point_CH :=
  eq_refl.

(* CONTROL: N1's value is wrong, not merely unconvertible: the equation
   carries [true] and [false] of the two-point carrier to the point. *)
Lemma p455_n1_wrong_value@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) = Point_CH →
  False.
Proof.
  intro H.
  assert (E : ∀ a b : top_carrier (`1 (@arrow_obj Sets _
                 (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
                 (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum))),
              a = b).
  { rewrite H. intros [] []. reflexivity. }
  specialize (E true false). discriminate E.
Qed.

(* CONTROL: a second enumeration of the two-point set, its list reversed,
   and the object it gives. *)
Lemma p455_bool_FinEnum_rev@{o +} : FinEnum bool_setoid_object@{o o}.
Proof.
  exists (false :: true :: nil). intros [|].
  - exists true. split; [right; left; reflexivity | reflexivity].
  - exists false. split; [left; reflexivity | reflexivity].
Qed.

Definition p455_bool_ch_rev@{o +} : CompHaus :=
  Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev.

Fail Example p455_n2_fin_obj_other_enum@{o h +} :
  @arrow_obj Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev := eq_refl.

(* CONTROL: N2's two objects have one space; they differ in the
   compactness proof alone. *)
Example p455_n2_same_space@{o +} :
  `1 (Discrete_CH bool_setoid_object@{o o} bool_FinEnum)
  = `1 (Discrete_CH bool_setoid_object@{o o} p455_bool_FinEnum_rev) :=
  eq_refl.

(* CONTROL: the unit does not see the enumeration; at the two-point set it
   IS the identity of [Sets]. *)
Example p455_fin_unit_other_enum@{o h +} (X : SetoidObject@{o o})
  (FX FX' : FinEnum X) :
  @arrow Sets _ (Setoid_Lift@{o h} X) _ (StoneCech_finite X FX)
    = sc_fin_unit X FX' := eq_refl.

Example p455_fin_unit_bool_id@{o h +} :
  @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = @id Sets (Setoid_Lift@{o h} bool_setoid_object@{o o}) := eq_refl.

(* CONTROL: negation, an arrow of the unit's type that differs from the
   unit at a point. *)
Definition p455_negb_lift@{o h +} :
  Setoid_Lift@{o h} bool_setoid_object@{o o} ~{Sets}~>
    CompHaus_Forget (Discrete_CH bool_setoid_object@{o o} bool_FinEnum).
Proof.
  unshelve refine {| morphism := negb |}.
  intros a b e. simpl in *. rewrite e. reflexivity.
Defined.

Lemma p455_negb_not_unit@{o h +} :
  p455_negb_lift
    ≈ @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
        (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum) → False.
Proof. intro H. specialize (H true). simpl in H. discriminate H. Qed.

Fail Example p455_n3_fin_unit_negb@{o h +} :
  @arrow Sets _ (Setoid_Lift@{o h} bool_setoid_object@{o o}) _
    (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum)
    = p455_negb_lift := eq_refl.

(* CONTROL: [CompHaus_Incl_universal_obj], restated, and at the point. *)
Example p455_incl_obj_at@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K)
    = K := eq_refl.

Example p455_incl_obj_point@{h o +} :
  @arrow_obj Top@{h o} _ (CompHaus_Incl Point_CH) _
    (CompHaus_Incl_universal Point_CH) = Point_CH := eq_refl.

Fail Example p455_n4_incl_obj_point@{h o +} (K : CompHaus) :
  @arrow_obj Top@{h o} _ (CompHaus_Incl K) _ (CompHaus_Incl_universal K)
    = Point_CH := eq_refl.

(* CONTROL: the type of a universal arrow with its category named. *)
Definition p455_ua_with_C@{o h +} (X : SetoidObject@{o o}) : Type :=
  UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget.

Fail Definition p455_n5_ua_without_C@{o h +} (X : SetoidObject@{o o}) :
  Type :=
  UniversalArrow (Setoid_Lift@{o h} X) CompHaus_Forget.

(** ** N6-N8 (UNIVERSE): Instance/Top/StoneCech.v, the universes *)

(* CONTROL: the header's Prop-valued topology.  A setoid with Prop-valued
   opens closed under unions indexed at the points' universe, and its
   continuous maps, at that universe, under a CLOSED binder. *)
Record p455_TopP@{o} := {
  p455_tp_carrier :> SetoidObject@{o o};
  p455_POpen : (p455_tp_carrier → Prop) → Prop;
  p455_popen_union (I : Type@{o}) (U : I → p455_tp_carrier → Prop) :
    (∀ i, p455_POpen (U i)) → p455_POpen (fun x => exists i, U i x)%type
}.

Definition p455_ContHom@{o} (X Y : p455_TopP@{o}) : Type@{o} :=
  { f : SetoidMorphism@{o o o} X Y &
    ∀ U : Y → Prop, p455_POpen Y U → p455_POpen X (fun x => U (f x)) }.

(* CONTROL: the tree's continuous maps one universe up. *)
Definition p455_conthom_at_h@{h o +| o < h +} (X Y : TopSpace@{o}) :
  Type@{h} :=
  ContinuousMorphism X Y.

Fail Definition p455_n6_conthom_at_o@{o +} (X Y : TopSpace@{o}) :
  Type@{o} :=
  ContinuousMorphism X Y.

(* CONTROL: [Point_Hausdorff] at its [Set] carrier; the one-point space
   separated and compact above [Set], by [Discrete_Hausdorff] and by
   Instance/Top.v's [Point_Compact]. *)
Definition p455_point_hausdorff_set : IsHausdorff Point_Top@{Set} :=
  Point_Hausdorff.

Definition p455_point_hausdorff_o@{h o +| o < h +} :
  IsHausdorff@{h o o o} Point_Top@{o} :=
  Discrete_Hausdorff _.

Definition p455_point_compact_o@{o +| Set < o +} :
  IsCompact Point_Top@{o} :=
  Point_Compact.

Fail Definition p455_n7_point_hausdorff_o@{h o +| o < h +} :
  IsHausdorff@{h o o o} Point_Top@{o} :=
  Point_Hausdorff.

(* CONTROL: [bool_FinEnum] stated without a universe binder, and its uses:
   at [Set], at [FinEnum] above [Set] by conversion, and in an object of
   [CompHaus] above [Set] once its setoid is named at that universe. *)
Lemma p455_bool_FinEnum_bare : FinEnum bool_setoid_object.
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | reflexivity].
  - exists false. split; [right; left; reflexivity | reflexivity].
Qed.

Definition p455_bare_at_set : FinEnum bool_setoid_object@{Set Set} :=
  p455_bool_FinEnum_bare.

Definition p455_bare_at_o@{o +| Set < o +} :
  FinEnum bool_setoid_object@{o o} :=
  p455_bool_FinEnum_bare.

Definition p455_bare_named_setoid@{o +| Set < o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum bool_setoid_object@{o o}
        p455_bool_FinEnum_bare, Discrete_Hausdorff _)).

(* CONTROL: [Bool_CH]'s body, and [Bool_CH] itself above [Set]. *)
Definition p455_bool_ch_body@{o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum _ bool_FinEnum, Discrete_Hausdorff _)).

Example p455_bool_ch_above_set@{o +| Set < o +} :
  `1 Bool_CH = Bool_Discrete@{o} := eq_refl.

(* CONTROL: N8's own body at [Set]. *)
Definition p455_bool_ch_bare_at_set : CompHaus :=
  (Bool_Discrete@{Set};
     (Discrete_Compact_of_FinEnum _ p455_bool_FinEnum_bare,
      Discrete_Hausdorff _)).

Fail Definition p455_n8_bool_ch_bare@{o +} : CompHaus :=
  (Bool_Discrete@{o};
     (Discrete_Compact_of_FinEnum _ p455_bool_FinEnum_bare,
      Discrete_Hausdorff _)).

(** ** N9 (UNIVERSE): Instance/Top/StoneCech.v, the reduction of GAFT *)

(* CONTROL: the reduction of GAFT at [CompHaus_Forget] to completeness. *)
Definition p455_pres@{h s +} :
  @PreservesImageLimit CompHaus Sets@{h s} CompHaus_Forget :=
  CompHaus_Forget_PreservesImageLimit.

Definition p455_taut_sols@{h s +} (d : obj[Sets@{h s}]) :
  SolutionSet CompHaus_Forget d :=
  taut_sols d.

Definition p455_gaft_only_complete@{h s +}
  (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT_CompHaus_only_complete comp.

(* CONTROL: [GAFT_CompHaus_only_complete]'s body, restated. *)
Definition p455_gaft_body@{h s +} (comp : @Complete@{h h h h} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(* CONTROL: the tautological solution set with the objects of [CompHaus]
   above its homs. *)
Definition p455_taut_sols_above@{h s c +| h < c +} (d : obj[Sets@{h s}]) :
  SolutionSet (CompHaus_Forget : (CompHaus : Category@{c h h}) ⟶ Sets@{h s})
    d :=
  taut_sols d.

Fail Definition p455_n9_gaft_taut_above@{h s c +| h < c +}
  (comp : @Complete@{h h h c} CompHaus) :
  { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } :=
  GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit taut_sols.

(** ** Controls: the constructive pieces of Instance/Top/StoneCech.v *)

(* CONTROL: [Discrete_Hausdorff]; compactness of a discrete space iff
   finite enumerability, at one instance; discrete ℕ not compact. *)
Definition p455_discrete_hausdorff@{h o +| o < h +}
  (A : SetoidObject@{o o}) : IsHausdorff@{h o o o} (Discrete_Top@{o o} A) :=
  Discrete_Hausdorff A.

Definition p455_compact_iff@{o +} (A : SetoidObject@{o o}) :
  (FinEnum A → IsCompact (Discrete_Top@{o o} A))
  ∧ (IsCompact (Discrete_Top@{o o} A) → FinEnum A) :=
  (Discrete_Compact_of_FinEnum A, FinEnum_of_Discrete_Compact A).

Definition p455_nat_not_compact@{o +} :
  IsCompact (Discrete_Top@{o o} sc_nat_setoid) → False :=
  Discrete_nat_not_compact.

(* CONTROL: Exercise 4 over the underlying-set functor. *)
Definition p455_ex4_separated@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, (∀ (K : CompHaus)
                 (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
              → x ≈ y) →
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y :=
  unit_injective_of_separated X UA.

Definition p455_ex4_converse@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget) :
  (∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y) →
  ∀ x y : X, (∀ (K : CompHaus)
                (f : Setoid_Lift X ~{Sets}~> CompHaus_Forget K), f x ≈ f y)
             → x ≈ y :=
  separated_of_unit_injective X UA.

Definition p455_ex4_dec@{o h +} (X : SetoidObject@{o o})
  (UA : UniversalArrow (C:=Sets) (Setoid_Lift@{o h} X) CompHaus_Forget)
  (dec : ∀ x y : X, (x ≈ y) + ((x ≈ y) → False)) :
  ∀ x y : X, @arrow _ _ _ _ UA x ≈ @arrow _ _ _ _ UA y → x ≈ y :=
  unit_injective_of_dec X UA dec.

Definition p455_ex4_bool@{o h +} :
  ∀ x y : bool_setoid_object@{o o},
    @arrow _ _ _ _ (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
                    : UniversalArrow (C:=Sets)
                        (Setoid_Lift@{o h} bool_setoid_object@{o o})
                        CompHaus_Forget) x
    ≈ @arrow _ _ _ _ (StoneCech_finite bool_setoid_object@{o o} bool_FinEnum
                      : UniversalArrow (C:=Sets)
                          (Setoid_Lift@{o h} bool_setoid_object@{o o})
                          CompHaus_Forget) y
    → x ≈ y :=
  StoneCech_finite_bool_injective.

(* CONTROL: Exercise 4 at a space, over the inclusion. *)
Definition p455_ex4_incl@{h o +} (K : CompHaus) (X : Top@{h o})
  (HX : KSeparated K X)
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl) :
  ∀ x y : top_carrier X,
    continuous_map (@arrow _ _ _ _ UA) x
      ≈ continuous_map (@arrow _ _ _ _ UA) y
    → x ≈ y :=
  StoneCech_unit_injective_completely_regular K X HX UA.

Definition p455_ex4_incl_converse@{h o +} (K : CompHaus)
  (sepK : ∀ (Y : CompHaus) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (X : Top@{h o}) (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X :=
  KSeparated_of_unit_injective K sepK X UA Hinj.

Definition p455_ex4_at_CompHaus@{h o +} (K : CompHaus) :
  ∀ x y : top_carrier (CompHaus_Incl K : obj[Top@{h o}]),
    continuous_map (@arrow _ _ _ _ (CompHaus_Incl_universal K)) x
      ≈ continuous_map (@arrow _ _ _ _ (CompHaus_Incl_universal K)) y
    → x ≈ y :=
  StoneCech_unit_injective_at_CompHaus K.

Definition p455_ex4_incl_local@{h o +} (K : CompHaus) (X : Top@{h o})
  (UA : UniversalArrow (C:=Top@{h o}) X CompHaus_Incl)
  (sepK : ∀ p q : top_carrier (`1 (@arrow_obj _ _ _ _ UA)),
            (∀ k : @arrow_obj _ _ _ _ UA ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (Hinj : ∀ x y : top_carrier X,
     continuous_map (@arrow _ _ _ _ UA) x
       ≈ continuous_map (@arrow _ _ _ _ UA) y
     → x ≈ y) :
  KSeparated K X :=
  KSeparated_of_unit_injective_local K X UA sepK Hinj.

Definition p455_ex4_local_at_CompHaus@{h o +} (K : CompHaus) :
  KSeparated K (CompHaus_Incl K : obj[Top@{h o}]) :=
  KSeparated_of_unit_injective_local_at_CompHaus K.

(** ** N10-N12, N20-N22 (UNIVERSE): Instance/Top/StoneCech/Refutations.v,
       the reach of the refutations *)

(* CONTROL: completeness of [CompHaus] refuted by an index at a shape
   below its objects; by [IEM] at [c <= s] and [h <= s], and at GAFT's
   instance. *)
Definition p455_not_complete_index@{r s c h +| s < c +}
  (AI : ArrowIndex@{s c h} CompHaus) (comp : @Complete@{r s h c} CompHaus) :
  False :=
  CompHaus_not_complete AI comp.

Definition p455_not_complete_IEM@{e r s c h +| c <= s, h <= s +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

Definition p455_not_complete_IEM_gaft@{e h +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

(* CONTROL: an arrow index of [Top] transported to [CompHaus]; through it,
   N10's statement with [h <= s] refuted under [IEM], and GAFT's shape
   with the objects above the homs. *)
Definition p455_sub_index@{s h o c +} (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (CompHaus : Category@{c h h}) :=
  CompHaus_ArrowIndex_of_Top AIT.

Definition p455_not_complete_IEM_below@{e r s c h +| s < c, h <= s +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM_below E comp.

Definition p455_not_complete_IEM_above@{e h c +| h < c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h})) : False :=
  CompHaus_not_complete_IEM_above E comp.

Fail Definition p455_n10_not_complete_IEM_below@{e r s c h +| s < c +}
  (E : IEM@{e}) (comp : @Complete@{r s h c} CompHaus) : False :=
  CompHaus_not_complete_IEM E comp.

(* CONTROL: [CompHaus] written out slot by slot, its [Top] slot (the
   third) at the homs, its proof slot (the fourth) at the objects: the
   form through [Top]'s index at GAFT's shape above the homs; the older
   form with the [Top] slot below the homs. *)
Definition p455_not_complete_below_slots@{e h c o +| h < c +}
  (E : IEM@{e})
  (comp : @Complete@{h h h c}
            (CompHaus@{c h h c _ _ o _ _ _ _ _ _ _ _} : Category@{c h h})) :
  False :=
  CompHaus_not_complete_IEM_below@{e h h c h o _ _ _ _ _ _ _} E comp.

Definition p455_not_complete_IEM_top_slot@{e h t o +| t < h +}
  (E : IEM@{e})
  (comp : @Complete@{h h h h}
            (CompHaus@{h h t h _ _ o _ _ _ _ _ _ _ _} : Category@{h h h})) :
  False :=
  CompHaus_not_complete_IEM E comp.

Fail Definition p455_n21_below_top_slot@{e h c t o +| t < h, h < c +}
  (E : IEM@{e})
  (comp : @Complete@{h h h c}
            (CompHaus@{c h t c _ _ o _ _ _ _ _ _ _ _} : Category@{c h h})) :
  False :=
  CompHaus_not_complete_IEM_below@{e h h c h o _ _ _ _ _ _ _} E comp.

(* CONTROL: the same for [Top]. *)
Definition p455_top_not_complete_index@{r s h o +| s < h +}
  (AI : ArrowIndex@{s h h} Top@{h o}) (comp : @Complete@{r s h h} Top@{h o}) :
  False :=
  Top_not_complete AI comp.

Definition p455_top_not_complete_IEM@{e r s h o +| h <= s +} (E : IEM@{e})
  (comp : @Complete@{r s h h} Top@{h o}) : False :=
  Top_not_complete_IEM E comp.

Fail Definition p455_n11_top_not_complete_IEM_below@{e r s h o +| s < h +}
  (E : IEM@{e}) (comp : @Complete@{r s h h} Top@{h o}) : False :=
  Top_not_complete_IEM E comp.

(* CONTROL: the adjunction refuted under [IEM], applied to GAFT's own
   output; the universal arrow at a large set refuted by an index. *)
Definition p455_adj_refuted_IEM@{e h s +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM E A.

Definition p455_refutes_gaft_output@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) : False :=
  StoneCech_adjunction_refuted_IEM E
    (GAFT_CompHaus_only_complete@{h s _ _ _ _ _ _ _ _} comp).

Definition p455_large_ua_refuted@{c h +} (AI : ArrowIndex@{h c h} CompHaus)
  (UA : UniversalArrow (C:=Sets) (KSet AI) CompHaus_Forget) : False :=
  large_universal_arrow_refuted AI UA.

Definition p455_gaft_vacuous@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) :
  ({ F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } * False)%type :=
  GAFT_CompHaus_IEM_vacuous E comp.

(* CONTROL: with the objects above the homs, the adjunction refuted by an
   arrow index at the hom universe. *)
Definition p455_adj_refuted_index_above@{h s c +| h < c +}
  (AI : ArrowIndex@{h c h} (CompHaus : Category@{c h h}))
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  large_universal_arrow_refuted AI
    (universal_arrow_of_adjunction (`2 A) (KSet AI)).

(* CONTROL: N12's statement, refuted under [IEM] through [Top]'s index. *)
Definition p455_adj_refuted_IEM_above@{e h s c +| h < c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above E A.

Fail Definition p455_n12_adj_refuted_above@{e h s c +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM E A.

(* CONTROL: the same slot by slot, the proof slot at the objects; and
   GAFT's route with the objects above the homs, any solution sets. *)
Definition p455_adj_above_slots@{e h s c o +| h < c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ _ _}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

Definition p455_gaft_vacuous_above@{e h s c +| h < c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h}))
  (sols : ∀ d : obj[Sets@{h s}], SolutionSet CompHaus_Forget d) :
  ({ F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
     & F ⊣ CompHaus_Forget } * False)%type :=
  GAFT_CompHaus_IEM_vacuous_above E comp sols.

Fail Definition p455_n20_adj_above_proof_slot@{e h s c o +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h h _ _ o _ _ _ _ _ _ _ _}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

(* CONTROL: the same with the fourteenth and fifteenth slots, the
   universes of the separating opens of the Hausdorff proof, written out
   at the points' universe o. *)
Definition p455_adj_above_hausdorff_at_o@{e h s c o +| h < c +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ o o}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

Fail Definition p455_n22_hausdorff_opens_below@{e h s c o q +| h < c, q < o +}
  (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus@{c h h c _ _ o _ _ _ _ _ _ q q}
                             : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False :=
  StoneCech_adjunction_refuted_IEM_above@{e h s o c _ _ _ _ _ _ _} E A.

(** ** N13-N17, N19 (UNIVERSE): Instance/Top/StoneCech/Refutations.v, SAFT
       at the inclusion *)

(* CONTROL: [SAFT_CompHaus_Incl], restated; the same body with the objects'
   universe c and the homs' h named apart and nothing declared between
   them; and SAFT at the inclusion at [h < c] with the well-powering a
   hypothesis. *)
Definition p455_saft_incl@{s h +} (comp : @Complete@{s s h h} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_CompHaus_Incl comp cont G.

Definition p455_saft_incl_apart@{s c h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Definition p455_saft_wp_hyp_above@{s c h t +| h < c +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus)
  (WP : WellPowered@{c h h c t} (CompHaus : Category@{c h h})) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G WP.

(* CONTROL: the two vacuity pairs, restated. *)
Definition p455_saft_vacuous@{s c h +} (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_vacuous AI comp cont G WP.

Definition p455_saft_iem_vacuous@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_IEM_vacuous E comp cont G WP.

Definition p455_saft_iem_vacuous_below@{e s c h +| h <= s, s < c +}
  (E : IEM@{e}) (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  SAFT_Incl_IEM_vacuous_below E comp cont G WP.

Fail Definition p455_n13_saft_incl_above@{s c h +| h < c +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Fail Definition p455_n14_saft_incl_below@{s c h +| c < h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Fail Definition p455_n19_saft_wp_below@{s c h +| c < h +}
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus)
  (WP : WellPowered CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G WP.

(* CONTROL: [CompHaus_WellPowered], restated; Structure/WellPowered.v's
   [trivial_small] at [CompHaus] with its objects below its homs; the type
   of a well-powering indexed at the objects' universe, above the homs; the
   inclusion with its objects above its homs. *)
Definition p455_wellpowered@{c h t +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  CompHaus_WellPowered.

Definition p455_trivial_small_below@{c h t +| c < h +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Definition p455_trivial_small_free@{c h t +} :
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Definition p455_wp_type_at_c@{c h t +| h < c +} : Type :=
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}).

Definition p455_incl_above@{c h +| h < c +} :=
  CompHaus_Incl : (CompHaus : Category@{c h h}) ⟶ Top.

Fail Definition p455_n15_wp_type_at_h@{c h t +| h < c +} : Type :=
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}).

Fail Definition p455_n16_trivial_small_at_c@{c h t +| h < c +} :
  WellPowered@{c h h c t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

Fail Definition p455_n17_incl_below@{c h +| c < h +} :=
  CompHaus_Incl : (CompHaus : Category@{c h h}) ⟶ Top.

(** ** N18 (UNIVERSE): Instance/Top/StoneCech/Refutations.v, [big_inj] *)

(* CONTROL: [big_inj_injective], restated; [big_inj]'s body with
   [obj[CompHaus]] written in both places, at [s < c]. *)
Definition p455_big_inj_injective@{r s c h +}
  (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi psi : obj[C] → bool) :
  big_inj comp phi ≈ big_inj comp psi → ∀ j, phi j = psi j :=
  big_inj_injective comp phi psi.

Definition p455_big_inj_unsplit@{r s c h +| s < c +}
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h}))
  (phi : obj[CompHaus] → bool) :=
  continuous_map
    (`1 (unique_obj
           (iprod_desc
              (complete_iprod comp (fun _ : obj[CompHaus] => Bool_CH))
              (fun j => sc_pt_bool (phi j))))) ttt.

Fail Definition p455_n18_big_inj_below@{r s c h +| s < c +}
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h}))
  (phi : obj[CompHaus] → bool) :=
  big_inj comp phi.

(* CONTROL: the cost of a cogenerator with ¬¬-stable members. *)
Definition p455_cogen_dne@{k c h +} (G : Cogenerator@{k c h} CompHaus)
  (stable : ∀ j (a b : top_carrier (`1 (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  CompHaus_cogenerator_stable_DNE G stable.

(* CONTROL: the cost of a single point-separating space with ¬¬-stable
   points. *)
Definition p455_point_sep_dne@{c h +} (K : (CompHaus : Category@{c h h}))
  (sepK : ∀ (Y : (CompHaus : Category@{c h h})) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (stable : ∀ a b : top_carrier (`1 K), ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P :=
  CompHaus_point_separator_stable_DNE K sepK stable.

(** ** Guard block *)

(* Instance/Top/StoneCech.v: 41 names *)
Check @Discrete_Hausdorff.
Check @FinEnum.
Check @Discrete_Compact_of_FinEnum.
Check @FinEnum_of_Discrete_Compact.
Check @sc_nat_setoid.
Check @sc_in_le_fold_max.
Check @nat_not_FinEnum.
Check @Discrete_nat_not_compact.
Check @bool_FinEnum.
Check @Bool_CH.
Check @Point_CH.
Check @Discrete_CH.
Check @sc_fin_unit.
Check @sc_unlift.
Check @sc_fin_ext.
Check @sc_fin_ump.
Check @StoneCech_finite.
Check @StoneCech_finite_obj.
Check @StoneCech_finite_unit.
Check @sc_pt_cone.
Check @sc_pres_pt.
Check @sc_pt_const_med.
Check @sc_pres_map.
Check @CompHaus_Forget_PreservesImageLimit.
Check @taut_sols.
Check @GAFT_CompHaus_only_complete.
Check @unit_injective_of_separated.
Check @separated_of_unit_injective.
Check @sc_chi.
Check @unit_injective_of_dec.
Check @sc_bool_dec.
Check @StoneCech_finite_bool_injective.
Check @KSeparated.
Check @StoneCech_unit_injective_completely_regular.
Check @KSeparated_of_unit_injective.
Check @KSeparated_of_unit_injective_local.
Check @CompHaus_Incl_universal.
Check @CompHaus_Incl_universal_obj.
Check @KSeparated_self.
Check @StoneCech_unit_injective_at_CompHaus.
Check @KSeparated_of_unit_injective_local_at_CompHaus.

(* Instance/Top/StoneCech/Refutations.v: 33 names *)
Check @sc_pt_bool.
Check @sc_eval_pt.
Check @sc_eval_pt_resp.
Check @CompHaus_not_complete.
Check @ObjDecEq_of_IEM.
Check @CompHaus_not_complete_IEM.
Check @Top_not_complete.
Check @Top_not_complete_IEM.
Check @CompHaus_ArrowIndex_of_Top.
Check @CompHaus_not_complete_IEM_below.
Check @CompHaus_not_complete_IEM_above.
Check @KSet.
Check @sc_phi_map.
Check @large_universal_arrow_refuted.
Check @StoneCech_adjunction_refuted_IEM.
Check @StoneCech_adjunction_refuted_IEM_above.
Check @GAFT_CompHaus_IEM_vacuous.
Check @GAFT_CompHaus_IEM_vacuous_above.
Check @CompHaus_WellPowered.
Check @SAFT_CompHaus_Incl.
Check @SAFT_Incl_vacuous.
Check @SAFT_Incl_IEM_vacuous.
Check @SAFT_Incl_IEM_vacuous_below.
Check @big_inj.
Check @big_inj_injective.
Check @sc_yp_equiv.
Check @sc_yp_equiv_Equivalence.
Check @sc_YP.
Check @sc_yp_FinEnum.
Check @YP_CH.
Check @sc_yp_const.
Check @CompHaus_cogenerator_stable_DNE.
Check @CompHaus_point_separator_stable_DNE.
