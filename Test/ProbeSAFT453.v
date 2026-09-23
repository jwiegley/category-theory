(** * Probe for SAFT as a characterization (issue #453)

    Pins the measured boundaries of Adjunction/SAFT/Characterization.v (Mac
    Lane §V.8 Theorem 2, the Lemma inside its proof and the Corollary after
    it, book pp. 129-130; Awodey Remark 9.35; Riehl Theorem 4.7.10,
    Corollary 4.7.13 and the Epilogue's two restatements) and of its three
    satellites Adjunction/SAFT/Characterization/Cover.v,
    Adjunction/SAFT/Characterization/Corollaries.v and
    Adjunction/SAFT/Characterization/Examples.v.  Every negative restates a
    refusal or a readback measured on #453 by its scouts, builders or
    reviews, except N14 (the trivial well-powering at [SAFT_cover_wp_at])
    and N23 (a peel of N22), which are this file's own; N26-N29 are the
    probe review's body-level and [GAFT]-direct forms of N9, N10, N14 and
    N25, numbered after the others so that N1-N25 keep their numbers; N10,
    N20 and N21 pin as refusals three equations first measured as readbacks
    ([About] printing "r = r2", "h = cr" and "su = pa"), and N17 is the
    refusal a scout measured on an unannotated prototype of its own,
    restated at an unannotated wrapper of the library constant.  The
    positive controls restate the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines.  First
    Adjunction/SAFT/Characterization.v's twenty-two lines verbatim and in
    order; then the lines each other target adds, file by file, the target
    modules aside: Cover.v ten, Corollaries.v six and Examples.v thirteen;
    then the four target modules in _CoqProject order.  One supplier module
    is added, immediately before the section that needs it and named there:
    Instance/Sets/SpecialInitial.v before N25 and N29 (its [setsop_comp] and
    [setsop_cog]; Examples.v's header measured N25 with its own import list
    and that file).  So every command above that addition runs under
    exactly the four targets' list.  Structure/Pullback/Wide/Complete.v,
    whose [complete_wide_pullback] is the completeness route of N22-N24,
    was a second addition, before N22, in an earlier revision of this file;
    Adjunction/SAFT/Characterization.v has imported it since its
    [Complete_HasSubobjectWidePullbacks] landed, so it is now one of the
    twenty-two and the addition is gone.  Adjunction/SAFT.v is imported
    after Theory/Subobject.v, so the short name [sub_dom] is
    [SubobjectIndex]'s field and a subobject's is written
    [Subobject.sub_dom], as the targets write it.  Functor/Opposite.v is
    imported after Construction/Opposite.v (Cover.v's list), so [C^op] reads
    as the opposite of a functor unless scoped; N25, N29 and their controls
    write [(Sets@{o so}^op)%category].  A shorter import list is what makes
    a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and each of the fifty-six
    definitions and examples of this file that is not a refutation, wrapped
    in one in a copy of this WHOLE file, stops the build at that command
    with the report that the guarded command had been accepted (fifty-six of
    fifty-six, by a script over the copies); [Print Assumptions] of each of
    the fifty-six, by its fully qualified name, reports "Closed under the
    global context".  Every negative other than that instrument is a
    [Definition] or an [Example], never a [Check], so that an open evar or a
    missing instance cannot satisfy it.  Each negative was stripped of its
    refutation keyword in a copy of this WHOLE file, one at a time,
    compiled, and its error read; the kind recorded is the kind of that
    error, and each has positive controls beside it; every identifier a
    negative uses, its own name and the instrument's absent one aside, is
    used by some positive control of this file (by a script over the
    identifiers of the commands).  In one further copy of this WHOLE file
    each negative other than the instrument was followed by a BINDER
    INSTRUMENT, the same universe binder, arguments and return type with a
    trivial body (a hypothesis of the return type, or [Datatypes.unit] where
    the command states none): twenty-eight of the twenty-nine are accepted,
    and N8's is refused with N8's own text, so every negative but N8 is
    refused by its body.  Every UNIVERSE negative is a top-level definition
    whose universes are declared in its own binder or left to inference,
    never a [Section]'s.  Quotations are Rocq 9.1.1's under this file's
    import list, with the error's environment block left out; Rocq prints
    the "cannot unify" parenthetical with the short names in scope, and a
    universe the stripped copy names after itself and a serial number is
    written <1>, <2>, ..., numbered afresh in each quotation in order of
    first appearance.  The file also compiles on Coq 8.19.2 and 8.20.1,
    against copies of prebuilt trees of this library for those versions in
    which every file of the probe's closure whose source differs from this
    tree's, and every file depending on one, was recompiled in dependency
    order; the stripped copies were compiled there as well.  Every one is
    refused on both at the same line and the same character range.  Under
    8.20.1 every error is the Rocq 9.1.1 one up to the serial numbers
    (compared by a script over the copies).  Under 8.19.2 seventeen are (the
    instrument, N1-N7, N11, N18, N21-N27); N8 names its two universes by
    serial numbers, N9 prints a serial number where Rocq 9.1.1 prints [o],
    and N19's chain names [jo] where Rocq 9.1.1 names a generated universe;
    N10 and N17 print as "cannot unify" mismatches, and N12-N16, N20, N28
    and N29 as type mismatches, those ten with no universe-inconsistency
    clause.

    KINDS.  Thirty refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), CONVERSION (N1-N7,
    N18), TYPING (N21), BINDER (N8, whose error is a universe inconsistency
    raised by its own binder, as its binder instrument shows) and UNIVERSE
    (N9-N17, N19, N20, N22-N29): one, eight, one, one and nineteen.

    LABELS.  The pins carry the N-numbers of this file; the #453 reviews and
    builders asked for them under other names, recorded here so that the
    target headers can cite either: the first review's [r_neg], [r_neg2] and
    [r2_neg] are N1, N2 and N3; its [u_ctrl] is N8 and its [u_ctrl2] N9; its
    [h_large] is N22, [h_ctrl] being the control [p453_hw_at_objects]; the
    second builder's M2, M3, N1, N1w, N2c, N3, T2 and M1b are N6, N7, N11,
    N13, N15, N25, N18 and N19, and its N2, measured against a stub of the
    headline file, is N16; the first builder's [m1_gaft_route_obj],
    [m1_thm2_gaft_obj], [m1_hw_of_complete_large] and [m2_sets_hw_large] are
    N4, N5, N22 and N24, and its readback [m2_r2] is N10's; the second
    review's direct [GAFT] form of N1 is N12, and its [wp_trivial]
    application is the positive control [p453_cover_trivial]; the probe
    review's E1, E6, E2 and E5 are N26, N27, N28 and N29, its E2c is N28's
    control [p453_gaft_trivial_small], and its E7 is the control
    [p453_sets_wp_trivial].  The labels are not constants.

    ** The two left adjoints, read back

    N1-N3 (CONVERSION).  Both left adjoints read back by [eq_refl]:
    [p453_left_obj] and [p453_thm2_left_obj] restate
    Adjunction/SAFT/Characterization.v's [SAFT_left_obj] and
    [SAFT_thm2_left_obj], and [p453_iff_left_obj] and [p453_iff_thm2_obj]
    read the same values through the backward halves of
    [SAFT_wellpowered_iff] and [SAFT_iff].  The readbacks discriminate.  N1,
    the Corollary's value against the comma's cogenerator product itself:
      (cannot unify "fobj[projT1 (SAFT_wellpowered U comp cont G WP)] d" and
      "snd (projT1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator
      U d G)))").
    N2, against the intersection of the EMPTY class [fun _ => False], which
    differs from the readback in that one predicate: the same head and "snd
    (projT1 (Subobject.sub_dom (complete_intersection … False)))))", the
    middle elided here.  N3, Theorem 2's value against the product:
      (cannot unify "fobj[projT1 (SAFT_thm2 U comp cont G HW HU)] d" and
      "snd (projT1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator
      U d G)))").

    N4, N5 (CONVERSION).  The same assembly through Adjunction/GAFT.v's
    [GAFT_from_initials], which ends in [Qed]: the routes are formed
    ([p453_gaft_route], [p453_thm2_gaft_route]), and their readbacks, the
    transparent controls' statements with the route in place of the
    constant, are refused,
      (cannot unify "fobj[projT1 (p453_gaft_route U comp cont G WP)] d" and
      "snd (projT1 (Subobject.sub_dom (complete_intersection … True)))))")
    and
      (cannot unify "fobj[projT1 (p453_thm2_gaft_route U comp cont G HW HU)]
      d" and "WPull (HW … `1 (k)))"),
    the middles elided.  So the transparent assembly of both theorems,
    through Theory/Universal/Arrow.v's
    [LeftAdjointFunctorFromUniversalArrows], is what the readbacks rest on.

    N6, N7 (CONVERSION).  Cover.v's route through [GAFT] IS [GAFT] at its
    solution sets ([p453_cover_is_gaft], restating [SAFT_cover_wp_is_GAFT])
    and agrees with the Corollary's left adjoint up to isomorphism
    ([p453_cover_iso], [SAFT_cover_wp_iso]); N6, the two left adjoints at
    [eq_refl]:
      (cannot unify "projT1 (SAFT_cover_wp U comp cont G WP)" and "projT1
      (SAFT_wellpowered U comp cont G WP)").
    The two routes index the same family ([p453_same_index], restating
    [comma_cogenerator_index]); N7, their products at [eq_refl]:
      (cannot unify "snd (projT1 (cogen_prod (Comma_Complete cont comp)
      (comma_cogenerator U d G)))" and "saft_prod U comp G d").

    ** The regime of the theorems

    N8 (BINDER; an instrument).  [p453_small] and [p453_small_iff] accept
    the Corollary with the homs strictly below the shapes and the shapes
    strictly below the objects ([h < so, so < o, c < so, w < h]), and
    [p453_thm2_small] and [p453_thm2_small_iff] accept Theorem 2 at [h < so,
    so < o, c < so, o < q, h < q].  That the acceptances hold at that
    regime, and not at a collapse of it, is read off [About]: [p453_small]
    keeps [h < so], [so < o], [c < so] and [w < h], [p453_thm2_small] keeps
    [o < q], [h < so], [so < o], [c < so] and [h < q], and neither carries
    an equation.  N8 is the Corollary's command with [so < h], refused over
    the whole command:
      Universe inconsistency. Cannot enforce h <= so because so < h.
    That text is the binder's own: [Complete@{so so h o}] declares [h] at or
    below its first slot (Structure/Complete.v), whatever the body, as
    Test/ProbeSpecialInitial452.v's N4 records, and N8's binder instrument
    is refused with the same text.  What N8 pins is only that a binder's
    constraints are enforced.  [p453_t_below_pa] and [p453_pa_below_t]
    accept the Corollary with [WellPowered]'s [t] and
    [PreservesImageLimit]'s auxiliary [pa] apart in both orders: the "t =
    pa" collapses (a) and (b) Adjunction/SAFT/Characterization.v's header
    records as removed stay removed.  [p453_thm2_q_below_r] accepts Theorem
    2 with the class index strictly below both wide-pullback universes, so
    its collapse (c), "q = r" and "q = rd", stays removed too; and
    [p453_cover_t_below_pa] and [p453_cover_pa_below_t] (placed with the
    controls without a negative) do the same for Cover.v's [saft_cover_at],
    whose readback once carried "t = pa".

    N9 (UNIVERSE).  Theorem 2's class index below the objects, the control
    [p453_thm2_small] differing from it in [o < q] alone:
      The term "HW" has type "HasSubobjectWidePullbacks@{o h q r k} C" while
      it is expected to have type "HasSubobjectWidePullbacks@{o h <1> <2>
      <3>} C" (universe inconsistency: Cannot enforce <1> <= q because q < o
      <= <1>).
    That refusal records [SAFT_thm2]'s own declared bound: its binder
    carries [o <= q], and <1> is its [q].  N26 is the cause at the body.
    [least_index], the corresponding family of the comma's cogenerator
    product, lives at or above the objects ([About least_index]: [o <=
    lq]), and [SAFT_thm2_initial] asks [HW] to intersect it: the same
    application, alone, is accepted with the index at or above the objects
    ([p453_least_index_at_objects], [o <= q]) and N26, at [q < o]:
      The term "least_index U d (cogen_prod (Comma_Complete cont comp)
      (comma_cogenerator U d G))" has type "Type@{<1>}" while it is expected
      to have type "Type@{q}" (universe inconsistency: Cannot enforce <1> <=
      q because q < o <= <1>).

    N10 (UNIVERSE).  [HU]'s C-side wide-pullback universe declared strictly
    above [HW]'s:
      The term "HU" has type "PreservesWidePullbacks@{o h dobj h pw q r2 rd}
      U" while it is expected to have type "PreservesWidePullbacks@{o h dobj
      h <1> q r <2>} U" (universe inconsistency: Cannot enforce r = r2
      because r < r2).
    The control declares [r <= r2] ([p453_thm2_r_le]) and is accepted, the
    equation added.  That refusal records [SAFT_thm2]'s own binder, which
    gives [HW] and [HU] one [r].  N27 is the cause at the body:
    [SAFT_thm2_initial]'s body restated with [HU]'s slot [r2] apart from
    [HW]'s [r] is accepted at [r <= r2] ([p453_thm2_initial_r_le], [About]
    printing "r = r2") and refused at [r < r2] where
    [wide_pullback_is_pullback] hands [HW]'s cone to [HU]:
      The term "wide_pullback_is_pullback (HW ?z0 (∃ y, ?P1 y) (λ k : ∃ y,
      ?P1 y, `1 (k)))" has type "IsWidePullback@{q r o h} …" while it is
      expected to have type "IsWidePullback@{q r2 o h} …" (universe
      inconsistency: Cannot enforce r = r2 because r < r2),
    the arguments elided.  The first builder read "r = r2" back from an
    application of [SAFT_thm2] naming the two apart (the shape of N10's
    control), and the first review fold from [SAFT_thm2_initial]'s restated
    body (the shape of N27's).

    ** Well-poweredness one universe up, at the pin

    N11-N13 (UNIVERSE).  At [Sets@{o so}] without [Untruncate], the
    unconditional well-powerings in tree include two, both indexed strictly
    above the homs [o]: Instance/Sets/WellPowered.v's
    [Sets_WellPoweredAt_up], whose index sits at its own upper universe, and
    Structure/WellPowered.v's [wp_trivial], whose index [SubObj x] sits at
    or above the objects' [so] ([p453_sets_wp_trivial] states it at [so],
    [WellPoweredAt@{so so so o so}]).  Cover.v's [saft_cover_at] accepts
    each ([p453_cover_up] and [p453_sets_cover_trivial], a small
    [Cogenerator] taken as a hypothesis since none is built without
    [Untruncate]), and [saft_solution_set_at] accepts the first, its index
    universe left free ([p453_solution_set_up]).  N11, [SAFT_cover_wp_at],
    whose binder declares [w <= h]:
      The term "Sets_WellPoweredAt_up ?X" has type "WellPoweredAt@{<1> <2>
      <2> <3> <1>} ?X" while it is expected to have type "WellPoweredAt@{<4>
      so <5> o <6>} (saft_prod@{so so o o <7>} Id[Sets@{o so}]
      Sets_Complete@{o so} G d)" (universe inconsistency: Cannot enforce <4>
      = <6> because <4> <= <8> < <6>).
    N11 records that constant's own declared bound; N12 is the same step
    with Adjunction/GAFT.v's [GAFT] applied directly to the solution sets,
    so that the pin is [GAFT]'s:
      The term "saft_solution_set_at Id[Sets] Sets_Complete
      Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up (saft_prod
      Id[Sets] Sets_Complete G d))" has type "SolutionSet@{<1> so so o}
      Id[Sets@{o so}] d" while it is expected to have type "SolutionSet@{o
      so so o} Id[Sets@{o so}] d" (universe inconsistency: Cannot enforce
      <1> = o because o < <2> <= <1>).
    [GAFT]'s solution sets are indexed at the homs.  N13, #451's
    [WellPowered] itself, before any theorem is applied ([p453_wp_up_at] the
    per-object control):
      The term "Sets_WellPoweredAt_up x" has type "WellPoweredAt@{<1> <2>
      <2> o <1>} x" while it is expected to have type "WellPoweredAt@{<3> so
      <4> o <5>} x" (universe inconsistency: Cannot enforce <3> = <5>
      because <3> <= <6> < <5>).
    Under [Untruncate] the small well-powering meets the pin, and both
    routes are accepted ([p453_sets_id], [p453_sets_id_cover]).

    N14, N28 (UNIVERSE).  The cover needs no well-poweredness: at an
    arbitrary complete, continuous, cogenerated [C], Structure/
    WellPowered.v's [wp_trivial], indexed by [SubObj] itself, supplies
    [saft_cover_at]'s datum ([p453_cover_trivial], a POSITIVE control, the
    datum at [wp_trivial]'s own bounds, its index [w] with [o <= w] and [h
    <= w]), so the cover follows from completeness, preservation and the
    cogenerating family.  [SAFT_cover_wp_at] takes [wp_trivial] when the
    objects fit in the homs ([o <= h], [p453_cover_wp_trivial_small]), and
    N14, the same at [h < o]:
      The term "wp_trivial (saft_prod U comp G d)" has type
      "WellPoweredAt@{<1> o <2> h <3>} (saft_prod@{o dobj h h <4>} U comp G
      d)" while it is expected to have type "WellPoweredAt@{<5> o <6> h <7>}
      (saft_prod@{o dobj h h <8>} U comp G d)" (universe inconsistency:
      Cannot enforce <1> = <5> because <5> <= <9> < o <= <1>).
    That refusal records [SAFT_cover_wp_at]'s own declared [w <= h], as
    N11's does.  N28 is the same step with [GAFT] applied directly to the
    solution sets, so that the pin is [GAFT]'s: accepted at [o <= h]
    ([p453_gaft_trivial_small]), and at [h < o]
      The term "saft_solution_set_at U comp cont G d (wp_trivial (saft_prod
      U comp G d))" has type "SolutionSet@{<1> dobj o h} U d" while it is
      expected to have type "SolutionSet@{h dobj o h} U d" (universe
      inconsistency: Cannot enforce <1> = h because h < o <= <2> <= <1>).
    [wp_trivial]'s index is at or above the objects and [GAFT]'s solution
    sets are indexed at the homs: it is at [GAFT]'s pin that
    well-poweredness bites.

    ** The large cogenerating family of [Sets]

    N15, N16 (UNIVERSE).  Instance/Sets/Cogenerator.v's
    [Sets_Cogenerator_large], indexed by all objects, is a [Cogenerator] of
    [Sets] ([p453_large_cog]), and the Corollary takes it over a
    completeness datum whose shape universe is its index universe
    ([p453_large_cog_abstract], the datum a hypothetical variable).  N15,
    through Cover.v's [SAFT_cover_wp], whose [Cogenerator@{h o h}] indexes
    the family at the homs whatever completeness datum is supplied:
      The term "Sets_Cogenerator_large" has type "Cogenerator@{<1> <2> <3>}
      Sets@{<3> <2>}" while it is expected to have type "Cogenerator@{o so
      o} Sets@{o so}" (universe inconsistency: Cannot enforce <3> = o
      because <3> < o).
    and N16, through [SAFT_wellpowered], whose [Cogenerator@{c o h}] carries
    [c <= so], at [Sets_Complete], whose shape universe is the homs:
      The term "Sets_Cogenerator_large" has type "Cogenerator@{<1> <2> <3>}
      Sets@{<3> <2>}" while it is expected to have type "Cogenerator@{<4> so
      o} Sets@{o so}" (universe inconsistency: Cannot enforce <3> = o
      because <3> < <1> <= o).

    ** The binders are load-bearing

    N17 (UNIVERSE).  [p453_unannotated] wraps [SAFT_wellpowered] with no
    universe annotation; minimization then puts the well-powering's index at
    the homs ([About] reads its [WellPowered] with index universe and hom
    universe equal, measured in a scratch file carrying the four targets'
    import list).  The library constant takes Examples.v's index [Set],
    strictly below the homs ([p453_indiscrete_set_index], restating
    [indiscrete_saft]); the wrapper takes the index at the homs
    ([p453_unannotated_hom_index]) and N17, the index at [Set]:
      The term "Indiscrete_WellPowered Type" has type "WellPowered@{o j Set
      o <1>} (Indiscrete@{o j j} Type@{j})" while it is expected to have
      type "WellPowered@{o j j <2> <3>} (Indiscrete@{o j j} Type@{j})"
      (universe inconsistency: Cannot enforce Set = j).
    A scout measured this refusal on an unannotated prototype of its own
    through [GAFT]; the wrapper here is a different constant, with the same
    kind and the same cause.

    ** The cover's lift and the corollaries

    N18 (CONVERSION).  [saft_lift]'s cone takes its [Compose] universe from
    [cont]: the body at [pa] is accepted ([p453_lift_at_pa]), and N18, with
    a universe [pc] strictly above [pa] in its place, is refused by
    conversion, the two types differing in that universe alone:
      (cannot unify "Functor.Compose_obligation_1@{dobj so o pc h} Roof@{so
      h}^op C D U (ASpan@{so o <1> h} (saft_kappa@{o dobj h so dp cp} U comp
      G d c h) (cogen_canonical@{cp so h so o} comp G c))^op" and
      "Functor.Compose_obligation_1@{dobj so o pa h} Roof@{so h}^op C D U
      (ASpan@{so o <1> h} (…) (…))^op"),
    the second term's arguments elided, identical to the first's.

    N19 (UNIVERSE).  Riehl 4.7.13's proviso: the Corollary at [@Diagonal C
    J] is accepted with the shapes at or below the homs ([p453_diag_small]),
    and the diagonal alone with them above ([p453_diag_alone]); N19, the
    Corollary there:
      The term "Diagonal J" has type "@Functor@{o h h <1> <2> <2>} C
      (@Fun@{jo h o h <1> <2> <3>} J C)" while it is expected to have type
      "@Functor@{<4> <5> <5> <6> <5> <5>} ?C ?D" (universe inconsistency:
      Cannot enforce <2> = h because h < <7> <= <2>).
    [Fun J C]'s homs sit at or above [J]'s objects, and the theorem shares
    [C]'s hom universe with [D]'s.

    N20 (UNIVERSE).  [saft_cocomplete]'s colimit-datum universe is the homs,
    inherited from #353's [Diagonal_left_adjoint_HasColimits]: declared at
    or above them ([p453_cocomplete_cr_le]) it is accepted, the equation
    added, and N20, strictly above:
      The term "Diagonal_left_adjoint_HasColimits (projT2 (saft_colim C comp
      G WP J : ∃ L : ([J, C]) ⟶ C, L ⊣ Diagonal J)) F" has type "Colimit@{h
      jo h o} F" while it is expected to have type "Colimit@{cr jo h o} F"
      (universe inconsistency: Cannot enforce h = cr because h < cr).

    N21 (TYPING).  [continuous_Set_functor_representable_iff] carries [su =
    pa] ([About]), [su] the objects of [Sets@{h su}], and
    [continuous_Set_functor_representable] does not: the latter is accepted
    at [pa < su] ([p453_repr_pa_below_su]), the biconditional at [pa <= su]
    ([p453_repr_iff_pa_le_su]), and N21, the biconditional at [pa < su], is
    refused with no parenthetical, the two types differing in
    [PreservesImageLimit]'s seventh universe alone:
      The term "continuous_Set_functor_representable_iff K comp G WP" has
      type "Representable@{<1> <2> su o h} K ↔ PreservesImageLimit@{o h su h
      <3> so su so}" while it is expected to have type "Representable@{ra rt
      su o h} K ↔ PreservesImageLimit@{o h su h pl so pa so}".
    Peeled to its donor, Adjunction/Representability/Sets.v's
    [preserves_image_of_representable], the refusal is by conversion at the
    cone's [Compose] universe, [su] against [pa] (measured in a scratch file
    carrying the four targets' import list); so this is the same
    identification as N18's, and N21 is not reported as a universe
    inconsistency.

    ** Wide pullbacks of subobjects from completeness

    N22-N24 (UNIVERSE).  Completeness supplies
    Adjunction/SAFT/Characterization.v's [HasSubobjectWidePullbacks] when
    the objects fit in the shapes: with the index at the shapes
    ([p453_hw_at_shapes]) and at the objects ([p453_hw_at_objects]), both at
    [o <= so].  The second term IS that file's
    [Complete_HasSubobjectWidePullbacks] at the index at the objects
    ([p453_hw_is_library], by [eq_refl]); N22 and N23 restate the body
    rather than apply the constant, whose binder declares its index at or
    below the shapes ([q <= so]), so that a refusal is the body's and not
    that declaration's.  N22, the second at [so < o], refused at the index
    while instantiating an evar:
      The term "i" has type "?J" while it is expected to have type "I"
      (unable to find a well-typed instantiation for "?J": cannot ensure
      that "Type@{o}" is a subtype of "Type@{<1>}").
    N23 peels it, the family's index given explicitly (control
    [p453_hw_index_ok] at [o <= so]):
      The term "I" has type "Type@{o}" while it is expected to have type
      "Type@{<1>}" (universe inconsistency: Cannot enforce o <= <1> because
      <1> <= <2> < o).
    N24, at [Sets@{o so}], [Sets_Complete]'s shapes at the homs: the index
    at the homs is accepted ([p453_sets_hw_small], and the library constant
    there, [p453_sets_hw_library]) and at the objects refused,
      The term "Subobject.sub_mono (S i)" has type "Subobject.sub_dom (S i)
      ~{ Sets }~> x" while it is expected to have type "?A i ~{ Sets }~> ?z"
      (universe inconsistency: Cannot enforce o = <1> because o < so <= <2>
      <= <1>).
    Where the completeness route does apply, every premise of Theorem 2 is
    inhabited: [p453_thm2_subsets], at the thin [Subsets Y] with [U :=
    InverseImage f], both preservation premises read off
    [image_preimage_adjunction f] itself (so the conclusion was known).
    Adjunction/SAFT/Characterization/Examples.v's
    [subsets_inverse_image_thm2] IS that assembly
    ([p453_thm2_subsets_is_library], by [eq_refl]).

    ** [Sets^op]

    N25, N29 (UNIVERSE).  [Sets^op] is complete and cogenerated
    unconditionally (Instance/Sets/SpecialInitial.v) and co-well-powered
    only one universe up ([Sets_CoWellPoweredAt_up]).  The cover accepts it
    ([p453_setsop_cover_up]); N25, [SAFT_cover_wp_at]:
      The term "Sets_CoWellPoweredAt_up ?X" has type "WellPoweredAt@{<1> <2>
      <2> <3> <1>} ?X" while it is expected to have type "WellPoweredAt@{<4>
      so <5> o <6>} (saft_prod@{so so o o <7>} Id[Sets@{o so}^op]
      setsop_comp@{o so} setsop_cog@{o o so} d)" (universe inconsistency:
      Cannot enforce <4> = <6> because <4> <= <8> < <6>).
    That refusal records [SAFT_cover_wp_at]'s own [w <= h], as N11's does;
    N29 is the [GAFT]-direct form, as N12 is N11's: the solution set is
    accepted ([p453_setsop_solution_set_up]), and handed to [GAFT]
      The term "saft_solution_set_at Id[Sets^op] setsop_comp
      (right_adjoint_PreservesImageLimit adj_id) setsop_cog d
      (Sets_CoWellPoweredAt_up (saft_prod Id[Sets^op] setsop_comp setsop_cog
      d))" has type "SolutionSet@{<1> so so o} Id[Sets@{o so}^op] d" while
      it is expected to have type "SolutionSet@{o so so o} Id[Sets@{o
      so}^op] d" (universe inconsistency: Cannot enforce <1> = o because o <
      <2> <= <1>).

    CONTROLS WITHOUT A NEGATIVE.  The representing object is the left
    adjoint at the singleton ([p453_repr_obj], restating
    [continuous_Set_functor_representable_obj]); the cover's index IS the
    well-powering's name for the pullback subobject ([p453_cover_index],
    restating [saft_cover_at_index]), and the cover takes [t] and [pa] apart
    in both orders ([p453_cover_t_below_pa], [p453_cover_pa_below_t], the
    paragraph on N8); at one tuple at [Id[Sets]] under
    [Untruncate] the reshaped datum holds at every object and the old one is
    refuted ([p453_separation], through [sets_id_cover_separation]); the
    monos lemma at its stated type ([p453_monos_lemma]).

    NOT PINNED HERE.  Refusals the target headers quote that no command of
    this file can restate: Adjunction/SAFT/Characterization.v's "Illegal
    application (Non-functional construction)" with the [Require] of
    Instance/Sets.v dropped (a refusal under a SHORTER import list, which
    this file must not carry), and the collapses its header and Cover.v's
    record as found and removed during the build (readbacks of drafts that
    no longer exist; what is pinned is that (a)-(c) and Cover.v's "t = pa"
    stay removed, by the controls the paragraph on N8 names, and collapse
    (d), "oc = sc" on the comma's unnamed universes, is not pinned).
    Corollaries.v's refusal of [saft_colim] at [h < jo] is its own binder's
    [jo <= h] and is not pinned; N19 is the substantive one.

    The guard block at the end names all ninety-three constants of the four
    target files (forty-seven, twenty-two, eight and sixteen, by [Print
    Module] of each and, the same counts, by the [def] and [prf] entries of
    their .glob files), so that a rename breaks this file.  The two that
    landed after this file was first written, Adjunction/SAFT/
    Characterization.v's [Complete_HasSubobjectWidePullbacks] and
    Examples.v's [subsets_inverse_image_thm2], each have a positive control
    above as well ([p453_hw_is_library] and [p453_sets_hw_library];
    [p453_thm2_subsets_is_library]).  Under the full import list with its
    one addition, [Locate] lists exactly one constant for each of the
    ninety-three names, the target's. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Pullback.Wide.Complete.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Span.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Adjunction.GAFT.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.SAFT.Sets.
Require Import Category.Adjunction.SAFT.WellPowered.
Require Import Category.Adjunction.SAFT.InitialObject.Examples.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Cover.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.
Require Import Category.Adjunction.SAFT.Characterization.Examples.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe453_absent_name.

(** ** N1-N3 (CONVERSION): the two left adjoints read back *)

(* CONTROL: [SAFT_left_obj], restated. *)
Example p453_left_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (SAFT_wellpowered U comp cont G WP)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

(* CONTROL: the same through the backward half of the Corollary's
   biconditional. *)
Example p453_iff_left_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (snd (SAFT_wellpowered_iff U comp G WP) cont)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

Fail Example p453_n1_obj_is_product@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (SAFT_wellpowered U comp cont G WP)] d
    = snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))) :=
  eq_refl.

Fail Example p453_n2_obj_empty_class@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (SAFT_wellpowered U comp cont G WP)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => False))))) :=
  eq_refl.

(* CONTROL: [SAFT_thm2_left_obj], restated. *)
Example p453_thm2_left_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (SAFT_thm2 U comp cont G HW HU)] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

(* CONTROL: the same through the backward half of Theorem 2's
   biconditional. *)
Example p453_iff_thm2_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (snd (SAFT_iff U comp G HW) (cont, HU))] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

Fail Example p453_n3_thm2_obj_is_product@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (SAFT_thm2 U comp cont G HW HU)] d
    = snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))) :=
  eq_refl.

(** ** N4, N5 (CONVERSION): the same readbacks through [GAFT_from_initials] *)

(* CONTROL: the route through Adjunction/GAFT.v's [Qed] assembly is
   formed, for the Corollary ... *)
Definition p453_gaft_route@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT_from_initials U (SAFT_comma_initial U comp cont G WP).

(* ... and for Theorem 2. *)
Definition p453_thm2_gaft_route@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT_from_initials U (SAFT_thm2_initial U comp cont G HW HU).

Fail Example p453_n4_gaft_route_obj@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  fobj[`1 (p453_gaft_route U comp cont G WP)] d
    = snd (`1 (Subobject.sub_dom
        (complete_intersection (Comma_Complete cont comp)
           (wp_class_family
              (comma_WellPoweredAt U d (complete_pullbacks comp)
                 (cogen_prod (Comma_Complete cont comp)
                    (comma_cogenerator U d G))
                 (WP _))
              (fun _ => True))))) :=
  eq_refl.

Fail Example p453_n5_thm2_gaft_route_obj@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  fobj[`1 (p453_thm2_gaft_route U comp cont G HW HU)] d
    = WPull (HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                              (comma_cogenerator U d G))))
                (least_index U d
                   (cogen_prod (Comma_Complete cont comp)
                      (comma_cogenerator U d G)))
                (fun k => `1 k)) :=
  eq_refl.

(** ** N6, N7 (CONVERSION): the cover's route and the comma's product *)

(* CONTROL: [SAFT_cover_wp_is_GAFT], restated. *)
Example p453_cover_is_gaft@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP
    = GAFT U comp cont
        (fun d => saft_solution_set_at@{o dobj h h dp cp w s t pl pa h _ _ _}
                    U comp cont G d
                    (WP (saft_prod@{o dobj h h dp} U comp G d))) :=
  eq_refl.

(* CONTROL: the two left adjoints are isomorphic ([SAFT_cover_wp_iso]). *)
Definition p453_cover_iso@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  projT1 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP)
    ≈ projT1 (SAFT_wellpowered U comp cont G WP) :=
  SAFT_cover_wp_iso U comp cont G WP.

Fail Example p453_n6_routes_convertible@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  projT1 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP)
    = projT1 (SAFT_wellpowered U comp cont G WP) :=
  eq_refl.

(* CONTROL: [comma_cogenerator_index], restated: the two routes index the
   same family. *)
Example p453_same_index@{o dobj h so +| h <= so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (G : Cogenerator@{so o h} C) :
  cog_index (comma_cogenerator U d G) = saft_index U G d :=
  eq_refl.

Fail Example p453_n7_same_product@{o dobj h so dp pk pa +|
    h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{so o h} C) :
  snd (`1 (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G)))
    = saft_prod@{o dobj h so dp} U comp G d :=
  eq_refl.

(** ** N8-N10, N26, N27 (BINDER, UNIVERSE): the regime of the theorems *)

(* CONTROL: the Corollary with the homs strictly below the shapes and the
   shapes strictly below the objects. *)
Definition p453_small@{o dobj h so c w s t pk pa +|
    h < so, so < o, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* CONTROL: its biconditional at the same universes. *)
Definition p453_small_iff@{o dobj h so c w s t pk pa +|
    h < so, so < o, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ @PreservesImageLimit@{o h dobj h pk so pa so} C D U :=
  SAFT_wellpowered_iff U comp G WP.

(* CONTROL: [WellPowered]'s [t] and [PreservesImageLimit]'s auxiliary
   [pa] apart, in both orders. *)
Definition p453_t_below_pa@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, t < pa +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

Definition p453_pa_below_t@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, pa < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* INSTRUMENT: the binder's constraints are enforced.  [Complete@{so so h
   o}] declares [h] at or below its first slot, so this is refused
   whatever the body. *)
Fail Definition p453_n8_shapes_below_homs@{o dobj h so c w s t pk pa +|
    so < h, c < so, w < h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* CONTROL: Theorem 2 at the same regime, the class index strictly above
   the objects. *)
Definition p453_thm2_small@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, o < q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(* CONTROL: its biconditional at the same universes. *)
Definition p453_thm2_small_iff@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, o < q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ (@PreservesImageLimit@{o h dobj h pk so pa so} C D U
       * PreservesWidePullbacks@{o h dobj h pw q r rd} U) :=
  SAFT_iff U comp G HW.

(* CONTROL: Theorem 2 with the class index strictly below both
   wide-pullback universes, [q < r] and [q < rd]. *)
Definition p453_thm2_q_below_r@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q, q < r, q < rd +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

Fail Definition p453_n9_class_index_small@{o dobj h so c pk pa q r rd pw k +|
    h < so, so < o, c < so, q < o, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(* CONTROL: [HU]'s C-side wide-pullback universe [r2] declared at or
   above [HW]'s [r]. *)
Definition p453_thm2_r_le@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r <= r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

Fail Definition p453_n10_thm2_r_apart@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r < r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_thm2 U comp cont G HW HU.

(* CONTROL: N26's term, [HW] applied to the corresponding family
   [least_index] of the comma's cogenerator product, the class index at or
   above the objects. *)
Definition p453_least_index_at_objects@{o dobj h so c pk pa q r k +|
    h < so, so < o, c < so, o <= q, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) (d : D) :=
  HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))))
     (least_index U d (cogen_prod (Comma_Complete cont comp)
                         (comma_cogenerator U d G)))
     (fun k => `1 k).

Fail Definition p453_n26_least_index_small@{o dobj h so c pk pa q r k +|
    h < so, so < o, c < so, q < o, h < q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) (d : D) :=
  HW (snd (`1 (cogen_prod (Comma_Complete cont comp)
                 (comma_cogenerator U d G))))
     (least_index U d (cogen_prod (Comma_Complete cont comp)
                         (comma_cogenerator U d G)))
     (fun k => `1 k).

(* CONTROL: [SAFT_thm2_initial]'s body, [HU]'s C-side wide-pullback
   universe [r2] declared at or above [HW]'s [r]. *)
Definition p453_thm2_initial_r_le@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r <= r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) (d : D) :
  @Initial (=(d) ↓ U) :=
  special_initial_object_least (Comma_Complete cont comp)
    (comma_cogenerator U d G)
    (@least_sub C D U d
       (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G))
       (HW _ _ (fun k => `1 k))
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k)))))
    (least_le (complete_pullbacks comp)
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k))))).

Fail Definition p453_n27_initial_r_apart@{o dobj h so c pk pa q r r2 rd pw k +|
    h <= so, c <= so, o <= q, h <= q, r < r2 +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r2 rd} U) (d : D) :
  @Initial (=(d) ↓ U) :=
  special_initial_object_least (Comma_Complete cont comp)
    (comma_cogenerator U d G)
    (@least_sub C D U d
       (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G))
       (HW _ _ (fun k => `1 k))
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k)))))
    (least_le (complete_pullbacks comp)
       (HU _ _ _ _ (fun k => Subobject.sub_is_monic (`1 k)) _ _
          (wide_pullback_is_pullback (HW _ _ (fun k => `1 k))))).

(** ** N11-N14, N28 (UNIVERSE): well-poweredness one universe up, at the pin *)

(* CONTROL: at [Sets] with the unconditional well-powering one universe up
   and a small cogenerating family taken as a hypothesis, the cover is
   accepted ... *)
Definition p453_cover_up@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_cover_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G d
    (Sets_WellPoweredAt_up _).

(* ... and so is the solution set built from it, its index universe left
   free. *)
Definition p453_solution_set_up@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_solution_set_at (@Id Sets@{o so}) Sets_Complete
    Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up _).

(* CONTROL: the other unconditional well-powering of [Sets@{o so}],
   Structure/WellPowered.v's [wp_trivial], indexed at the objects' [so],
   strictly above the homs [o] ... *)
Definition p453_sets_wp_trivial@{o so +| o < so +} (d : Sets@{o so}) :
  WellPoweredAt@{so so so o so} d :=
  wp_trivial d.

(* ... and the cover accepts it too. *)
Definition p453_sets_cover_trivial@{o so +| o < so +} (d : Sets@{o so})
  (G : Cogenerator@{o so o} Sets@{o so}) :=
  saft_cover_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G d
    (wp_trivial _).

Fail Definition p453_n11_cover_wp_at_up@{o so +| o < so +}
  (G : Cogenerator@{o so o} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_cover_wp_at (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit G
    (fun d => Sets_WellPoweredAt_up _).

Fail Definition p453_n12_gaft_at_up@{o so +| o < so +}
  (G : Cogenerator@{o so o} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  GAFT (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (fun d => saft_solution_set_at (@Id Sets@{o so}) Sets_Complete
                Sets_Id_PreservesImageLimit G d (Sets_WellPoweredAt_up _)).

(* CONTROL: the well-powering one universe up, per object. *)
Definition p453_wp_up_at@{o so +| o < so +} (x : Sets@{o so}) :=
  Sets_WellPoweredAt_up x.

Fail Definition p453_n13_wp_up@{o so +| o < so +} : WellPowered Sets@{o so} :=
  fun x => Sets_WellPoweredAt_up x.

(* CONTROL: under [Untruncate] the small well-powering meets the pin, and
   both routes are accepted ([sets_id_saft], [sets_id_saft_cover]). *)
Definition p453_sets_id@{o so +| Set < o, o < so +} (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_wellpowered (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

Definition p453_sets_id_cover@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_cover_wp (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    (Sets_Cogenerator_untruncate Un) (Sets_WellPowered_untruncate Un).

(* POSITIVE CONTROL: the cover needs no well-poweredness at all.  At an
   arbitrary complete, continuous, cogenerated [C], Structure/
   WellPowered.v's [wp_trivial], indexed by [SubObj] itself, supplies the
   datum, at [w s t] with [wp_trivial]'s own bounds: its index [w] at or
   above the objects. *)
Definition p453_cover_trivial@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= w, h <= w, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) :=
  saft_cover_at U comp cont G d
    (wp_trivial@{o h w s t} (saft_prod U comp G d)).

(* CONTROL: [GAFT]'s pin takes [wp_trivial] when the objects fit in the
   homs. *)
Definition p453_cover_wp_trivial_small@{o dobj h dp cp s t pl pa +|
    o <= h, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_cover_wp_at U comp cont G (fun d => wp_trivial (saft_prod U comp G d)).

Fail Definition p453_n14_cover_wp_trivial_large@{o dobj h dp cp s t pl pa +|
    h < o, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_cover_wp_at U comp cont G (fun d => wp_trivial (saft_prod U comp G d)).

(* CONTROL: N28's term, [GAFT] applied directly to the solution sets built
   from [wp_trivial], when the objects fit in the homs. *)
Definition p453_gaft_trivial_small@{o dobj h dp cp pl pa +|
    o <= h, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont
    (fun d => saft_solution_set_at U comp cont G d
                (wp_trivial (saft_prod U comp G d))).

Fail Definition p453_n28_gaft_trivial_large@{o dobj h dp cp pl pa +|
    h < o, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont
    (fun d => saft_solution_set_at U comp cont G d
                (wp_trivial (saft_prod U comp G d))).

(** ** N15, N16 (UNIVERSE): the large cogenerating family of [Sets] *)

(* CONTROL: the family itself. *)
Definition p453_large_cog@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so} :=
  Sets_Cogenerator_large@{c o so}.

(* CONTROL: the Corollary takes it over a completeness datum whose shape
   universe is the family's index universe, a hypothetical datum taken as
   a variable ([Sets_Complete] is [Complete@{o o o so}]). *)
Definition p453_large_cog_abstract@{c o so w s t pk pa +|
    o < so, o < c, w <= o, so <= s, o <= s, o < t +}
  (comp : @Complete@{c c o so} Sets@{o so})
  (cont : @PreservesImageLimit@{so o so o pk c pa c} Sets@{o so} Sets@{o so}
            (@Id Sets@{o so}))
  (WP : WellPowered@{so o w s t} Sets@{o so}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ @Id Sets@{o so} } :=
  SAFT_wellpowered (@Id Sets@{o so}) comp cont Sets_Cogenerator_large@{c o so}
    WP.

Fail Definition p453_n15_large_cog_cover@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_cover_wp (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    Sets_Cogenerator_large (Sets_WellPowered_untruncate Un).

Fail Definition p453_n16_large_cog_comma@{o so +| Set < o, o < so +}
  (Un : Untruncate@{o}) :
  { F : Sets@{o so} ⟶ Sets@{o so} & F ⊣ Id } :=
  SAFT_wellpowered (@Id Sets@{o so}) Sets_Complete Sets_Id_PreservesImageLimit
    Sets_Cogenerator_large (Sets_WellPowered_untruncate Un).

(** ** N17 (UNIVERSE): the binders are load-bearing *)

(* An unannotated wrapper of [SAFT_wellpowered]: minimization sets the
   well-powering's index universe to the homs. *)
Definition p453_unannotated {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (cont : @PreservesImageLimit C D U)
  (G : Cogenerator C) (WP : WellPowered C) : { F : D ⟶ C & F ⊣ U } :=
  SAFT_wellpowered U comp cont G WP.

(* CONTROL: the library constant takes the index at [Set], strictly below
   the homs ([indiscrete_saft], restated). *)
Definition p453_indiscrete_set_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  SAFT_wellpowered (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j Set o _} Type@{j}).

(* CONTROL: the wrapper takes the index at the homs. *)
Definition p453_unannotated_hom_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  p453_unannotated (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j j o _} Type@{j}).

Fail Definition p453_n17_unannotated_set_index@{j o +| j < o +} :
  { F : Indiscrete@{o j j} Type@{j} ⟶ Indiscrete@{o j j} Type@{j}
    & F ⊣ @Id (Indiscrete@{o j j} Type@{j}) } :=
  p453_unannotated (@Id (Indiscrete@{o j j} Type@{j}))
    (Indiscrete_Complete (Datatypes.unit : Type@{j}))
    (right_adjoint_PreservesImageLimit (@adj_id (Indiscrete@{o j j} Type@{j})))
    (Indiscrete_Cogenerator_empty Type@{j})
    (Indiscrete_WellPowered@{o j Set o _} Type@{j}).

(** ** N18 (CONVERSION): the lift's [Compose] universe is [cont]'s *)

(* CONTROL: [saft_lift]'s body, the cone at [pa]. *)
Definition p453_lift_at_pa@{o dobj h so dp cp pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  d ~> U (Subobject.sub_dom
           (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)) :=
  unique_obj (cont _ _ _ (saft_pb_cone@{o dobj h so dp cp pl pa so pa _}
                            U comp cont G d c h)).

Fail Definition p453_n18_lift_at_pc@{o dobj h so dp cp pl pa pc +|
    h <= so, h < dp, h < cp, h < pc, pa < pc +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  d ~> U (Subobject.sub_dom
           (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)) :=
  unique_obj (cont _ _ _ (saft_pb_cone@{o dobj h so dp cp pl pa so pc _}
                            U comp cont G d c h)).

(** ** N19-N21 (UNIVERSE, TYPING): the corollaries' universes *)

(* CONTROL: the Corollary at the diagonal, shapes at or below the homs. *)
Definition p453_diag_small@{o h so c w s t jo +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h +}
  (C : Category@{o h h}) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C)
  (J : Category@{jo h h}) :=
  SAFT_wellpowered (@Diagonal C J) comp
    (Continuous_PreservesImageLimit Diagonal_continuous) G WP.

(* CONTROL: the diagonal alone, shapes strictly above the homs. *)
Definition p453_diag_alone@{o h jo +| h < jo +}
  (C : Category@{o h h}) (J : Category@{jo h h}) :=
  @Diagonal C J.

Fail Definition p453_n19_diag_large@{o h so c w s t jo +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < jo +}
  (C : Category@{o h h}) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C)
  (J : Category@{jo h h}) :=
  SAFT_wellpowered (@Diagonal C J) comp
    (Continuous_PreservesImageLimit Diagonal_continuous) G WP.

(* CONTROL: [saft_cocomplete]'s body with a colimit-datum universe [cr]
   declared at or above the homs. *)
Definition p453_cocomplete_cr_le@{o h so c w s t jo fo fa cr +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa, h <= cr, jo <= cr +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @Cocomplete@{cr jo h o} C :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (saft_colim C comp G WP J
                        : { L : @Fun@{jo h o h fo h fa} J C ⟶ C
                          & L ⊣ @Diagonal@{fo h fa jo o h} C J })) F.

Fail Definition p453_n20_cocomplete_cr_above@{o h so c w s t jo fo fa cr +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa, h < cr, jo <= cr +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @Cocomplete@{cr jo h o} C :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (saft_colim C comp G WP J
                        : { L : @Fun@{jo h o h fo h fa} J C ⟶ C
                          & L ⊣ @Diagonal@{fo h fa jo o h} C J })) F.

(* CONTROL: the representability corollary with [PreservesImageLimit]'s
   auxiliary [pa] strictly below the objects [su] of [Sets@{h su}]. *)
Definition p453_repr_pa_below_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K :=
  continuous_Set_functor_representable K comp cont G WP.

(* CONTROL: its biconditional with [pa] declared at or below [su]. *)
Definition p453_repr_iff_pa_le_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa <= su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K
    ↔ @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K :=
  continuous_Set_functor_representable_iff K comp G WP.

Fail Definition p453_n21_repr_iff_pa_below_su@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su, pa < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K
    ↔ @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K :=
  continuous_Set_functor_representable_iff K comp G WP.

(** ** N22-N24 (UNIVERSE): wide pullbacks of subobjects from completeness *)

(* CONTROL: completeness supplies them with the index at the shapes, the
   objects at or below the shapes. *)
Definition p453_hw_at_shapes@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h so so k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(* CONTROL: and with the index at the objects, when they fit. *)
Definition p453_hw_at_objects@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h o o k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(* CONTROL: Adjunction/SAFT/Characterization.v's
   [Complete_HasSubobjectWidePullbacks], at the index at the objects, IS
   that term. *)
Example p453_hw_is_library@{o h so k +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  (Complete_HasSubobjectWidePullbacks comp
     : HasSubobjectWidePullbacks@{o h o o k} C)
    = p453_hw_at_objects comp :=
  eq_refl.

Fail Definition p453_n22_hw_large@{o h so k +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h o o k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(* CONTROL: N23's term, the family's index explicit, at the objects'
   universe, when the objects fit in the shapes. *)
Definition p453_hw_index_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) (x : C)
  (I : Type@{o}) (S : I → SubObj x) :=
  @complete_wide_pullback C comp I (fun i => Subobject.sub_dom (S i)) x
    (fun i => Subobject.sub_mono (S i)).

Fail Definition p453_n23_hw_large_index@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) (x : C)
  (I : Type@{o}) (S : I → SubObj x) :=
  @complete_wide_pullback C comp I (fun i => Subobject.sub_dom (S i)) x
    (fun i => Subobject.sub_mono (S i)).

(* CONTROL: at [Sets], the index at the homs. *)
Definition p453_sets_hw_small@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o o o k} Sets@{o so} :=
  fun x I S => complete_wide_pullback Sets_Complete
                 (fun i => Subobject.sub_mono (S i)).

(* CONTROL: the library constant there, the index at the homs. *)
Definition p453_sets_hw_library@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o o o k} Sets@{o so} :=
  Complete_HasSubobjectWidePullbacks Sets_Complete.

Fail Definition p453_n24_sets_hw_large@{o so k +| Set < o, o < so +} :
  HasSubobjectWidePullbacks@{so o so so k} Sets@{o so} :=
  fun x I S => complete_wide_pullback Sets_Complete
                 (fun i => Subobject.sub_mono (S i)).

(* POSITIVE CONTROL: every premise of Theorem 2 at the thin [Subsets Y],
   [U := InverseImage f]; both preservation premises come from
   [image_preimage_adjunction f] itself. *)
Definition p453_thm2_subsets@{o u so k +| o <= u, u <= so, o <= so +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets}~> Y) :
  { F : Subsets@{o u} X ⟶ Subsets@{o u} Y & F ⊣ InverseImage f } :=
  SAFT_thm2 (InverseImage f) (Subsets_Complete_free Y)
    (right_adjoint_PreservesImageLimit (image_preimage_adjunction f))
    (Subsets_Cogenerator_empty Y)
    (p453_hw_at_shapes (Subsets_Complete_free Y))
    (right_adjoint_PreservesWidePullbacks (image_preimage_adjunction f)).

(* CONTROL: Adjunction/SAFT/Characterization/Examples.v's
   [subsets_inverse_image_thm2] IS that assembly. *)
Example p453_thm2_subsets_is_library@{o so u +| Set < o, o < so, o <= u +}
  {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y) :
  subsets_inverse_image_thm2 f
    = (p453_thm2_subsets f
       : { F : Subsets@{o u} X ⟶ Subsets@{o u} Y & F ⊣ InverseImage f }) :=
  eq_refl.

(** ** N25, N29 (UNIVERSE): [Sets^op], co-well-powered one universe up *)

Require Import Category.Instance.Sets.SpecialInitial.

(* CONTROL: the cover is accepted there. *)
Definition p453_setsop_cover_up@{o so +| o < so +}
  (d : (Sets@{o so}^op)%category) :=
  saft_cover_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog d (Sets_CoWellPoweredAt_up _).

Fail Definition p453_n25_setsop_cover_wp_at_up@{o so +| o < so +} :
  { F : (Sets@{o so}^op)%category ⟶ (Sets@{o so}^op)%category & F ⊣ Id } :=
  SAFT_cover_wp_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog (fun d => Sets_CoWellPoweredAt_up _).

(* CONTROL: N29's solution set, not handed to [GAFT]. *)
Definition p453_setsop_solution_set_up@{o so +| o < so +}
  (d : (Sets@{o so}^op)%category) :=
  saft_solution_set_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    setsop_cog d (Sets_CoWellPoweredAt_up _).

Fail Definition p453_n29_setsop_gaft_up@{o so +| o < so +} :
  { F : (Sets@{o so}^op)%category ⟶ (Sets@{o so}^op)%category & F ⊣ Id } :=
  GAFT (@Id ((Sets@{o so}^op)%category)) setsop_comp
    (right_adjoint_PreservesImageLimit (@adj_id ((Sets@{o so}^op)%category)))
    (fun d =>
       saft_solution_set_at (@Id ((Sets@{o so}^op)%category)) setsop_comp
         (right_adjoint_PreservesImageLimit
            (@adj_id ((Sets@{o so}^op)%category)))
         setsop_cog d (Sets_CoWellPoweredAt_up _)).

(** ** Controls without a negative *)

(* The representing object is the left adjoint at the singleton
   ([continuous_Set_functor_representable_obj], restated). *)
Example p453_repr_obj@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @repr_obj C K
    (continuous_Set_functor_representable K comp cont G WP
       : Representable@{ra rt su o h} K)
    = fobj[projT1 (SAFT_wellpowered K comp cont G WP)] SetsOne :=
  eq_refl.

(* The cover's index at [h] IS the well-powering's name for the pullback
   subobject ([saft_cover_at_index], restated). *)
Example p453_cover_index@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d))
  (c : C) (h : d ~> U c) :
  projT1 (saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _}
            U comp cont G d W c h)
    = wp_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h) :=
  eq_refl.

(* The cover with the well-powering's [t] and [PreservesImageLimit]'s
   auxiliary [pa] apart, in both orders. *)
Definition p453_cover_t_below_pa@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= s, h <= s, h < t, t < pa +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :=
  saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _} U comp cont G d W.

Definition p453_cover_pa_below_t@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp, o <= s, h <= s, h < t, pa < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :=
  saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _} U comp cont G d W.

(* At one tuple at [Id[Sets]] under [Untruncate], the reshaped covering
   datum holds at every object and the old one is refuted. *)
Definition p453_separation@{o so t +| Set < o, o < so, o < t +}
  (Un : Untruncate@{o}) :
  (∀ d : Sets@{o so},
     SubobjectCoverAt (@Id Sets@{o so}) Sets_Complete
       (Sets_Cogenerator_untruncate Un) d
       (Sets_WellPowered_untruncate@{o so t} Un _))
  * (SubobjectCover (@Id Sets@{o so}) Sets_Complete
       (Sets_Cogenerator_untruncate Un)
       (WellPowered_SubobjectIndex (Sets_WellPowered_untruncate@{o so t} Un))
     → False) :=
  sets_id_cover_separation Un.

(* The monos lemma over pullbacks in [C], at its stated type. *)
Definition p453_monos_lemma@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  Monic m ↔ Monic (snd (`1 m)) :=
  comma_monic_iff_underlying_monic HP m.

(** ** Guard block *)

Check @comma_monic_of_underlying.
Check @kp_diag.
Check @kp_diag_fst.
Check @kp_diag_snd.
Check @kp_obj.
Check @kp_fst.
Check @kp_snd.
Check @underlying_monic_of_comma_monic.
Check @comma_monic_iff_underlying_monic.
Check @comma_cogenerator.
Check @comma_wp_index.
Check @comma_wp_dom.
Check @comma_wp_mono.
Check @comma_wp_to.
Check @underlying_sub.
Check @comma_wp_from.
Check @comma_wp_iso_to.
Check @comma_wp_iso_from.
Check @comma_wp_to_from.
Check @comma_WellPoweredAt.
Check @comma_WellPowered.
Check @SAFT_comma_initial.
Check @SAFT_universal_arrow.
Check @SAFT_left.
Check @SAFT_adjunction.
Check @SAFT_wellpowered.
Check @SAFT_left_obj.
Check @SAFT_wellpowered_iff.
Check @HasSubobjectWidePullbacks.
Check @Complete_HasSubobjectWidePullbacks.
Check @least_index.
Check @least_top.
Check @least_lift.
Check @least_lift_commutes.
Check @least_dom.
Check @least_mono.
Check @least_sub.
Check @least_index_of.
Check @least_le.
Check @SAFT_thm2_initial.
Check @SAFT_thm2_universal_arrow.
Check @SAFT_thm2_left.
Check @SAFT_thm2_adjunction.
Check @SAFT_thm2.
Check @SAFT_thm2_left_obj.
Check @right_adjoint_PreservesWidePullbacks.
Check @SAFT_iff.
Check @image_family_cone.
Check @saft_index.
Check @saft_fam.
Check @saft_prod_limit.
Check @saft_prod.
Check @saft_point.
Check @saft_point_commutes.
Check @saft_kappa.
Check @saft_square.
Check @saft_sub.
Check @saft_sub_to.
Check @saft_pb_cone.
Check @saft_lift.
Check @saft_lift_commutes.
Check @SubobjectCoverAt.
Check @saft_cover_at.
Check @saft_solution_set_at.
Check @SAFT_cover_wp_at.
Check @SAFT_cover_wp.
Check @saft_cover_at_index.
Check @saft_solution_set_at_index.
Check @SAFT_cover_wp_is_GAFT.
Check @continuous_Set_functor_representable.
Check @continuous_Set_functor_representable_obj.
Check @continuous_Set_functor_representable_iff.
Check @continuous_Set_functor_representable_at.
Check @saft_colim.
Check @saft_cocomplete.
Check @SAFT_cover_wp_iso.
Check @comma_cogenerator_index.
Check @sets_id_saft.
Check @sets_id_saft_cover.
Check @sets_id_new_cover.
Check @sets_id_old_cover_refuted.
Check @sets_id_cover_separation.
Check @sets_hom_saft.
Check @sets_id_repr_saft.
Check @sets_hom_repr_saft.
Check @sets_saft_cocomplete.
Check @subsets_inverse_image_saft.
Check @subsets_inverse_image_thm2.
Check @subsets_saft_cocomplete.
Check @indiscrete_saft.
Check @indiscrete_saft_cocomplete.
Check @sets_id_saft_iso.
Check @subsets_inverse_image_saft_iso.
