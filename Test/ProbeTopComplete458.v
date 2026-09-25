(** * Probe for Mac Lane V.9's Remarks 1 and 2 and Exercise 3 (issue #458)

    Pins the measured boundaries of the six files #458 adds for Mac Lane
    §V.9, book pp. 133-136 (catalog ids maclane:V.9:remark1, that Top is
    complete; maclane:V.9:remark2, that it is cocomplete; and
    maclane:V.9:ex3, products through the functor G_* a functor induces
    on categories of cones; the book numbers neither remark, and the ids
    are names, not book numbering), and for the items appended to the
    issue: Awodey §2.6 (awodey:2.6:construction-product-top), Riehl §3.1
    Example 3.1.10 (riehl:3.1:example10, the box topology a non-example),
    Riehl §3.6 Proposition 3.6.2 (riehl:3.6:prop2, the underlying-set
    functor continuous and cocontinuous) and Riehl §3.6 Example 3.6.3
    (riehl:3.6:example3, the recipe as a lemma, both halves).  The targets
    are Instance/Top/Complete.v (the initial topology [PInit], the recipe
    for limits, products, [PTop_Complete] and the book's route to it),
    with its satellites Instance/Top/Complete/ConeComma.v (Exercise 3,
    corrected to a RIGHT adjoint of G_*: (a) as printed is refuted, and
    (b)'s left adjoint exists but is the discrete one) and Instance/Top/
    Complete/Refutations.v (where completeness stops, over [PTopCat] and
    over the Type-valued [Top] below its homs); and Instance/Top/
    Cocomplete.v (the final topology [PFinal], the recipe for colimits,
    coproducts, [PTop_Cocomplete] and the book's route to it), with its
    satellites Instance/Top/Cocomplete/Refutations.v (where
    cocompleteness stops) and Instance/Top/Cocomplete/TypeValued.v (what
    is formable over the Type-valued [Top] of Instance/Top.v, and the
    three walls that stop the rest).  The positive results are over
    Instance/Top/Prop.v's Prop-valued [PTopCat], by the maintainer's
    decision of 2026-09-24 on #458.  N2-N4, N8-N14, N16-N22 and N27-N35
    restate a refusal that a target header records, measured by #458's
    builders and reviews in scratch files or in this file; N1, N5-N7,
    N15 and N23-N26 are this file's own.  The positive controls restate
    the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines by script.
    First Instance/Top/Complete.v's twenty-two lines verbatim and in
    order, then that file; then the seven lines Instance/Top/Complete/
    ConeComma.v adds, in its order (Structure/Terminal.v, Structure/Limit/
    Comparison.v, Instance/Cones.v, Instance/Cones/Limit.v,
    Instance/Discrete.v, Instance/One.v, Instance/Roof.v), and the
    satellite; then the six lines Instance/Top/Complete/Refutations.v
    adds (Structure/Complete/Freyd.v, Construction/Quotient.v,
    Instance/Sets/Classifier/OneLevel.v, Instance/Top.v,
    Instance/Top/CompHaus.v, Instance/Top/StoneCech/Refutations.v) and
    the satellite; then the six lines Instance/Top/Cocomplete.v adds
    (Functor/Opposite.v, Construction/Opposite.v, Structure/Limit/
    Coproduct.v, Structure/Coequalizer.v, Instance/Sets/Cocomplete.v,
    Instance/Sets/Coequalizer.v) and that file; then the one line
    Instance/Top/Cocomplete/Refutations.v adds (Construction/Product/
    Limit.v; its [From Coq Require Import Eqdep_dec] loads the module
    Instance/Top/Complete.v already requires as [Coq.Logic.Eqdep_dec],
    and it requires Instance/Top/Complete/Refutations.v, already above)
    and the satellite; then the one line Instance/Top/Cocomplete/
    TypeValued.v adds (Instance/Top/Subspace/TypeValued.v) and the
    satellite.  Forty-nine lines: the forty-six distinct [Require]s of
    the six targets and the three targets no other target requires.  A
    shorter import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of
    an absent name is refused for that reason ("The reference
    probe458_absent_name was not found in the current environment."),
    and each of the one hundred and one definitions, examples, lemmas and
    inductives of this file that is not a refutation (eighty-one,
    seventeen, one and two), wrapped in one in a copy of this WHOLE file,
    stops the build at that command with the report that the guarded
    command had been accepted (one hundred and one of one hundred and
    one, by a script over the copies).  Every negative other than that
    instrument is a [Definition], an [Example] or an [Inductive], never a
    [Check], so that an open evar cannot satisfy it.  Each negative was
    stripped of its refutation keyword in a copy of this WHOLE file, one
    at a time, compiled, and its error read; each of the thirty-six
    copies stops inside the stripped command (by the File line that
    precedes its error, compared by a script with the command's extent).
    The kind recorded is the kind of that error, and each negative has
    positive controls beside it; every identifier a negative uses, its
    own name, the constructors it declares and the universes its binder
    names aside, is used by some positive control of this file (by a
    script over the identifiers of the commands, the guard block not
    counted).  In one further copy of this WHOLE file, each negative but
    the instrument and N17 was followed by a BINDER INSTRUMENT, the same
    universe binder, binders and return type with a hypothesis of the
    return type as its body (for N19, the same arity with no
    constructors): all thirty-four are accepted, so every negative is
    refused by its body, never by its statement.  N17 has neither binder
    nor type.  And each of the thirteen UNIVERSE negatives whose binder
    declares the constraint that separates it from a control, N1-N4,
    N8-N12, N15, N29, N31 and N32, was rewritten in one copy of this
    WHOLE file with its refutation keyword removed AND that constraint
    deleted, the "+" kept: the copy compiles, so each of the thirteen is
    refused exactly because of the declared constraint.  The separating
    constraint of N16-N20 is [o < h], which Instance/Top.v's [Top@{h o}]
    carries itself, and N24-N28, N30 and N33-N35 separate by an instance
    equation, not a constraint (N30, N33 and N34 by an explicit universe
    instance of the refutation they read).  Every UNIVERSE negative is a
    top-level command whose universes are declared in its own binder,
    never a [Section]'s, but N17, which declares none.  Quotations are
    Rocq 9.1.1's under this file's import list, with the error's
    environment block left out; Rocq prints the "cannot unify"
    parenthetical with the short names in scope, and a universe the
    stripped copy names after itself and a serial number is written <1>,
    <2>, ..., numbered afresh in each quotation in order of first
    appearance.  Under this import list the file's dependency closure is
    one hundred and eighty-two [Category] modules ([Print Libraries]),
    the six targets among them.  The file also compiles on Coq 8.19.2 and
    8.20.1, with no warning, against the prebuilt trees of this library
    for those versions: of their one thousand and seventy-two sources, one
    thousand and sixty-three are this tree's byte for byte and the other
    nine, the master files #458 corrects, differ from it in comments only
    (compared by script, comments and white space removed), and the six
    targets were compiled beside them from this tree.  The stripped copies
    were compiled there as well, and every one of the thirty-six is
    refused on both at the File line of its Rocq 9.1.1 refusal.  Under
    8.20.1 every error is the Rocq 9.1.1 one up to the serial names; under
    8.19.2 twelve are, and the other twenty-four, all UNIVERSE, print the
    same type mismatch with a "cannot unify" clause between universe
    instances in place of the inconsistency (N2-N4, N8-N12, N24-N28, N31,
    N32, N35), with no clause (N1, N15, N18, N29), or the same
    inconsistency between serial names (N19, N30, N33, N34) (compared by a
    script over the copies).

    KINDS.  Thirty-six refutations, counted as the lines that open with
    the refutation keyword: NAME-ABSENCE (the instrument), UNIVERSE (N1-N4,
    N8-N12, N15-N20, N24-N35), CONVERSION (N5, N13, N14) and TYPING (N6,
    N7, N21-N23): one, twenty-seven, three and five.  No refusal is a
    BINDER one: every binder instrument is accepted.  None is an INSTANCE
    or a SECTION-VARIABLE refusal.  N21 and N22 are the elimination rule
    for propositions: a proof of a [Prop] builds only proofs.  N29 is an
    encoding artifact, pinned as one, not a wall: see its paragraph.

    LABELS.  The pins carry the N-numbers of this file; #458's builders
    and reviews measured most of them in scratch files under other names,
    recorded here so that the target headers can cite either; a review
    is named after the builder whose half it reviewed.  Builder B's walls
    file: its W1 is N16, its W1free N17, its W2 (the relation
    [tcolim_rel]) N19, its [tcolim_relH_at_o] N20, its W3 N21 and its
    W3squash N22; its controls [W1ctl_coprod], [W1ctl_coeq],
    [tcolim_relH], [tcolim_prel], [tcolim_prel_at_o] and
    [tcolim_med_respects_squashed] are [p458_top_coproducts_small],
    [p458_top_coequalizers], [p458_tcolim_relH], [p458_tcolim_prel],
    [p458_tcolim_prel_at_o] and [p458_tcolim_med_squashed].  Builder B's
    bounds file: its B1 is N10, its B2 N11, its B2r N12, its B8 N18 and
    its B10 N27; its B1ctl, B1below, B3, B4, B5, B6, B9 and B11 are
    [p458_cocomplete_at_points], [p458_cocomplete_below],
    [p458_cocomplete_points_at_set], [p458_not_cocomplete_points_at_set],
    [p458_corecipe_above], [p458_pforget_copreserves_above],
    [p458_icoprod_at_points] and [p458_cocomplete_record_above].  Builder
    B's routes file: its [routes_points] is N13, its [routes_apex] N14 and
    its [routes_carrier] [p458_cocomplete_routes_carrier].  Builder A's
    boundary table, re-measured in its review's boundary file: that
    file's d4 and d4b (annotated and free) are N2, its d1v N3, its d3v N4
    and its d3c N8; its d1, d1c, d2, d3 and d4n are
    [p458_complete_below], [p458_complete_via_cones_below],
    [p458_complete_at_set], [p458_complete_record_above] and
    [p458_not_complete_above]; builder A's "refused at s > o" for the
    cone route is N9.  The review's comparison file's [cone_eq] is
    [p458_via_cones_cone].  The second review's transport files: its
    [cm_rebuild] is the target's [top_rebuild] and its [TAI_rebuild]
    [Top_ArrowIndex_transport]; its rebuild with the field passed through,
    refused under a closed binder with no "+" ("Universe constraints are
    not implied by the ones declared: h1 = h2", re-measured under this
    file's import list), is the artifact N29 pins at [h1 < h2]; its
    [Top_not_complete_IEM_transported], [Top_iprod_refuted_IEM_below_h],
    [Top_not_cocomplete_ObjDecEq_try] and
    [CompHaus_not_complete_IEM_between_try] are the targets'
    [Top_not_complete_below_IEM], [Top_iprod_refuted_below_IEM],
    [Top_not_cocomplete_ObjDecEq] and [CompHaus_not_complete_below_IEM].
    The labels are not constants: each refutation carries its own in a
    comment on the line above it, the instrument's reading "The
    instrument".

    ** Instance/Top/Complete.v

    Controls of the initial topology.  [PInit]'s index universe is free:
    it and its opens' readback are stated under the CLOSED binder
    [@{o i}] ([p458_pinit], [p458_pinit_open]); its universal property
    over ARBITRARY spaces mapping in ([p458_pinit_universal]); along one
    map it has the opens of Instance/Top/Subspace.v's [PSub]
    ([p458_pinit_one_psub]).  The recipe, Riehl's Example 3.6.3 for
    limits, at a shape universe ABOVE the points, [o < j], the consumed
    and produced limit properties at independent universes
    ([p458_recipe_above]); its mediator IS the [Sets] one, at [eq_refl]
    ([p458_recipe_med_map]); Riehl's "must", the opens of ANY limiting
    cone ([p458_topology_forced]).  [PForget] is continuous
    ([p458_pforget_continuous]) and preserves the limits of shapes above
    the points ([p458_pforget_preserves_above]).

    N1 (UNIVERSE).  Instance/Top/Complete.v's header, WHAT IS HERE:
    [PTop_HasIndexedProducts] builds products "at every index universe
    at or below [o]".  At the points' universe and strictly below it
    they are formed ([p458_iprod_at_points], [p458_iprod_below]);
    indexed strictly above, at the class [HasIndexedProducts@{s s s s so
    o}] that Instance/Top/Complete/Refutations.v's
    [PTop_iprod_refuted_IEM] refutes under [IEM], N1:
      The term "PTop_HasIndexedProducts" has type
      "HasIndexedProducts@{<1> <1> <1> <2> <3> <2>} PTopCat@{<2> <3>}"
      while it is expected to have type "HasIndexedProducts@{s s s s so
      o} PTopCat@{o so}" (universe inconsistency: Cannot enforce s = o
      because o < s).
    The product IS the product topology at [eq_refl] ([p458_product_obj],
    [p458_pprod_open]), and the topology of ANY indexed product is the
    initial one ([p458_iprod_topology_forced]) and of ANY equalizer the
    subspace topology along its arrow ([p458_equalizer_topology_forced],
    restating [PTop_equalizer_open_iff_PSub]): the reviewer's "products
    must carry the initial topology and equalizers the subspace
    topology".

    N2 (UNIVERSE).  The same header, UNIVERSES: [PTop_Complete] is
    accepted at a shape universe [s < o], at [s := Set] and at a limit
    record [r > o], and refused above the points.  Restated at [s = o],
    at [s < o], at [Set] with [Set < o], with the points themselves at
    [Set], and with the record above the points
    ([p458_complete_at_points], [p458_complete_below],
    [p458_complete_at_set], [p458_complete_points_at_set],
    [p458_complete_record_above]); at [o < s], N2:
      The term "PTop_Complete" has type "Complete@{<1> <2> <3> <4>}"
      while it is expected to have type "Complete@{r s o so}" (universe
      inconsistency: Cannot enforce o = <3> because o < s <= <3>).
    Its limit is the initial topology on the [Sets] limit, at [eq_refl]
    ([p458_complete_apex]).

    N3, N4 (UNIVERSE).  The same paragraph: the book's route
    [PTop_Complete_via_products] is accepted only at [s = o] and [r = o].
    It IS #416's [Complete_from_products_equalizers] at the products and
    #457's [PTop_HasEqualizers], at [eq_refl]
    ([p458_complete_via_products], [p458_via_products_is_book_route]); at
    [s < o], N3:
      The term "PTop_Complete_via_products" has type "Complete@{<1> <1>
      <1> <2>}" while it is expected to have type "Complete@{o s o so}"
      (universe inconsistency: Cannot enforce o = s because s < o).
    and at [r > o], N4:
      The term "PTop_Complete_via_products" has type "Complete@{o o o
      so}" while it is expected to have type "Complete@{r o o so}"
      (universe inconsistency: Cannot enforce o = r because o < r).

    N5 (CONVERSION).  The two routes' apexes are isomorphic
    ([p458_complete_routes_iso]) and the book route's is a subspace of a
    product space ([p458_via_products_apex]); unlike the colimit routes
    (N13), their points' underlying types are not equal at [eq_refl], N5:
      The term "eq_refl" has type "vertex_obj[PTop_Complete J T] =
      vertex_obj[PTop_Complete J T]" while it is expected to have type
      "vertex_obj[PTop_Complete J T] = vertex_obj[PTop_Complete_via_products
      J T]" (cannot unify "carrier vertex_obj[PTop_Complete J T]" and
      "carrier vertex_obj[PTop_Complete_via_products J T]").
    Rocq prints the equation with the coercions [carrier] and
    [pt_carrier] elided, and the parenthetical with [pt_carrier] elided.
    The direct route's points are those of Instance/Sets/Complete.v's
    limit, the book route's those of a [Sets] equalizer of two maps out
    of the product over the shape's objects.

    Controls of Awodey and Riehl.  Awodey's description of the binary
    product's opens as unions of boxes ([p458_ppair_open_iff_box]) and
    the cartesian structure ([p458_cartesian]); the box space on the
    nat-indexed power of [PBool] is not an indexed product
    ([p458_box_not_product], [box_not_indexed_product] at the index
    type's [Nat.eq_dec]), the product topology does mediate
    ([p458_box_mediator]), and the box-open [pbox_all_false] is not
    product-open ([p458_box_strictly_finer]).

    ** Instance/Top/Complete/ConeComma.v

    N6 (TYPING).  The header, THE PRINTED STATEMENT, CORRECTED: Exercise
    3(a) holds with a RIGHT adjoint of G_*.  G_*'s object action is
    [FCone] at [eq_refl] ([p458_coneimage_obj]), and the corrected (a) is
    restated at its type, for any [G], [T] and shape ([p458_ex3a_right]);
    the same lemma given a LEFT adjoint of G_*, the printed premise, N6:
      The term "A" has type "F ⊣ ConeImage G T" while it is expected to
      have type "ConeImage G T ⊣ F".
    The lemma's shape is the correction: G_* on the left of [⊣].

    N7 (TYPING).  The same paragraph: at [PForget] G_* has BOTH adjoints.
    The right one is the weakest topology ([p458_pinitcone_obj], at
    [eq_refl]), and (a) at it IS [PTop_limit_via_cones] at [eq_refl]
    ([p458_limit_via_right], [p458_limit_via_right_is]); the left one, the
    discrete topology, exists ([p458_left_adjoint_at_pforget]) and does
    not fit the lemma, N7:
      The term "pdisc_cone_adjunction T" has type "PDiscCone T ⊣
      ConeImage PForget T" while it is expected to have type "ConeImage
      PForget T ⊣ PDiscCone T".
    So (b)'s left adjoint exists but is the discrete one, and it does
    not construct the weakest topology.

    N8, N9 (UNIVERSE).  The same header, UNIVERSES:
    [PTop_Complete_via_cones] carries the equation [r = o] and the bound
    [s <= o].  It is accepted strictly below the points and at them
    ([p458_complete_via_cones_below], [p458_complete_via_cones_at_points]);
    with the record above the points, N8:
      The term "PTop_Complete_via_cones" has type "Complete@{o o o so}"
      while it is expected to have type "Complete@{r o o so}" (universe
      inconsistency: Cannot enforce o = r because o < r).
    and with the shape above them, N9:
      The term "PTop_Complete_via_cones" has type "Complete@{<1> <2> <1>
      <3>}" while it is expected to have type "Complete@{s s o so}"
      (universe inconsistency: Cannot enforce o = <1> because o < s <=
      <1>).
    Its whole limit cone, not only the apex the header's
    [PTop_via_cones_apex] compares, IS [PTop_Complete]'s at [eq_refl]:
    the target's [PTop_via_cones_cone], restated independently
    ([p458_via_cones_cone], builder A's review's measurement) and at its
    own type ([p458_via_cones_cone_is]); Exercise 3(c)'s products at
    their type ([p458_products_via_cone_comma]).

    ** Instance/Top/Cocomplete.v

    Controls of the final topology.  [PFinal]'s index universe is free
    and its opens read back at [eq_refl], under the CLOSED binder [@{o i}]
    ([p458_pfinal], [p458_pfinal_open]); its universal property over
    ARBITRARY spaces mapping out ([p458_pfinal_universal]); along one map
    it has the opens of Instance/Top/Subspace.v's [PQuot]
    ([p458_pfinal_one_pquot]).  The colimit recipe at a shape universe
    ABOVE the points, the two colimit properties at independent levels
    ([p458_corecipe_above]); the direct colimit's apex at [eq_refl]
    ([p458_pcolimit_apex]); the triangle of its mediator on the nose, at
    [eq_refl], restated independently ([p458_pcolimit_med_at]) and as the
    target's [PColimit_med_at] at its type ([p458_pcolimit_med_at_is]);
    the header's STRENGTHS records that it holds because
    [pfinal_cocone_colimiting] ends [Defined]; Riehl's "must" for colimits
    ([p458_colimit_open_iff_final]).  [PForget] is cocontinuous
    ([p458_pforget_cocontinuous]) and preserves the colimits of shapes
    above the points ([p458_pforget_copreserves_above]).

    N10 (UNIVERSE).  The header, UNIVERSES: [PTop_Cocomplete] is
    accepted with the record above the points, at [s < o] and with the
    points at [Set], and refused at [o < s].  Restated at the points,
    below them, at [Set] and with the record above
    ([p458_cocomplete_at_points], [p458_cocomplete_below],
    [p458_cocomplete_points_at_set], [p458_cocomplete_record_above]); at
    [o < s], N10:
      The term "PTop_Cocomplete" has type "Cocomplete@{<1> <2> <3> <4>}"
      while it is expected to have type "Cocomplete@{r s o so}" (universe
      inconsistency: Cannot enforce o = <3> because o < s <= <3>).

    N11, N12 (UNIVERSE).  The same paragraph: the book's route
    [PTop_Cocomplete_via_coproducts] is [Cocomplete@{o o o so}] only.  It
    IS #416's [Cocomplete_from_coproducts_coequalizers] at the coproducts
    and #457's [PTop_HasCoequalizers], at [eq_refl]
    ([p458_cocomplete_via_coeq], [p458_via_coeq_is_book_route]); at
    [s < o], N11:
      The term "PTop_Cocomplete_via_coproducts" has type
      "Cocomplete@{<1> <1> <1> <2>}" while it is expected to have type
      "Cocomplete@{o s o so}" (universe inconsistency: Cannot enforce
      o = s because s < o).
    and at [r > o], N12:
      The term "PTop_Cocomplete_via_coproducts" has type
      "Cocomplete@{o o o so}" while it is expected to have type
      "Cocomplete@{r o o so}" (universe inconsistency: Cannot enforce
      o = r because o < r).

    N13, N14 (CONVERSION).  The same header, STRENGTHS: the two routes'
    apexes are isomorphic ([p458_cocomplete_routes_iso]) and their
    points' underlying types are equal at [eq_refl]
    ([p458_cocomplete_routes_carrier]); the point setoids are not, N13:
      The term "eq_refl" has type "colimit_apex (PTop_Cocomplete D F) =
      colimit_apex (PTop_Cocomplete D F)" while it is expected to have
      type "colimit_apex (PTop_Cocomplete D F) = colimit_apex
      (PTop_Cocomplete_via_coproducts D F)" (cannot unify "pt_carrier
      (colimit_apex (PTop_Cocomplete D F))" and "pt_carrier (colimit_apex
      (PTop_Cocomplete_via_coproducts D F))").
    and neither are the two spaces, N14, the same message with the
    parenthetical (cannot unify "colimit_apex (PTop_Cocomplete D F)" and
    "colimit_apex (PTop_Cocomplete_via_coproducts D F)").  Rocq prints
    N13's equation of point setoids with the coercion [pt_carrier]
    elided, so the two quotations differ only in the parenthetical.  The
    setoids' equalities differ, the header records: [colim_rel] against
    the equivalence a [Sets] coequalizer generates.

    N15 (UNIVERSE).  The same header, UNIVERSES: the coproducts'
    index universe sits at or below the points'.  The coproduct's opens
    at [eq_refl] ([p458_psigma_open]) and coproducts indexed at the
    points' universe ([p458_icoprod_at_points]); indexed strictly above,
    N15:
      The term "PTop_HasIndexedCoproducts" has type
      "HasIndexedCoproducts@{<1> <2> <3> <4> <3>} PTopCat@{<3> <4>}"
      while it is expected to have type "HasIndexedCoproducts@{u s s so
      o} PTopCat@{o so}" (universe inconsistency: Cannot enforce s = o
      because o < s).
    The non-vacuity witness's injections differ
    ([p458_sum_injections_differ]).

    ** Instance/Top/Cocomplete/TypeValued.v

    N16-N18 (UNIVERSE).  The header, THE WALLS, W1: the book's route over
    [Top] is refused, annotated and with every universe left to
    inference, and the coproducts read at an index universe [h] are
    refused the same way.  The two ingredients are formed alone
    ([p458_top_coproducts_small], [p458_top_coequalizers]) and the
    coequalizer IS the quotient topology on the [Sets] coequalizer at
    [eq_refl] ([p458_top_coequalizer_obj]); the route annotated
    [@{o h +| o < h +}], N16, and free, N17, each:
      The term "Top_HasIndexedCoproducts_small" has type
      "HasIndexedCoproducts@{<1> <2> <3> <3> <3>} Top@{<3> <4>}" while it
      is expected to have type "HasIndexedCoproducts@{<5> <6> <6> <7>
      <6>} ?C" (universe inconsistency: Cannot enforce <2> = <7> because
      <2> <= <4> < <7>).
    [<4>] is the points' universe of that [Top] and [<7>] its hom
    universe.  At an index universe [h], N18:
      The term "Top_HasIndexedCoproducts_small" has type
      "HasIndexedCoproducts@{<1> <2> <3> <3> <3>} Top@{<3> <4>}" while it
      is expected to have type "HasIndexedCoproducts@{u h h h h} Top@{h
      o}" (universe inconsistency: Cannot enforce <2> = h because <2> <=
      <4> < h).

    N19, N20 (UNIVERSE).  W2: Instance/Sets/Cocomplete.v's [colim_rel],
    restated for a diagram in [Top@{h o}] over a shape at or below the
    points ([p458_tcarr], the points of the colimit at [Type@{o}]), is
    refused as a relation at [Type@{o}], N19:
      Universe inconsistency. Cannot enforce h <= o because o < h.
    The same inductive valued at [Type@{h}] is formed
    ([p458_tcolim_relH]); read as a relation at [Type@{o}], N20:
      The term "p458_tcolim_relH D F" has type "p458_tcarr@{o h s} D F →
      p458_tcarr@{o h s} D F → Type@{h}" while it is expected to have
      type "p458_tcarr@{o h s} D F → p458_tcarr@{o h s} D F → Type@{o}"
      (universe inconsistency: Cannot enforce h <= o because o < h).
    N19's arity is formed (its binder instrument, with no constructors,
    is accepted): the glue constructor, quantifying over the arrows of
    the shape at [h], is what is refused.

    N21, N22 (TYPING).  W3: the relation valued in [Prop] is formed and
    read at [Type@{o}] ([p458_tcolim_prel], [p458_tcolim_prel_at_o]); the
    mediator respects it up to [inhabited] ([p458_tcolim_med_squashed]),
    and a squash eliminates into a proposition ([p458_squash_prop]).
    Eliminating the relation into the Type-valued [≈] of an apex, N21:
      Incorrect elimination of "H" in the inductive type
      "p458_tcolim_prel": the return type has sort "Type" while it should
      be SProp or Prop. Elimination of an inductive object of sort Prop
      is not allowed on a predicate in sort "Type" because proofs can be
      eliminated only to build proofs.
    and unwrapping the squash, N22, the same message for "w" in the
    inductive type "inhabited".  N21's branches are holes; its refusal
    is the elimination's, not theirs.

    ** REFUTATION CONSTANTS

    The constants of Instance/Top/Complete/Refutations.v and
    Instance/Top/Cocomplete/Refutations.v, and the [ex3_*] and [Ex3a_*]
    pieces of Instance/Top/Complete/ConeComma.v's refutation of the
    printed Exercise 3(a), are named only in the two sections of that
    name below and in the guard block, so that renaming them touches
    those places and, of this header, the paragraphs LABELS, N1 and
    N23-N35.

    N23 (TYPING).  ConeComma.v's header: the printed (a) is refuted at
    the empty shape into [Roof] ([p458_ex3a_literal_refuted], restating
    [ex3a_left_adjoint_literal_refuted]), by three facts about the same
    [G] and [T] ([p458_ex3a_counterexample]): a left adjoint of G_*
    ([p458_ex3_left_adj]), a limit of [G ◯ T] ([p458_ex3_point_limit])
    and no limit of [T].  The refutation holds under a CLOSED binder
    naming its eleven universes, every one of them declared strictly
    above [Set] ([p458_ex3a_literal_above_set]): the counterexample's
    hom universe is not pinned to [Set].  The left adjunction fed to the
    corrected (a), N23:
      The term "ex3_left_adj" has type "ex3_LeftAdj ⊣ ConeImage ex3_G1
      ex3_T0" while it is expected to have type "ConeImage ex3_G1 ex3_T0
      ⊣ ex3_LeftAdj".
    So the counterexample does not touch the corrected lemma.

    N24, N25 (UNIVERSE).  Instance/Top/Complete/Refutations.v's header,
    THE BOUNDARY.  Completeness and products are refuted above the points
    under [IEM] ([p458_not_complete_above], [p458_iprod_refuted_above]),
    and no arrow index exists at or below them, constructively
    ([p458_no_arrow_index_below]); the two refutations read at the
    points' universe, where [PTop_Complete] and [PTop_HasIndexedProducts]
    hold, N24:
      The term "PTop_not_complete_IEM" has type "IEM@{e} → ¬
      Complete@{<1> <2> <3> <4>}" while it is expected to have type
      "IEM@{e} → ¬ Complete@{r o o so}" (universe inconsistency: Cannot
      enforce <3> = o because <3> < o).
    and N25:
      The term "PTop_iprod_refuted_IEM" has type "IEM@{e} → ¬
      HasIndexedProducts@{<1> <1> <1> <1> <2> <3>} PTopCat@{<3> <2>}"
      while it is expected to have type "IEM@{e} → ¬
      HasIndexedProducts@{o o o o so o} PTopCat@{o so}" (universe
      inconsistency: Cannot enforce o = <3> because <3> < o).

    N26 (UNIVERSE).  The same header: [Top_iprod_refuted_IEM_canonical]
    refutes the Type-valued [Top]'s products at its hom universe
    ([p458_top_iprod_refuted]); the class indexed at the points' universe
    is formed (N26's binder instrument) and the canonical refutation does
    not reach it, N26:
      The term "Top_iprod_refuted_IEM_canonical" has type "IEM@{e} → ¬
      HasIndexedProducts@{<1> <1> <1> <1> <2> <2>} Top@{<2> <3>}" while
      it is expected to have type "IEM@{e} → ¬ HasIndexedProducts@{o o o
      h h h} Top@{h o}" (universe inconsistency: Cannot enforce o = h
      because o < h).
    Nor does [Top_iprod_refuted_below_IEM] (N33).  Products of [Top] at
    index universes at or below its points are neither built nor
    refuted: that is the formability boundary pinned.

    N27 (UNIVERSE).  Instance/Top/Cocomplete/Refutations.v's header, THE
    BOUNDARY: cocompleteness is refuted above the points under [IEM],
    with the points at [Set] as well ([p458_not_cocomplete_above],
    [p458_not_cocomplete_points_at_set]), and so is that of [Sets] and of
    [Top] ([p458_sets_not_cocomplete_above],
    [p458_top_not_cocomplete_above]); read at a shape universe equal to
    the points', N27:
      The term "PTop_not_cocomplete_IEM" has type "IEM@{e} → ¬
      Cocomplete@{<1> <2> <3> <4>}" while it is expected to have type
      "IEM@{e} → ¬ Cocomplete@{r o o so}" (universe inconsistency: Cannot
      enforce <3> = o because <3> < o).

    N28 (UNIVERSE).  The same header, THE BOUNDARY: under decidable
    equality of spaces cocompleteness of [PTopCat] is refuted with the
    points at [Set] by Freyd's argument through the transport
    ([p458_not_cocomplete_objdeceq_at_set]), and by Cantor's only with
    the points above [Set] ([p458_cantor_objdeceq_above_set]); Cantor's
    read at [o := Set], N28:
      The term "PTop_not_cocomplete_Cantor_ObjDecEq" has type
      "ObjDecEq@{<1> <2>} PTopCat@{<2> <1>} → ¬ Cocomplete@{<3> <4>
      <2> <1>}" while it is expected to have type "ObjDecEq@{so Set}
      PTopCat@{Set so} → ¬ Cocomplete@{r s Set so}" (universe
      inconsistency: Cannot enforce Set = <2> because Set < <2>).
    The bound is the separator's, [pcc_Prop] at [Set+1], a property of
    that proof route and not of the refuted statement.

    N29 (UNIVERSE; an encoding artifact, not a wall).
    Instance/Top/Complete/Refutations.v's header, WHAT IS HERE: a
    continuous map of [Top@{h1 o}] is rebuilt as one of [Top@{h2 o}],
    the continuity field eta-expanded, at [h1 < h2]
    ([p458_top_rebuild_up], [top_rebuild]); the field passed through
    unexpanded is accepted where the two hom universes are one
    ([p458_top_rebuild_unexpanded_at_h]), and at [h1 < h2], N29:
      The term "{| continuous_map := f; continuity := continuity f |}"
      has type "ContinuousMorphism@{h1 o} X Y" while it is expected to
      have type "ContinuousMorphism@{h2 o} X Y" (universe inconsistency:
      Cannot enforce h1 = h2 because h1 < h2).
    Elaboration unifies the two continuity types first-order and adds
    [h1 = h2]: with the separating [h1 < h2] deleted the same record is
    accepted, and under [@{o h1 h2 | o < h1, o < h2 +}] it reads back
    with that equation ([About], in a scratch file carrying this file's
    import list).  The hom universes of
    [Top] are NOT walled off from each other: an arrow index moves up
    and down between them ([p458_top_transport_up],
    [p458_top_transport_down], [Top_ArrowIndex_transport]).
    N29 pins elaborator behaviour, not a library boundary: a future
    Rocq that unfolds before unifying would accept the command, which
    would mean the artifact is gone, not that a wall moved.

    N30, N31 (UNIVERSE).  The same header, THE BOUNDARY: completeness of
    [Top] is refuted under [IEM] at a shape universe strictly between the
    points and the homs ([p458_top_not_complete_below]) and under
    [ObjDecEq] with the points at [Set]
    ([p458_top_not_complete_below_at_set]); #455's
    [Top_not_complete_IEM] refutes it at and above the homs
    ([p458_top_not_complete_canonical]).  The first read at [s := o], by
    its universe instance, N30:
      Universe inconsistency. Cannot enforce o < o because o = o.
    and #455's read at [o < s < h], N31:
      The term "Top_not_complete_IEM" has type "IEM@{e} → ¬
      Complete@{<1> <2> <3> <3>}" while it is expected to have type
      "IEM@{e} → ¬ Complete@{r s h h}" (universe inconsistency: Cannot
      enforce <3> = h because <3> <= <2> < h).
    So the [_below] form reaches strictly more shapes than #455's, and
    no refutation reaches the shapes at or below the points.

    N32 (UNIVERSE).  The same paragraph, and Instance/Top/CompHaus.v's
    CORRECTION (#458): completeness of [CompHaus] is refuted under [IEM]
    at a shape universe strictly between the points and the homs
    ([p458_comphaus_not_complete_below]), #455's
    [CompHaus_not_complete_IEM_below] at and above the homs
    ([p458_comphaus_not_complete_canonical]); #455's read at
    [o < s < h], N32:
      The term "CompHaus_not_complete_IEM_below" has type "IEM@{e} → ¬
      Complete@{<1> <2> <3> <4>}" while it is expected to have type
      "IEM@{e} → ¬ Complete@{r s h c}" (universe inconsistency: Cannot
      enforce <3> = h because <3> <= <2> < h).

    N33 (UNIVERSE).  The same header: products of [Top] are refuted under
    [IEM] at an index universe strictly between the points and the homs,
    at the reading [HasIndexedProducts@{s s s h h h}]
    ([p458_top_iprod_refuted_below]); read at the index universe [o], by
    its universe instance, N33:
      Universe inconsistency. Cannot enforce o < o because o = o.

    N34, N35 (UNIVERSE).  Instance/Top/Cocomplete/Refutations.v's header,
    THE BOUNDARY: cocompleteness of [Top] is refuted under [IEM] at a
    shape universe strictly between the points and the homs, by Freyd's
    argument through the transport and by Cantor's
    ([p458_top_not_cocomplete_between], [p458_top_not_cocomplete_cantor]),
    and under [ObjDecEq] with the points at [Set] by Freyd's
    ([p458_top_not_cocomplete_at_set]), by Cantor's only above [Set]
    ([p458_top_cantor_objdeceq_above_set]).  The Freyd [IEM] form read at
    [s := o], by its universe instance, N34:
      Universe inconsistency. Cannot enforce o < o because o = o.
    and Cantor's [ObjDecEq] form read at [o := Set], N35:
      The term "Top_not_cocomplete_Cantor_ObjDecEq" has type
      "ObjDecEq@{<1> <1>} Top@{<1> <2>} → ¬ Cocomplete@{<3> <4> <1>
      <1>}" while it is expected to have type "ObjDecEq@{h h} Top@{h
      Set} → ¬ Cocomplete@{r s h h}" (universe inconsistency: Cannot
      enforce Set = <2> because Set < <2>).

    NOT PINNED HERE.  (a) [About] readbacks as such, the headers' [Set]
    censuses and their attributions to first carriers: pinned only where
    a CLOSED binder carries them ([p458_pinit], [p458_pinit_open],
    [p458_pfinal], [p458_pfinal_open], [p458_top_rebuild_up],
    [p458_top_transport_up], [p458_top_transport_down],
    [p458_ex3a_literal_above_set]) or a refusal does; in particular the
    equation [h1 = h2] that the unexpanded rebuild reads back with is
    pinned only through N29's refusal.  (b) Flip censuses ([Defined]
    against [Qed]) and the closure of the targets under
    [Print Assumptions]: measurements of the build rather than of
    commands; the Makefile's print-assumptions gate is where closure is
    kept.  What a flip decides is pinned where it has a command: the
    triangles [p458_recipe_med_map] and [p458_pcolimit_med_at] hold at
    [eq_refl].  (c) The decidable equality of the index type that
    Instance/Top/Complete.v's [pbox_proj_cont] takes: no refusal shows it
    necessary, and the header records it as a hypothesis of the
    construction, not as a boundary.  (d) Anything about the Type-valued
    [Top] at shapes at or below its points: open there, neither built
    nor refuted, so nothing is refused but the readings N26, N30, N33
    and N34, which only show the refutations do not reach there.

    The guard block at the end names the three hundred and twenty-six
    constants of the six targets, so that a rename breaks this file: one
    hundred and twelve of Instance/Top/Complete.v, sixty-four of
    Instance/Top/Complete/ConeComma.v, seventeen of Instance/Top/
    Complete/Refutations.v, seventy-eight of Instance/Top/Cocomplete.v,
    thirty-two of Instance/Top/Cocomplete/Refutations.v and twenty-three
    of Instance/Top/Cocomplete/TypeValued.v, exactly the list
    [Print Module] gives for each, the forty-two [Program] obligations
    included; the targets declare no record or inductive, so there is
    no [Build_] constructor to name.  The obligations are not reachable
    by their short names under this import list; each is named by the
    shortest qualified name [Locate] gives for it.  Under the full import
    list, [Locate] lists exactly one object for each of the three hundred
    and twenty-six. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Cartesian.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Instance.Top.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Top.Complete.ConeComma.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Complete.Refutations.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Top.Cocomplete.Refutations.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Cocomplete.TypeValued.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

(* The instrument *)
Fail Check probe458_absent_name.

(** ** Instance/Top/Complete.v: the initial topology and the recipe *)

(* CONTROL: [PInit]'s index universe is free, under the CLOSED binder
   [@{o i}]; its opens read back at [eq_refl]. *)
Definition p458_pinit@{o i} (S : SetoidObject@{o o}) (I : Type@{i})
  (X : I → PTop@{o}) (t : ∀ k : I, SetoidMorphism@{o o o} S (X k)) :
  PTop@{o} := PInit S I X t.

Example p458_pinit_open@{o i} (S : SetoidObject@{o o}) (I : Type@{i})
  (X : I → PTop@{o}) (t : ∀ k : I, SetoidMorphism@{o o o} S (X k))
  (V : S → Prop) :
  POpen (PInit S I X t) V = pinit_open S I X t V := eq_refl.

(* CONTROL: the universal property over ARBITRARY spaces mapping in, and
   the one-map case, the subspace topology, restated. *)
Definition p458_pinit_universal@{o i +} (S : SetoidObject@{o o})
  (I : Type@{i}) (X : I → PTop@{o})
  (t : ∀ k : I, SetoidMorphism@{o o o} S (X k)) (Z : PTop@{o})
  (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z (PInit S I X t) g <->
  (∀ k, @PCont Z (X k) (setoid_morphism_compose@{o o o} (t k) g)) :=
  pinit_universal S I X t Z g.

Definition p458_pinit_one_psub@{o +} (X : PTop@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X)
  (V : S → Prop) :
  POpen (PInit S Datatypes.unit (fun _ => X) (fun _ => h)) V
  <-> POpen (PSub X S h) V :=
  PInit_one_PSub X S h V.

(* CONTROL: the recipe at a shape universe ABOVE the points, [o < j],
   the consumed and the produced limit properties at independent
   universes; its mediator IS the [Sets] one at [eq_refl]. *)
Definition p458_recipe_above@{j o so v v1 w w1 +| o < so, o < j +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (N : Cone (PForget@{o so} ◯ T)) (HN : IsLimitCone@{v v1 j o so} N) :
  IsLimitCone@{w w1 j o so} (pinit_cone T N) :=
  pinit_cone_limiting T N HN.

Example p458_recipe_med_map@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (N : Cone (PForget@{o so} ◯ T)) (HN : IsLimitCone N) (M : Cone T) :
  pmap (unique_obj (pinit_cone_limiting T N HN M))
    = unique_obj (HN (FCone PForget M)) := eq_refl.

(* CONTROL: Riehl's "must": the opens of ANY limiting cone are those of
   the initial topology of its legs. *)
Definition p458_topology_forced@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}) (L : Cone T)
  (HL : IsLimitCone L) (V : vertex_obj[L] → Prop) :
  POpen (vertex_obj[L]) V
  <-> POpen (vertex_obj[pinit_cone T (FCone PForget L)]) V :=
  PTop_limit_open_iff_initial T L HL V.

(* CONTROL: [PForget] is continuous, and preserves the limits of shapes
   ABOVE the points, [o < s]. *)
Definition p458_pforget_continuous@{o so +| o < so +} :
  ContinuousFunctor PForget@{o so} := PForget_Continuous.

Definition p458_pforget_preserves_above@{s o so +| o < so, o < s +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  PreservesLimitCone T PForget@{o so} := PForget_PreservesLimitCone J T.

(** ** Instance/Top/Complete.v: products and their index boundary *)

(* CONTROL: products indexed at the points' universe and strictly
   below it. *)
Definition p458_iprod_at_points@{o so +| o < so +} :
  @HasIndexedProducts@{o o o o so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

Definition p458_iprod_below@{i o so +| i < o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

(* N1 *)
Fail Definition p458_iprod_above@{s o so +| o < so, o < s +} :
  @HasIndexedProducts@{s s s s so o} PTopCat@{o so} :=
  PTop_HasIndexedProducts.

(* CONTROL: the product IS the product topology, at [eq_refl]; the
   topology of ANY indexed product is the initial one. *)
Example p458_product_obj@{i o so +| i <= o, o < so +} (A : Type@{i})
  (X : A → PTop@{o}) :
  @indexed_product PTopCat@{o so} PTop_HasIndexedProducts A X
    = PProd A X := eq_refl.

Example p458_pprod_open@{i o +| i <= o +} (A : Type@{i})
  (X : A → PTop@{o}) (V : PProd_carrier A X → Prop) :
  POpen (PProd A X) V
    = pinit_open (PProd_carrier A X) A X (pprod_leg A X) V := eq_refl.

Definition p458_iprod_topology_forced@{i o so +| i <= o, o < so +}
  (A : Type@{i}) (X : A → PTop@{o}) (Y : PTop@{o})
  (p : ∀ a, Y ~{PTopCat@{o so}}~> X a)
  (H : @IsIndexedProduct PTopCat@{o so} A X Y p) (V : Y → Prop) :
  POpen Y V <-> POpen (PInit Y A X (fun a => pmap (p a))) V :=
  PTop_iprod_open_iff_initial A X Y p H V.

(* CONTROL: the topology of ANY equalizer of spaces is the subspace
   topology along its arrow. *)
Definition p458_equalizer_topology_forced@{o so +| o < so +}
  {X Y : PTop@{o}} (f g : X ~{PTopCat@{o so}}~> Y) (E : PTop@{o})
  (e : E ~{PTopCat@{o so}}~> X)
  (H : @IsEqualizer PTopCat@{o so} X Y f g E e) (V : E → Prop) :
  POpen E V <-> POpen (PSub X E (pmap e)) V :=
  PTop_equalizer_open_iff_PSub f g E e H V.

(** ** Instance/Top/Complete.v: Remark 1 and its universe boundary *)

(* CONTROL: [PTop_Complete] at a shape universe equal to the points',
   strictly below them, at [Set], with the points at [Set], and with the
   limit record strictly above the points. *)
Definition p458_complete_at_points@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_at_set@{o so +| Set < o, o < so +} :
  @Complete@{o Set o so} PTopCat@{o so} := PTop_Complete.

Definition p458_complete_points_at_set@{so +| Set < so +} :
  @Complete@{Set Set Set so} PTopCat@{Set so} := PTop_Complete.

Definition p458_complete_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete.

(* N2 *)
Fail Definition p458_complete_above@{r s o so +| o < s, o < so, s <= r +} :
  @Complete@{r s o so} PTopCat@{o so} := PTop_Complete.

(* CONTROL: its limit is the initial topology on the [Sets] limit, at
   [eq_refl]. *)
Example p458_complete_apex@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T)]
    = pinit_top T (Sets_limit_cone (PForget ◯ T)) := eq_refl.

(* CONTROL: the book's route, at its one instance [Complete@{o o o so}];
   it IS #416's theorem at the products and #457's equalizers. *)
Definition p458_complete_via_products@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete_via_products.

Example p458_via_products_is_book_route@{o so +| o < so +} :
  @PTop_Complete_via_products@{o so _ _ _ _ _}
    = @Complete_from_products_equalizers PTopCat@{o so}
        PTop_HasIndexedProducts PTop_HasEqualizers := eq_refl.

(* N3 *)
Fail Definition p458_via_products_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete_via_products.

(* N4 *)
Fail Definition p458_via_products_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete_via_products.

(* CONTROL: the book route's limit is a subspace of a product space, and
   the two routes' apexes are isomorphic. *)
Definition p458_via_products_apex@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  ex (fun S => ex (fun h =>
    vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_products J T)]
      = PSub (PProd (obj[J]) (fun j => fobj[T] j)) S h)) :=
  PTop_Complete_via_products_apex J T.

Definition p458_complete_routes_iso@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete J T)]
    ≅[PTopCat@{o so}]
  vertex_obj[@limit_cone _ _ _ (@PTop_Complete_via_products J T)] :=
  PTop_Complete_routes_iso J T.

(* N5 *)
Fail Example p458_complete_routes_carrier@{o so +| o < so +}
  (J : Category@{o o o}) (T : J ⟶ PTopCat@{o so}) :
  carrier (pt_carrier (vertex_obj[@limit_cone _ _ _ (PTop_Complete J T)]))
  = carrier (pt_carrier
      (vertex_obj[@limit_cone _ _ _ (PTop_Complete_via_products J T)])) :=
  eq_refl.

(** ** Instance/Top/Complete.v: Awodey §2.6 and Riehl's box topology *)

(* CONTROL: Awodey's description of the binary product's opens, and the
   cartesian structure. *)
Definition p458_ppair_open_iff_box@{o +} (X1 X2 : PTop@{o})
  (W : PPair_carrier X1 X2 → Prop) :
  POpen (PPair X1 X2) W <-> pair_box_union X1 X2 W :=
  PPair_open_iff_box X1 X2 W.

Definition p458_cartesian@{o so +| o < so +} : @Cartesian PTopCat@{o so} :=
  PTop_Cartesian.

(* CONTROL: the box space on the nat-indexed power of [PBool] is not an
   indexed product; the product topology mediates; the box-open
   [pbox_all_false] is not product-open. *)
Definition p458_box_not_product@{o so +| o < so +} :
  @IsIndexedProduct PTopCat@{o so} nat (fun _ => PBool@{o})
    (PBoxTop nat (fun _ => PBool@{o}))
    (pbox_proj nat (fun _ => PBool@{o}) Nat.eq_dec)
  → False :=
  box_not_indexed_product.

Definition p458_box_mediator@{o +} :
  PMor@{o} PConv@{o} (PProd nat (fun _ => PBool@{o})) :=
  pconv_prod_mediator.

Definition p458_box_strictly_finer@{o +} :
  POpen (PProd nat (fun _ => PBool@{o})) pbox_all_false → False :=
  pbox_all_false_not_product_open.

(** ** Instance/Top/Complete/ConeComma.v: Exercise 3, corrected *)

(* CONTROL: G_*'s object action, and (a) with a RIGHT adjoint of G_*,
   restated for any [G], [T] and shape. *)
Example p458_coneimage_obj@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (N : Cone T) : fobj[ConeImage G T] N = FCone G N :=
  eq_refl.

Definition p458_ex3a_right@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (W : Cones (G ◯ T) ⟶ Cones T) (A : ConeImage G T ⊣ W)
  (L : Limit (G ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint G T W A L.

(* N6 *)
Fail Definition p458_ex3a_left@{oj oc od h +} {J : Category@{oj h h}}
  {C : Category@{oc h h}} {D : Category@{od h h}} (G : C ⟶ D)
  (T : J ⟶ C) (F : Cones (G ◯ T) ⟶ Cones T) (A : F ⊣ ConeImage G T)
  (L : Limit (G ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint G T F A L.

(* CONTROL: at [PForget] the right adjoint is the weakest topology, and
   (a) at it IS [PTop_limit_via_cones]; the left adjoint, the discrete
   topology, exists too. *)
Example p458_pinitcone_obj@{j o so +| o < so +} {J : Category@{j o o}}
  (T : J ⟶ PTopCat@{o so}) (N : Cone (PForget@{o so} ◯ T)) :
  fobj[PInitCone T] N = pinit_cone T N := eq_refl.

Definition p458_limit_via_right@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (L : Limit (PForget@{o so} ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint PForget T (PInitCone T)
    (pcone_adjunction T) L.

Example p458_limit_via_right_is@{j o so +| o < so +} {J : Category@{j o o}}
  (T : J ⟶ PTopCat@{o so}) (L : Limit (PForget@{o so} ◯ T)) :
  p458_limit_via_right T L = PTop_limit_via_cones T L := eq_refl.

Definition p458_left_adjoint_at_pforget@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so}) :
  PDiscCone T ⊣ ConeImage PForget@{o so} T :=
  pdisc_cone_adjunction T.

(* N7 *)
Fail Definition p458_limit_via_left@{j o so +| o < so +}
  {J : Category@{j o o}} (T : J ⟶ PTopCat@{o so})
  (L : Limit (PForget@{o so} ◯ T)) : Limit T :=
  limit_from_cone_right_adjoint PForget T (PDiscCone T)
    (pdisc_cone_adjunction T) L.

(* CONTROL: [PTop_Complete_via_cones] strictly below the points and at
   them; its whole limit cone IS [PTop_Complete]'s at [eq_refl]; the
   products of (c). *)
Definition p458_complete_via_cones_below@{s o so +| s < o, o < so +} :
  @Complete@{o s o so} PTopCat@{o so} := PTop_Complete_via_cones.

Definition p458_complete_via_cones_at_points@{o so +| o < so +} :
  @Complete@{o o o so} PTopCat@{o so} := PTop_Complete_via_cones.

(* N8 *)
Fail Definition p458_via_cones_record_above@{r o so +| o < r, o < so +} :
  @Complete@{r o o so} PTopCat@{o so} := PTop_Complete_via_cones.

(* N9 *)
Fail Definition p458_via_cones_above@{s o so +| o < s, o < so +} :
  @Complete@{s s o so} PTopCat@{o so} := PTop_Complete_via_cones.

Example p458_via_cones_cone@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  @limit_cone _ _ _ (@PTop_Complete_via_cones@{o s o so _ _ _} J T)
    = @limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T) := eq_refl.

Definition p458_via_cones_cone_is@{s o so +| s <= o, o < so +}
  (J : Category@{s o o}) (T : J ⟶ PTopCat@{o so}) :
  @limit_cone _ _ _ (@PTop_Complete_via_cones@{o s o so _ _ _} J T)
    = @limit_cone _ _ _ (@PTop_Complete@{o s o so _ _} J T) :=
  PTop_via_cones_cone J T.

Definition p458_products_via_cone_comma@{i o so +| i <= o, o < so +} :
  @HasIndexedProducts@{i i i o so o} PTopCat@{o so} :=
  PTop_products_via_cone_comma.

(** ** Instance/Top/Cocomplete.v: the final topology and the recipe *)

(* CONTROL: [PFinal]'s index universe is free, under the CLOSED binder
   [@{o i}]; its opens read back at [eq_refl]. *)
Definition p458_pfinal@{o i} (S : SetoidObject@{o o}) (Ix : Type@{i})
  (X : Ix → PTop@{o}) (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S) :
  PTop@{o} := PFinal S Ix X f.

Example p458_pfinal_open@{o i} (S : SetoidObject@{o o}) (Ix : Type@{i})
  (X : Ix → PTop@{o}) (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S)
  (V : S → Prop) :
  POpen (PFinal S Ix X f) V
  = ((∀ s t : S, s ≈ t → V s → V t) /\
     (∀ k : Ix, POpen (X k) (fun x => V (f k x)))) := eq_refl.

(* CONTROL: the universal property over ARBITRARY spaces mapping out,
   and the one-map case, the quotient topology, restated. *)
Definition p458_pfinal_universal@{o i +} (S : SetoidObject@{o o})
  (Ix : Type@{i}) (X : Ix → PTop@{o})
  (f : ∀ k : Ix, SetoidMorphism@{o o o} (X k) S) (Z : PTop@{o})
  (g : SetoidMorphism@{o o o} S Z) :
  @PCont (PFinal S Ix X f) Z g <->
  (∀ k, @PCont (X k) Z (setoid_morphism_compose@{o o o} g (f k))) :=
  pfinal_universal S Ix X f Z g.

Definition p458_pfinal_one_pquot@{o +} (X : PTop@{o})
  (T : SetoidObject@{o o}) (q : SetoidMorphism@{o o o} X T)
  (V : T → Prop) :
  POpen (PQuot X T q) V
  <-> POpen (PFinal T Datatypes.unit (fun _ => X) (fun _ => q)) V :=
  pfinal_one_map_PQuot X T q V.

(* CONTROL: the colimit recipe at a shape universe ABOVE the points; the
   direct colimit's apex; Riehl's "must" for colimits. *)
Definition p458_corecipe_above@{o so s r r' x x' +| o < so, o < s +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so})
  (N : Cocone (PForget@{o so} ◯ F))
  (HN : IsColimitCocone@{x' x' r' s o so} N) :
  IsColimitCocone@{x x r s o so} (PFinalCocone F N) :=
  pfinal_cocone_colimiting F N HN.

Example p458_pcolimit_apex@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) :
  vertex_obj[@limit_cone _ _ _ (@PColimit@{r s o so _ _} D F)]
    = PFinal (Sets_colim_obj (PForget ◯ F)) (obj[D]) (fun d => F d)
        (fun d => Sets_colim_inj (PForget ◯ F) d) := eq_refl.

Example p458_pcolimit_med_at@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) (M : Cocone F) (d : D)
  (x : pt_carrier (F d)) :
  pmap (unique_obj (@ump_limits _ _ _ (@PColimit@{r s o so _ _} D F) M))
    (existT _ d x) = pmap (cocone_inj M d) x := eq_refl.

Definition p458_pcolimit_med_at_is@{r s o so +| o < so, s <= o, o <= r +}
  {D : Category@{s o o}} (F : D ⟶ PTopCat@{o so}) (M : Cocone F) (d : D)
  (x : pt_carrier (F d)) :
  pmap (unique_obj (@ump_limits _ _ _ (@PColimit@{r s o so _ _} D F) M))
    (existT _ d x) = pmap (cocone_inj M d) x :=
  PColimit_med_at F M d x.

Definition p458_colimit_open_iff_final@{o so s r +| o < so +}
  {D : Category@{s o o}} {F : D ⟶ PTopCat@{o so}}
  (L : Colimit@{r s o so} F) (V : pt_carrier (colimit_apex L) → Prop) :
  POpen (colimit_apex L) V
  <-> POpen (PFinal (pt_carrier (colimit_apex L)) (obj[D]) (fun d => F d)
               (fun d => pmap (colimit_inj (colimit_is_acolimit L) d))) V :=
  PTop_colimit_open_iff_final L V.

(* CONTROL: [PForget] is cocontinuous, and preserves the colimits of
   shapes ABOVE the points. *)
Definition p458_pforget_cocontinuous@{o so +| o < so +} :
  CocontinuousFunctor PForget@{o so} := PForget_Cocontinuous.

Definition p458_pforget_copreserves_above@{s o so +| o < so, o < s +}
  (J : Category@{s o o}) (K : J ⟶ PTopCat@{o so}) :
  PreservesColimitCocone K PForget@{o so} :=
  PForget_PreservesColimitCocone J K.

(** ** Instance/Top/Cocomplete.v: Remark 2 and its universe boundary *)

(* CONTROL: [PTop_Cocomplete] at the points' universe, strictly below
   it, with the points at [Set], and with the colimit record strictly
   above the points. *)
Definition p458_cocomplete_at_points@{o so +| o < so +} :
  @Cocomplete@{o o o so} PTopCat@{o so} := PTop_Cocomplete.

Definition p458_cocomplete_below@{s o so +| s < o, o < so +} :
  @Cocomplete@{o s o so} PTopCat@{o so} := PTop_Cocomplete.

Definition p458_cocomplete_points_at_set@{so +| Set < so +} :
  @Cocomplete@{Set Set Set so} PTopCat@{Set so} := PTop_Cocomplete.

Definition p458_cocomplete_record_above@{r o so +| o < r, o < so +} :
  @Cocomplete@{r o o so} PTopCat@{o so} := PTop_Cocomplete.

(* N10 *)
Fail Definition p458_cocomplete_above@{r s o so +| o < s, o < so, s <= r +} :
  @Cocomplete@{r s o so} PTopCat@{o so} := PTop_Cocomplete.

(* CONTROL: the book's route, at its one instance
   [Cocomplete@{o o o so}]; it IS #416's theorem at the coproducts and
   #457's coequalizers. *)
Definition p458_cocomplete_via_coeq@{o so +| o < so +} :
  @Cocomplete@{o o o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

Example p458_via_coeq_is_book_route@{o so +| o < so +} :
  @PTop_Cocomplete_via_coproducts@{o so _ _ _ _ _ _}
    = Cocomplete_from_coproducts_coequalizers PTop_HasIndexedCoproducts
        PTop_HasCoequalizers := eq_refl.

(* N11 *)
Fail Definition p458_via_coeq_below@{s o so +| s < o, o < so +} :
  @Cocomplete@{o s o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

(* N12 *)
Fail Definition p458_via_coeq_record_above@{r o so +| o < r, o < so +} :
  @Cocomplete@{r o o so} PTopCat@{o so} := PTop_Cocomplete_via_coproducts.

(* CONTROL: the two routes' apexes are isomorphic, and their points'
   underlying types are equal at [eq_refl]. *)
Definition p458_cocomplete_routes_iso@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  colimit_apex (PTop_Cocomplete D F)
    ≅[PTopCat@{o so}] colimit_apex (PTop_Cocomplete_via_coproducts D F) :=
  PTop_Cocomplete_routes_iso D F.

Example p458_cocomplete_routes_carrier@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  carrier (pt_carrier (colimit_apex (PTop_Cocomplete D F)))
  = carrier
      (pt_carrier (colimit_apex (PTop_Cocomplete_via_coproducts D F))) :=
  eq_refl.

(* N13 *)
Fail Example p458_cocomplete_routes_points@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  pt_carrier (colimit_apex (PTop_Cocomplete D F))
  = pt_carrier (colimit_apex (PTop_Cocomplete_via_coproducts D F)) := eq_refl.

(* N14 *)
Fail Example p458_cocomplete_routes_spaces@{o so +| o < so +}
  (D : Category@{o o o}) (F : D ⟶ PTopCat@{o so}) :
  colimit_apex (PTop_Cocomplete D F)
  = colimit_apex (PTop_Cocomplete_via_coproducts D F) := eq_refl.

(** ** Instance/Top/Cocomplete.v: coproducts and their index boundary *)

(* CONTROL: the coproduct's opens at [eq_refl]; coproducts indexed at
   the points' universe; the non-vacuity witness. *)
Example p458_psigma_open@{o i +| i <= o +} (Ix : Type@{i})
  (X : Ix → PTop@{o})
  (V : Sets_icoprod_obj (fun k => pt_carrier (X k)) → Prop) :
  POpen (PSigma Ix X) V
  = ((∀ p q : Sets_icoprod_obj (fun k => pt_carrier (X k)),
        p ≈ q → V p → V q) /\
     (∀ k : Ix, POpen (X k) (fun x => V (existT _ k x)))) := eq_refl.

Definition p458_icoprod_at_points@{o so u +| o < so, so <= u, o < u +} :
  @HasIndexedCoproducts@{u o o so o} PTopCat@{o so} :=
  PTop_HasIndexedCoproducts.

(* N15 *)
Fail Definition p458_icoprod_above@{s o so u +| o < so, o < s, so <= u,
  s < u +} :
  @HasIndexedCoproducts@{u s s so o} PTopCat@{o so} :=
  PTop_HasIndexedCoproducts.

Definition p458_sum_injections_differ@{o so u | o < so, o < u +} :
  psigma_inj@{o so o u} bool (fun _ => PTwoIndisc@{o}) true
    ≈[PTopCat@{o so}] psigma_inj@{o so o u} bool (fun _ => PTwoIndisc) false
  → False := PTwoIndiscSum_injections_differ.

(** ** Instance/Top/Cocomplete/TypeValued.v: the three walls *)

(* CONTROL: W1's two ingredients, each accepted alone; the coequalizer
   IS the quotient topology at [eq_refl]. *)
Definition p458_top_coproducts_small@{o h u u0 +| o < h, u0 <= o, h < u +} :
  @HasIndexedCoproducts@{u u0 h h h} Top@{h o} :=
  Top_HasIndexedCoproducts_small.

Definition p458_top_coequalizers@{o h +| o < h +} :
  @HasCoequalizers Top@{h o} := Top_HasCoequalizers.

Example p458_top_coequalizer_obj@{o h +| o < h +} {x y : Top@{h o}}
  (f g : x ~{Top@{h o}}~> y) :
  `1 (@coeq _ Top_HasCoequalizers x y f g)
    = TQuot y (SetsCoeq (continuous_map f) (continuous_map g))
        (sets_coeq_proj (continuous_map f) (continuous_map g)) := eq_refl.

(* N16 *)
Fail Definition p458_top_book_route@{o h +| o < h +} :
  @Cocomplete Top@{h o} :=
  Cocomplete_from_coproducts_coequalizers Top_HasIndexedCoproducts_small
    Top_HasCoequalizers.

(* N17 *)
Fail Definition p458_top_book_route_free :=
  Cocomplete_from_coproducts_coequalizers Top_HasIndexedCoproducts_small
    Top_HasCoequalizers.

(* N18 *)
Fail Definition p458_top_coproducts_at_homs@{o h u +| o < h, h < u +} :
  @HasIndexedCoproducts@{u h h h h} Top@{h o} :=
  Top_HasIndexedCoproducts_small.

(* The points of a colimit of [Top@{h o}] over a shape at or below the
   points: the sigma over the shape's objects, at [o]. *)
Definition p458_tcarr@{o h s +| o < h, s <= o +} (D : Category@{s h h})
  (F : D ⟶ Top@{h o}) : Type@{o} :=
  { d : obj[D] & top_carrier (F d) }.

(* N19 *)
Fail Inductive p458_tcolim_rel@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  | p458_tcr_point : ∀ (d : D) (x y : top_carrier (F d)), x ≈ y →
      p458_tcolim_rel (existT _ d x) (existT _ d y)
  | p458_tcr_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_rel (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcr_sym : ∀ p q, p458_tcolim_rel p q → p458_tcolim_rel q p
  | p458_tcr_trans : ∀ p q r, p458_tcolim_rel p q →
      p458_tcolim_rel q r → p458_tcolim_rel p r.

(* CONTROL: the same relation valued at the homs' universe [h]. *)
Inductive p458_tcolim_relH@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{h} :=
  | p458_tcrH_point : ∀ (d : D) (x y : top_carrier (F d)), x ≈ y →
      p458_tcolim_relH (existT _ d x) (existT _ d y)
  | p458_tcrH_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_relH (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcrH_sym : ∀ p q, p458_tcolim_relH p q → p458_tcolim_relH q p
  | p458_tcrH_trans : ∀ p q r, p458_tcolim_relH p q →
      p458_tcolim_relH q r → p458_tcolim_relH p r.

(* N20 *)
Fail Definition p458_tcolim_relH_at_o@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  p458_tcolim_relH D F.

(* CONTROL: the same relation valued in [Prop] fits at [Type@{o}]; the
   mediator respects it up to [inhabited]; the squash eliminates into a
   proposition. *)
Inductive p458_tcolim_prel@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Prop :=
  | p458_tcp_point : ∀ (d : D) (x y : top_carrier (F d)),
      inhabited (x ≈ y) → p458_tcolim_prel (existT _ d x) (existT _ d y)
  | p458_tcp_glue : ∀ (d d' : D) (f : d ~{D}~> d') (x : top_carrier (F d)),
      p458_tcolim_prel (existT _ d x)
        (existT _ d' (continuous_map (fmap[F] f) x))
  | p458_tcp_sym : ∀ p q, p458_tcolim_prel p q → p458_tcolim_prel q p
  | p458_tcp_trans : ∀ p q r, p458_tcolim_prel p q →
      p458_tcolim_prel q r → p458_tcolim_prel p r.

Definition p458_tcolim_prel_at_o@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) :
  p458_tcarr D F → p458_tcarr D F → Type@{o} :=
  p458_tcolim_prel D F.

Lemma p458_tcolim_med_squashed@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) (Z : TopSpace@{o})
  (m : p458_tcarr D F → top_carrier Z)
  (Hp : ∀ d (x y : top_carrier (F d)), x ≈ y →
          m (existT _ d x) ≈ m (existT _ d y))
  (Hm : ∀ d d' (f : d ~{D}~> d') x,
          m (existT _ d x) ≈ m (existT _ d' (continuous_map (fmap[F] f) x)))
  (p q : p458_tcarr D F) :
  p458_tcolim_prel D F p q → inhabited (m p ≈ m q).
Proof.
  induction 1 as [d x y [e]|d d' f x|p q _ [IH]|p q r _ [IH1] _ [IH2]].
  - constructor. exact (Hp d x y e).
  - constructor. exact (Hm d d' f x).
  - constructor. symmetry. exact IH.
  - constructor. transitivity (m q); assumption.
Qed.

Definition p458_squash_prop@{o +} (Z : TopSpace@{o}) (a b : top_carrier Z)
  (P : Prop) (k : a ≈ b → P) (w : inhabited (a ≈ b)) : P :=
  match w with inhabits e => k e end.

(* N21 *)
Fail Definition p458_tcolim_elim@{o h s +| o < h, s <= o +}
  (D : Category@{s h h}) (F : D ⟶ Top@{h o}) (Z : TopSpace@{o})
  (m : p458_tcarr D F → top_carrier Z) (p q : p458_tcarr D F)
  (H : p458_tcolim_prel D F p q) : m p ≈ m q :=
  match H with
  | p458_tcp_point _ _ _ _ _ _ => _
  | p458_tcp_glue _ _ _ _ _ _ => _
  | p458_tcp_sym _ _ _ _ _ => _
  | p458_tcp_trans _ _ _ _ _ _ _ => _
  end.

(* N22 *)
Fail Definition p458_squash_elim@{o +} (Z : TopSpace@{o})
  (a b : top_carrier Z) (w : inhabited (a ≈ b)) : a ≈ b :=
  match w with inhabits e => e end.

(** ** REFUTATION CONSTANTS: the two Refutations satellites and the pieces
       of Exercise 3's printed reading *)

(* CONTROL: the printed (a) refuted, the refuting data, the left
   adjunction and the limit of [G ◯ T] it consists of, restated. *)
Definition p458_ex3a_literal_refuted :
  Ex3a_left_literal ex3_G1 ex3_T0 → False :=
  ex3a_left_adjoint_literal_refuted.

(* CONTROL: the same refutation under a CLOSED binder that puts every one
   of its eleven universes strictly above [Set]. *)
Definition p458_ex3a_literal_above_set@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 |
  Set < u, Set < u0, Set < u1, Set < u2, Set < u3, Set < u4, Set < u5,
  Set < u6, Set < u7, Set < u8, Set < u9, u8 < u5, u9 < u2 +} :
  Ex3a_left_literal@{u u5 u0 u1 u2 u9 u3 u4 u6 u8 u7} ex3_G1@{u7 u4 u8}
    ex3_T0@{u6 u8 u7 u5} → False :=
  ex3a_left_adjoint_literal_refuted@{u u0 u1 u2 u3 u4 u5 u6 u7 u8 u9}.

Definition p458_ex3a_counterexample :
  Ex3a_left_refuting_data ex3_G1 ex3_T0 := ex3a_left_counterexample.

Definition p458_ex3_left_adj : ex3_LeftAdj ⊣ ConeImage ex3_G1 ex3_T0 :=
  ex3_left_adj.

Definition p458_ex3_point_limit : Limit (ex3_G1 ◯ ex3_T0) :=
  ex3_point_limit.

(* N23 *)
Fail Definition p458_ex3a_left_at_roof : Limit ex3_T0 :=
  limit_from_cone_right_adjoint ex3_G1 ex3_T0 ex3_LeftAdj ex3_left_adj
    ex3_point_limit.

(* CONTROL: completeness refuted above the points under [IEM]; no arrow
   index at or below them, constructively. *)
Definition p458_not_complete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Complete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_complete_IEM.

(* N24 *)
Fail Definition p458_not_complete_at_points@{e r o so +| o < so, o <= r +} :
  IEM@{e} → @Complete@{r o o so} PTopCat@{o so} → False :=
  PTop_not_complete_IEM.

Definition p458_no_arrow_index_below@{s o so +| s <= o, o < so +} :
  ArrowIndex@{s so o} PTopCat@{o so} → False :=
  PTop_no_ArrowIndex_below.

(* CONTROL: products refuted above the points under [IEM]. *)
Definition p458_iprod_refuted_above@{e s o so +| o < so, o < s +} :
  IEM@{e} → @HasIndexedProducts@{s s s s so o} PTopCat@{o so} → False :=
  PTop_iprod_refuted_IEM.

(* N25 *)
Fail Definition p458_iprod_refuted_at_points@{e o so +| o < so +} :
  IEM@{e} → @HasIndexedProducts@{o o o o so o} PTopCat@{o so} → False :=
  PTop_iprod_refuted_IEM.

(* CONTROL: products of the Type-valued [Top] refuted at the homs'
   universe under [IEM]. *)
Definition p458_top_iprod_refuted@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{h h h h h h} Top@{h o} → False :=
  Top_iprod_refuted_IEM_canonical.

(* N26 *)
Fail Definition p458_top_iprod_refuted_at_points@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{o o o h h h} Top@{h o} → False :=
  Top_iprod_refuted_IEM_canonical.

(* CONTROL: cocompleteness refuted above the points under [IEM], with
   the points at [Set] too; of [Sets] and of [Top] as well. *)
Definition p458_not_cocomplete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Cocomplete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_IEM.

Definition p458_not_cocomplete_points_at_set@{e r s so +| Set < so,
  Set < s, s <= r +} :
  IEM@{e} → @Cocomplete@{r s Set so} PTopCat@{Set so} → False :=
  PTop_not_cocomplete_IEM.

(* N27 *)
Fail Definition p458_not_cocomplete_at_points@{e r o so +| o < so,
  o <= r +} :
  IEM@{e} → @Cocomplete@{r o o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_IEM.

Definition p458_sets_not_cocomplete_above@{e r s o so +| o < so, o < s,
  s <= r +} :
  IEM@{e} → @Cocomplete@{r s o so} Sets@{o so} → False :=
  Sets_not_cocomplete_IEM.

Definition p458_top_not_cocomplete_above@{e r s o h +| o < h, o < s,
  s <= r, h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM.

(** ** REFUTATION CONSTANTS: [ObjDecEq] with the points at [Set], and the
       Type-valued [Top] below its homs *)

(* CONTROL: cocompleteness of [PTopCat] refuted under decidable equality
   of spaces with the points at [Set], by Freyd's argument through the
   transport; by Cantor's with the points above [Set]. *)
Definition p458_not_cocomplete_objdeceq_at_set@{r s so +| Set < so,
  Set < s, s <= r +} :
  ObjDecEq PTopCat@{Set so} → @Cocomplete@{r s Set so} PTopCat@{Set so}
  → False :=
  PTop_not_cocomplete_ObjDecEq.

Definition p458_cantor_objdeceq_above_set@{r s o so +| Set < o, o < so,
  o < s, s <= r +} :
  ObjDecEq PTopCat@{o so} → @Cocomplete@{r s o so} PTopCat@{o so} → False :=
  PTop_not_cocomplete_Cantor_ObjDecEq.

(* N28 *)
Fail Definition p458_cantor_objdeceq_at_set@{r s so +| Set < so, Set < s,
  s <= r +} :
  ObjDecEq PTopCat@{Set so} → @Cocomplete@{r s Set so} PTopCat@{Set so}
  → False :=
  PTop_not_cocomplete_Cantor_ObjDecEq.

(* CONTROL: a continuous map rebuilt between two hom universes of [Top],
   the continuity field eta-expanded, at [h1 < h2]; the field passed
   through unexpanded where the two hom universes are one. *)
Definition p458_top_rebuild_up@{o h1 h2 | o < h1, h1 < h2 +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h1 o} X Y) :
  ContinuousMorphism@{h2 o} X Y :=
  top_rebuild f.

Definition p458_top_rebuild_unexpanded_at_h@{o h | o < h +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h o} X Y) :
  ContinuousMorphism@{h o} X Y :=
  {| continuous_map := continuous_map f; continuity := continuity f |}.

(* N29 *)
Fail Definition p458_top_rebuild_unexpanded@{o h1 h2 | o < h1, h1 < h2 +}
  {X Y : TopSpace@{o}} (f : ContinuousMorphism@{h1 o} X Y) :
  ContinuousMorphism@{h2 o} X Y :=
  {| continuous_map := continuous_map f; continuity := continuity f |}.

(* CONTROL: an arrow index of [Top] moves up and down between hom
   universes. *)
Definition p458_top_transport_up@{s o h1 h2 | o < h1, h1 < h2 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) : ArrowIndex@{s h2 h2} Top@{h2 o} :=
  Top_ArrowIndex_transport AI.

Definition p458_top_transport_down@{s o h1 h2 | o < h2, h2 < h1 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) : ArrowIndex@{s h2 h2} Top@{h2 o} :=
  Top_ArrowIndex_transport AI.

(* CONTROL: completeness of [Top] refuted under [IEM] at a shape universe
   strictly between the points and the homs, and under [ObjDecEq] with
   the points at [Set]; #455's form at and above the homs. *)
Definition p458_top_not_complete_below@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_below_IEM.

Definition p458_top_not_complete_below_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Complete@{r s h h} Top@{h Set} → False :=
  Top_not_complete_below_ObjDecEq.

Definition p458_top_not_complete_canonical@{e r s h o +| o < h, h <= s,
  s <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_IEM.

(* N30 *)
Fail Definition p458_top_not_complete_at_points@{e r h o +| o < h,
  h <= r +} :
  IEM@{e} → @Complete@{r o h h} Top@{h o} → False :=
  Top_not_complete_below_IEM@{e r o h o}.

(* N31 *)
Fail Definition p458_top_not_complete_canonical_below@{e r s h o +| o < s,
  s < h, h <= r +} :
  IEM@{e} → @Complete@{r s h h} Top@{h o} → False :=
  Top_not_complete_IEM.

(* CONTROL: completeness of [CompHaus] refuted under [IEM] at a shape
   universe strictly between the points and the homs; #455's form at and
   above the homs. *)
Definition p458_comphaus_not_complete_below@{e r s c h o +| o < s, s < h,
  h <= c, h <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_below_IEM.

Definition p458_comphaus_not_complete_canonical@{e r s c h o +| o < h,
  h <= s, h <= c, s <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_IEM_below.

(* N32 *)
Fail Definition p458_comphaus_canonical_below@{e r s c h o +| o < s, s < h,
  h <= c, h <= r +} :
  IEM@{e} → @Complete@{r s h c} (CompHaus : Category@{c h h}) → False :=
  CompHaus_not_complete_IEM_below.

(* CONTROL: products of [Top] refuted under [IEM] at an index universe
   strictly between the points and the homs. *)
Definition p458_top_iprod_refuted_below@{e s h o +| o < s, s < h +} :
  IEM@{e} → @HasIndexedProducts@{s s s h h h} Top@{h o} → False :=
  Top_iprod_refuted_below_IEM.

(* N33 *)
Fail Definition p458_top_iprod_below_at_points@{e h o +| o < h +} :
  IEM@{e} → @HasIndexedProducts@{o o o h h h} Top@{h o} → False :=
  Top_iprod_refuted_below_IEM@{e o h o}.

(* CONTROL: cocompleteness of [Top] refuted under [IEM] at a shape
   universe strictly between the points and the homs, under [ObjDecEq]
   with the points at [Set], and by Cantor's argument between the points
   and the homs as well, its [ObjDecEq] form with the points above
   [Set]. *)
Definition p458_top_not_cocomplete_between@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM.

Definition p458_top_not_cocomplete_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Cocomplete@{r s h h} Top@{h Set} → False :=
  Top_not_cocomplete_ObjDecEq.

Definition p458_top_not_cocomplete_cantor@{e r s h o +| o < s, s < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_Cantor_IEM.

Definition p458_top_cantor_objdeceq_above_set@{r s h o +| Set < o, o < s,
  s < h, h <= r +} :
  ObjDecEq Top@{h o} → @Cocomplete@{r s h h} Top@{h o} → False :=
  Top_not_cocomplete_Cantor_ObjDecEq.

(* N34 *)
Fail Definition p458_top_not_cocomplete_at_points@{e r h o +| o < h,
  h <= r +} :
  IEM@{e} → @Cocomplete@{r o h h} Top@{h o} → False :=
  Top_not_cocomplete_IEM@{e r o h o}.

(* N35 *)
Fail Definition p458_top_cantor_objdeceq_at_set@{r s h +| Set < s, s < h,
  h <= r +} :
  ObjDecEq Top@{h Set} → @Cocomplete@{r s h h} Top@{h Set} → False :=
  Top_not_cocomplete_Cantor_ObjDecEq.

(** ** Guard: every constant of the six targets *)

(* Instance/Top/Complete.v *)
Check PBoxTop.
Check PConv.
Check PDisc.
Check PDisc_PForget.
Check Complete.PDisc_obligation_1.
Check Complete.PDisc_obligation_2.
Check Complete.PDisc_obligation_3.
Check PForget_Continuous.
Check PForget_PreservesLimitCone.
Check PInit.
Check PInit_carrier.
Check PInit_one_PSub.
Check PInit_open.
Check PIsTopology.
Check PPair.
Check PPair_carrier.
Check PPair_open_iff_box.
Check PProd.
Check PProd_carrier.
Check PProd_open.
Check PTop_Cartesian.
Check PTop_Complete.
Check PTop_Complete_apex.
Check PTop_Complete_routes_iso.
Check PTop_Complete_routes_iso_legs.
Check PTop_Complete_via_products.
Check PTop_Complete_via_products_apex.
Check PTop_HasIndexedProducts.
Check PTop_IsIndexedProduct.
Check PTop_Limit_lift.
Check PTop_equalizer_open_iff_PSub.
Check PTop_iprod_open_iff_initial.
Check PTop_iprod_ump.
Check Complete.PTop_iprod_ump_obligation_1.
Check Complete.PTop_iprod_ump_obligation_2.
Check PTop_limit_open_iff_initial.
Check PTop_product_obj.
Check box_not_indexed_product.
Check equalizer_points_monic.
Check iprod_points_jointly_monic.
Check pair_box_union.
Check pair_box_union_topology.
Check pbox_all_false.
Check pbox_all_false_not_product_open.
Check pbox_all_false_open.
Check pbox_at.
Check pbox_no_mediator.
Check pbox_open.
Check pbox_open_inter.
Check pbox_open_proper.
Check pbox_open_respects.
Check pbox_open_union.
Check pbox_open_whole.
Check pbox_proj.
Check pbox_proj_cont.
Check pconv_ind.
Check pconv_ind_cont.
Check pconv_ind_map.
Check pconv_ind_mor.
Check pconv_limit_point_not_open.
Check pconv_open.
Check pconv_open_inter.
Check pconv_open_proper.
Check pconv_open_respects.
Check pconv_open_union.
Check pconv_open_whole.
Check pconv_prod_mediator.
Check pconv_setoid.
Check pdisc_forget_iso.
Check Complete.pdisc_forget_iso_obligation_1.
Check Complete.pdisc_forget_iso_obligation_2.
Check Complete.pdisc_forget_iso_obligation_3.
Check Complete.pdisc_forget_iso_obligation_4.
Check pinit_cone.
Check pinit_cone_leg.
Check pinit_cone_limiting.
Check pinit_cone_med_map.
Check pinit_cone_points.
Check pinit_leg.
Check pinit_leg_cont.
Check pinit_leg_map.
Check pinit_lift.
Check pinit_lift_map.
Check pinit_open.
Check pinit_open_inter.
Check pinit_open_proper.
Check pinit_open_respects.
Check pinit_open_union.
Check pinit_open_whole.
Check pinit_sub.
Check pinit_top.
Check pinit_universal.
Check pinit_weakest.
Check plimit_point.
Check plimit_point_cone.
Check plimit_points_jointly_monic.
Check popen_topology.
Check ppair_exl.
Check ppair_exr.
Check ppair_fam.
Check ppair_fork.
Check ppair_fork_map.
Check ppair_fst.
Check ppair_leg.
Check ppair_snd.
Check pprod_leg.
Check pprod_open_pbox_open.
Check pprod_tuple.
Check pproj.
Check pproper.
Check pproper_topology.
Check ptuple.

(* Instance/Top/Complete/ConeComma.v *)
Check ConeImage.
Check ConeImage_obj.
Check Ex3a_left_literal.
Check Ex3a_left_refuting_data.
Check PDiscCone.
Check PDiscCone_open.
Check PInitCone.
Check PInitCone_obj.
Check PTop_Complete_via_cones.
Check PTop_iprod_cone.
Check PTop_iprod_via_cones.
Check PTop_limit_via_cones.
Check PTop_products_via_cone_comma.
Check PTop_via_cones_apex.
Check PTop_via_cones_cone.
Check cone_adjoints_differ_at_empty_shape.
Check ex3_G1.
Check ex3_LeftAdj.
Check ConeComma.ex3_LeftAdj_obligation_1.
Check ConeComma.ex3_LeftAdj_obligation_2.
Check ConeComma.ex3_LeftAdj_obligation_3.
Check ConeComma.ex3_LeftAdj_obligation_4.
Check ex3_T0.
Check ex3_left_adj.
Check ex3_left_adj_iso.
Check ConeComma.ex3_left_adj_iso_obligation_1.
Check ConeComma.ex3_left_adj_iso_obligation_2.
Check ConeComma.ex3_left_adj_iso_obligation_3.
Check ConeComma.ex3_left_adj_iso_obligation_4.
Check ConeComma.ex3_left_adj_iso_obligation_5.
Check ConeComma.ex3_left_adj_iso_obligation_6.
Check ex3_point_cone.
Check ex3_point_limit.
Check ex3_point_terminal.
Check ConeComma.ex3_point_terminal_obligation_1.
Check ConeComma.ex3_point_terminal_obligation_2.
Check ex3_roof_cone.
Check ex3_roof_from_apex.
Check ex3_roof_no_limit.
Check ex3a_left_adjoint_literal_refuted.
Check ex3a_left_counterexample.
Check limit_from_cone_right_adjoint.
Check pbool_cone.
Check pcone_adj_iso.
Check ConeComma.pcone_adj_iso_obligation_1.
Check ConeComma.pcone_adj_iso_obligation_2.
Check ConeComma.pcone_adj_iso_obligation_3.
Check ConeComma.pcone_adj_iso_obligation_4.
Check ConeComma.pcone_adj_iso_obligation_5.
Check ConeComma.pcone_adj_iso_obligation_6.
Check ConeComma.pcone_adj_iso_obligation_7.
Check pcone_adjunction.
Check pdisc_cone.
Check pdisc_cone_adj_iso.
Check ConeComma.pdisc_cone_adj_iso_obligation_1.
Check ConeComma.pdisc_cone_adj_iso_obligation_2.
Check ConeComma.pdisc_cone_adj_iso_obligation_3.
Check ConeComma.pdisc_cone_adj_iso_obligation_4.
Check ConeComma.pdisc_cone_adj_iso_obligation_5.
Check ConeComma.pdisc_cone_adj_iso_obligation_6.
Check pdisc_cone_adjunction.
Check pempty_diagram.
Check puniform_topology.
Check terminal_of_right_adjoint.

(* Instance/Top/Complete/Refutations.v *)
Check CompHaus_not_complete_below_IEM.
Check PTop_ArrowIndex_transport.
Check PTop_iprod_refuted_IEM.
Check PTop_no_ArrowIndex_at_points.
Check PTop_no_ArrowIndex_below.
Check PTop_not_complete_Freyd.
Check PTop_not_complete_IEM.
Check PTop_not_complete_IEM_canonical.
Check PTop_not_complete_ObjDecEq.
Check Top_ArrowIndex_transport.
Check Top_iprod_refuted_IEM_canonical.
Check Top_iprod_refuted_below_IEM.
Check Top_not_complete_below_IEM.
Check Top_not_complete_below_ObjDecEq.
Check pbool_eval_pt.
Check pbool_eval_pt_resp.
Check top_rebuild.

(* Instance/Top/Cocomplete.v *)
Check PColimit.
Check PColimit_apex.
Check PColimit_inj.
Check PColimit_med_at.
Check PColimit_points.
Check PFinal.
Check PFinalCocone.
Check PFinalCocone_legs.
Check Cocomplete.PFinalCocone_obligation_1.
Check PFinalCocone_points.
Check PFinal_carrier.
Check PFinal_open.
Check PForget_Cocontinuous.
Check PForget_PIndisc.
Check PForget_PreservesColimitCocone.
Check PIndisc.
Check PIndisc_fobj.
Check Cocomplete.PIndisc_obligation_1.
Check Cocomplete.PIndisc_obligation_2.
Check Cocomplete.PIndisc_obligation_3.
Check PIndiscrete.
Check PIndiscrete_carrier.
Check PIndiscrete_open.
Check PSigma.
Check PSigma_open.
Check PSigma_points.
Check PTop_Cocomplete.
Check PTop_Cocomplete_routes_iso.
Check PTop_Cocomplete_routes_iso_injs.
Check PTop_Cocomplete_via_coproducts.
Check PTop_Cocomplete_via_coproducts_apex.
Check PTop_Colimit_lift.
Check PTop_Colimit_lift_apex.
Check PTop_HasIndexedCoproducts.
Check PTop_IsIndexedCoproduct.
Check PTop_colimit_open_iff_final.
Check PTwoIndisc.
Check PTwoIndiscSum.
Check PTwoIndiscSum_injections_differ.
Check PTwoIndiscSum_not_discrete.
Check PTwoIndiscSum_not_indiscrete.
Check PTwoIndiscSum_summand_open.
Check pfinal_cocone_colimiting.
Check pfinal_cocone_colimiting_reflect.
Check pfinal_cocone_inj.
Check pfinal_cocone_med_map.
Check pfinal_cocone_obj.
Check pfinal_desc.
Check pfinal_desc_map.
Check pfinal_finest.
Check pfinal_leg.
Check pfinal_leg_cont.
Check pfinal_leg_map.
Check pfinal_one_map_PQuot.
Check pfinal_open.
Check pfinal_open_inter.
Check pfinal_open_proper.
Check pfinal_open_respects.
Check pfinal_open_union.
Check pfinal_open_whole.
Check pfinal_universal.
Check pforget_indisc_iso.
Check Cocomplete.pforget_indisc_iso_obligation_1.
Check Cocomplete.pforget_indisc_iso_obligation_2.
Check Cocomplete.pforget_indisc_iso_obligation_3.
Check pindisc_cont.
Check pindisc_mor.
Check pindisc_mor_map.
Check pindisc_open.
Check pindisc_open_inter.
Check pindisc_open_proper.
Check pindisc_open_respects.
Check pindisc_open_union.
Check pindisc_open_whole.
Check psigma_case.
Check psigma_case_at.
Check psigma_desc.
Check psigma_inj.

(* Instance/Top/Cocomplete/Refutations.v *)
Check PTop_not_cocomplete_Cantor_IEM.
Check PTop_not_cocomplete_Cantor_ObjDecEq.
Check PTop_not_cocomplete_Freyd.
Check PTop_not_cocomplete_IEM.
Check PTop_not_cocomplete_ObjDecEq.
Check Sets_not_cocomplete_IEM.
Check Top_not_cocomplete_Cantor_IEM.
Check Top_not_cocomplete_Cantor_ObjDecEq.
Check Top_not_cocomplete_Freyd.
Check Top_not_cocomplete_IEM.
Check Top_not_cocomplete_ObjDecEq.
Check cocomp_cantor_diagonal.
Check pcc_Prop.
Check Refutations.pcc_Prop_obligation_1.
Check pcc_contradiction.
Check pcc_enc.
Check pcc_enc_inj.
Check pcc_index.
Check pcc_inj.
Check pcc_leg.
Check pcc_sep.
Check pcc_sep_at.
Check pcc_sum.
Check tcc_contradiction.
Check tcc_enc.
Check tcc_enc_inj.
Check tcc_index.
Check tcc_inj.
Check tcc_leg.
Check tcc_sep.
Check tcc_sep_at.
Check tcc_sum.

(* Instance/Top/Cocomplete/TypeValued.v *)
Check TSigma.
Check TSigma_carrier.
Check TSigma_open.
Check Top_HasCoequalizers.
Check Top_HasIndexedCoproducts_small.
Check Top_coequalizer_obj.
Check tcoeq_IsCoequalizer.
Check tcoeq_cofork.
Check tcoeq_desc.
Check tcoeq_med.
Check tcoeq_obj.
Check tcoeq_proj.
Check tsig_case.
Check tsig_case_cont.
Check tsig_desc.
Check tsig_inj.
Check tsig_open.
Check tsig_open_inter.
Check tsig_open_proper.
Check tsig_open_respects.
Check tsig_open_union.
Check tsig_open_whole.
Check tsig_setoid.
