(** * Probe for Mac Lane V.9's sliced adjoint inverses (issue #457)

    Pins the measured boundaries of the five files #457 adds for Mac Lane
    §V.9, book pp. 132-134 (catalog ids maclane:V.9:construction2, the
    subspace topology as a right-adjoint-right-inverse of the sliced
    underlying-set functor; maclane:V.9:construction3, the quotient
    topology as a left-adjoint-right-inverse of the cosliced one; and
    maclane:V.9:prop1, Proposition 1 with its dual; the book numbers only
    Proposition 1, and the ids are names, not book numbering) and for
    Seven Sketches' Exercise 7.32: Structure/SlicedInverse.v and its
    satellite Structure/SlicedInverse/Strict.v (Proposition 1 abstractly,
    where faithfulness is spent, and its refutation without it),
    Instance/Top/Prop.v (spaces with Prop-valued opens, the category
    [PTopCat] and its forgetful functor [PForget]),
    Instance/Top/Subspace.v (the two constructions over them, packaged,
    and the equalizers and coequalizers of [PTopCat] they give) and
    Instance/Top/Subspace/TypeValued.v (what of them is formable over the
    Type-valued [Top] of Instance/Top.v, and where the rest stops).  N1,
    N2, N7-N14, N18, N20, N21 and N25 restate a refusal that a target
    header records, measured by #457's builders, scouts and reviews in
    scratch files; N15-N17 and N26 restate the measurements behind the
    headers' account of the two [Sets] (N17 and N26 are
    Instance/Top/Forgetful.v's first wall, N26 at that file's own
    [Sets@{o so}]); N3-N6 and N19 are this file's own; N22-N24 are the
    scouts' measurements of encodings no target adopts.  The positive
    controls restate the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines by script.  First
    Structure/SlicedInverse/Strict.v's fifteen lines verbatim and in order,
    one of them the target Structure/SlicedInverse.v; then the four lines
    Structure/SlicedInverse.v adds, in its order
    (Theory/Universal/Arrow/Dual.v, Adjunction/Opposite.v,
    Adjunction/Determination.v, Structure/Equalizer/Fork.v); then the
    satellite itself; then the four lines Instance/Top/Subspace.v adds, in
    its order (Structure/Pullback/Reduction.v, Instance/Sets/Pullback.v,
    Instance/Sets/Coequalizer.v and the target Instance/Top/Prop.v, whose
    own four lines are already present), and Subspace.v itself; then the
    three lines Instance/Top/Subspace/TypeValued.v adds
    (Instance/Sets/Classifier.v, Instance/Top.v, Instance/Top/Forgetful.v)
    and TypeValued.v itself.  That is every [Require] of the five targets.
    One line is added for one section, Instance/Sets/Powerset.v, for the
    truncation [Powerset_squash] of the squashed subspace (N20-N22).  Thirty
    lines.  Two modules are named [Strict] (Theory/Equivalence/Strict.v and
    the satellite); the guard block's [Strict.] names resolve to the
    satellite ([Locate]), and no other command names either module.  A
    shorter import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and each of the one hundred and
    twenty-five definitions, examples, lemmas and records of this file that
    is not a refutation (seventy, forty-three, ten and two), wrapped in one
    in a copy of this WHOLE file, stops the build at that command with the
    report that the guarded command had been accepted (one hundred and
    twenty-five of one hundred and twenty-five, by a script over the
    copies).  Every negative other than that instrument and N7 is a
    [Definition] or an [Example], never a [Check], so that an open evar or a
    missing instance cannot satisfy it; N7 is a [Qed].  Each negative was
    stripped of its refutation keyword in a copy of this WHOLE file, one at
    a time, compiled, and its error read; each of the twenty-seven copies
    stops inside the stripped command (by the File line that precedes its
    error, compared by a script with the command's extent).  The kind
    recorded is the kind of that error, and each negative has positive
    controls beside it; every identifier a negative uses, its own name and
    the universes its binder names aside, is used by some positive control
    of this file (by a script over the identifiers of the commands, the
    guard block not counted).  In one further copy of this WHOLE file, each
    negative but the instrument and N7 was followed by a BINDER INSTRUMENT,
    the same universe binder, arguments and return type with a trivial body
    (a hypothesis of the return type, or [Datatypes.unit] where the command
    states none): all twenty-five are accepted, so every negative is refused
    by its body.  And each of the sixteen negatives whose binder declares
    constraints, N10-N12 and N14-N26, was rewritten in a copy of this WHOLE
    file with those constraints removed and the "+" kept: with its
    refutation keyword each copy compiles, and stripped of it each is
    refused at the same File line with the same clause (compared by a
    script, serial universe names aside), so no refusal rests on a
    constraint the binder alone declares.  N23's [s < o] is forced by its
    hypothesis [HV], whose type [p457_small_sub_open@{s o}] carries it.
    Every UNIVERSE negative is a top-level definition whose universes are
    declared in its own binder, never a [Section]'s; N8 and N9 declare none,
    their universes being [Set].  Quotations are Rocq 9.1.1's under this
    file's import list, with the error's environment block left out; Rocq
    prints the "cannot unify" parenthetical with the short names in scope,
    and a universe the stripped copy names after itself and a serial number
    is written <1>, <2>, ..., numbered afresh in each quotation in order of
    first appearance.  The file also compiles on Coq 8.19.2 and 8.20.1, with
    no warning, against the prebuilt trees of this library for those
    versions with the five targets compiled beside them from this tree.
    Under this import list the file's dependency closure is ninety-five
    [Category] modules ([Print Libraries]); of the ninety that are not
    targets, eighty-nine are this tree's byte for byte in both prebuilt
    trees (compared by [cmp]), and the ninetieth, Instance/Top.v, differs
    from both only by #457's CORRECTION sentences in its header comment, the
    prebuilt trees carrying the base commit's text.  The stripped copies
    were compiled there as well, and every one of the twenty-seven is
    refused on both at the File line of its Rocq 9.1.1 refusal.  Under
    8.20.1 every error is the Rocq 9.1.1 one up to the serial names; under
    8.19.2 all but N15-N17 and N26 are, those four printing the same type
    mismatch with no universe clause (compared by a script over the copies).

    KINDS.  Twenty-seven refutations, counted as the lines that open with
    the refutation keyword: NAME-ABSENCE (the instrument), CONVERSION (N1,
    N2, N10-N12, N19, N25), INSTANCE (N3-N6), SECTION-VARIABLE (N7) and
    UNIVERSE (N8, N9, N13-N18, N20-N24, N26): one, seven, four, one and
    fourteen.  No refusal is a BINDER one: every binder instrument is
    accepted.  The INSTANCE refusals carry the parenthetical "(no type
    class instance found)".  N20 and N22 are universe clauses whose other
    side is the sort [Prop]: the truncation eliminates only into
    propositions, as in Test/ProbeCompHaus413.v's N1.  N12 and N25 are
    unification refusals reported by the tactic that closes the body.

    LABELS.  The pins carry the N-numbers of this file; #457's scouts,
    builders and reviews measured most of them in scratch files under other
    names, recorded here so that the target headers can cite either.  Scout
    A's N1 and N2 are N13 and N14, its N3 is N23, its N4, N5 and N6 are N20,
    N21 and N22, its N7, N8 and N9 are N15, N16 and N17, its N10 is N24, its
    M1 is N8 (with the control [p457_psub_at_set]) and its M2 is N10 and
    N11.  Builder A's p2/V1 is N7 and its p6/M1 is N1.  Builder B's W1 is
    N10 and N11, its W2 is N13, its W3 N14 and its W4 N18; its union-design
    file's [m1_idx_union_at_Set], [idx_to_family_at_Set] and
    [m1_PSub_at_Set] are N8, N9 and [p457_psub_at_set]; its SqN4 and SqN5
    are N20 and N21; its and its review's flip of [psub_obj] to [Qed] is
    N12.  Builder A's review's LOW-5 (descent at [Erase Parallel] with no
    [Faithful]) is [p457_desc_at_erase], and builder B's review's LOW 8
    ([Top_Forget_under X y] is a lift) is [p457_forget_under_lift].  The
    stage-two review's flip of [tquot_obj_stripped] to [Qed] is N25, its N17
    at a fresh [so] is N26, and its same-shape controls for N4 and N6 are
    [p457_prop1_at_pforget] and [p457_prop1_dual_at_pforget].  The labels
    are not constants: each refutation carries its own in a comment on the
    line above it, the instrument's reading "The instrument".  N25 and N26,
    added after the rest, sit beside the negatives they extend, N26 after
    N17 and N25 after N19, so the body runs N1-N17, N26, N18, N19, N25,
    N20-N24.

    ** Structure/SlicedInverse.v and Structure/SlicedInverse/Strict.v

    N1 (CONVERSION).  Structure/SlicedInverse.v's header, Strengths: the
    book forms read the downstairs equalizer by projections so that their
    readbacks reach [eq_refl].  Proposition 1's object and arrow readbacks
    are restated ([p457_prop1_obj], [p457_prop1_arrow]), as is its
    reduction to the form over whole right adjoints applied to
    [rari_right] and [rari_adj] ([p457_prop1_by_adjoints], at [eq_refl]:
    the right-inverse clause is not consulted).  The same book form written
    with [destruct] on the downstairs equalizer ([p457_eq_by_match],
    formed) has its object readback refused, N1:
      The term "eq_refl" has type "projT1 (equalizer f g) = projT1
      (equalizer f g)" while it is expected to have type "projT1
      (equalizer f g) = projT1 (fobj[rari_right (L x)] (projT1 (equalizer
      (fmap[G] f) (fmap[G] g)); projT1 (projT2 (equalizer (fmap[G] f)
      (fmap[G] g)))))" (cannot unify "projT1 (equalizer f g)" and "projT1
      (fobj[rari_right (L x)] (projT1 (equalizer (fmap[G] f) (fmap[G] g));
      projT1 (projT2 (equalizer (fmap[G] f) (fmap[G] g)))))").

    N2 (CONVERSION).  The same header: [rari_over], that the lift sits
    over [S], is Leibniz but not [eq_refl], the field [rari_obj] being its
    only source at a variable right-adjoint-right-inverse.  It is restated
    at its Leibniz type ([p457_rari_over]), the equalizer's object
    readback [rari_eq_obj] is restated at [eq_refl] ([p457_rari_eq_obj]),
    and at [eq_refl], N2:
      The term "eq_refl" has type "fobj[G] (projT1 (fobj[rari_right L]
      (S; s))) = fobj[G] (projT1 (fobj[rari_right L] (S; s)))" while it is
      expected to have type "fobj[G] (projT1 (fobj[rari_right L] (S; s)))
      = S" (cannot unify "fobj[G] (projT1 (fobj[rari_right L] (S; s)))"
      and "S").

    N3-N6 (INSTANCE).  The same header, Where each hypothesis is spent:
    faithfulness is spent in the fork equation alone, and descent (the
    existence and uniqueness of the mediating arrow) takes none.  Pinned
    at the countermodel [Erase Parallel], where no [Faithful] instance
    exists and faithfulness is refuted ([Erase_Parallel_not_faithful]):
    with the equalizer [p457_erase_eq] of the erased pair in [_1] and the
    couniversal arrow [p457_erase_U] of [erase_slice_RARI], descent is
    applied there with no [Faithful] in scope ([p457_desc_at_erase]), and
    the fork equation of the lift is false there
    ([p457_fork_refuted_at_erase], closed); so is the dual cofork
    ([p457_codesc_at_erase], [p457_cofork_refuted_at_erase], over
    [p457_erase_coeq] and [p457_erase_V]).  The lemmas [sliced_fork] and
    [cosliced_cofork] (restated with faithfulness, [p457_cofork] and N7's
    lemma) and the book forms [equalizers_from_sliced_RARI] and
    [coequalizers_from_sliced_LARI] are applied there with the
    faithfulness argument left to resolution, N3, N4, N5 and N6, each:
      ?GF: Cannot infer this placeholder of type "Faithful (Erase
      Parallel)" (no type class instance found).
    after "The following term contains unresolved implicit arguments:"
    and the term.  The same two book forms applied the same way at
    [PForget], where resolution finds [PForget_Faithful], are formed
    ([p457_prop1_at_pforget], [p457_prop1_dual_at_pforget]) and ARE
    Instance/Top/Subspace.v's [PTop_HasEqualizers] and
    [PTop_HasCoequalizers], at [eq_refl]
    ([p457_prop1_at_pforget_is_ptop],
    [p457_prop1_dual_at_pforget_is_ptop]).  The refutations are restated
    at their stated types ([p457_prop1_needs_faithfulness],
    [p457_prop1_dual_needs_faithfulness]).

    N7 (SECTION-VARIABLE).  Builder A's measurement of the same boundary
    by [Proof using].  In a section declaring [E], [U] and the instance
    [GF] as Structure/SlicedInverse.v's [SlicedEqualizer] does, descent
    closes under [Proof using E U] from the constant [sliced_desc]
    ([p457_desc_using]); the fork equation from the constant
    [sliced_fork], under [Proof using E U], has its [Qed] refused, N7:
      The following section variable is used but not declared: GF.
    and the same statement, with faithfulness a hypothesis in place of the
    section's instance, closes under [Proof using E U]
    ([p457_fork_using]).  The refused proof is discarded by [Restart],
    which Rocq warns about in batch mode; that warning is switched off
    for the section alone.

    Controls of the rest of the two files: [p457_sliced_fobj] and
    [p457_cosliced_fobj] (the sliced functors' object maps at
    [eq_refl]), [p457_prop1] and [p457_prop1_dual] (Proposition 1 and its
    dual at their stated types), [p457_prop1_dual_obj] (the dual's object
    readback at [eq_refl]) and [p457_rari_lali_rari] (the round trip
    through left-adjoint-left-inverses at [eq_refl]).

    ** Instance/Top/Prop.v

    Controls.  The homs of [PTopCat] sit at the points' universe:
    [PMor X Y] is ascribed [Type@{o}] under the CLOSED binder [@{o}]
    ([p457_pmor_at_o]), where Test/ProbeStoneCech455.v's N6 refuses
    Instance/Top.v's [ContinuousMorphism].  [PTopCat@{o so}] is a
    [Category@{so o o}] and [PForget@{o so}] lands in [Sets@{o so}], the
    [Sets] whose objects are the point setoids, both under a binder that
    names [o] and [so] only ([p457_ptopcat], [p457_pforget]); its object
    and arrow readbacks hold at [eq_refl] ([p457_pforget_fobj],
    [p457_pforget_fmap]) and its faithfulness is found by resolution
    ([p457_pforget_faithful]).  Compare N17 and N26.

    Controls of the concrete spaces.  The discrete space's points and opens
    read back at [eq_refl] under the CLOSED binder [@{o}]
    ([p457_pdiscrete_carrier], [p457_pdiscrete_open],
    [p457_pdisc_open_body]), its five axioms are formed
    ([p457_pdisc_axioms]), every setoid map out of it is continuous
    ([p457_pdisc_cont]) and becomes an arrow with that map as its
    underlying one ([p457_pdisc_mor_map]); the constant map computes
    ([p457_pconst_at]); [PPoint] and [PBool] are the discrete spaces on
    Instance/Sets.v's one- and two-point setoids ([p457_ppoint],
    [p457_pbool], at [eq_refl] under [@{o}]), and [PBool]'s two points are
    distinct ([p457_pbool_points_distinct]).

    N8, N9 (UNIVERSE).  Instance/Top/Prop.v's header, THE UNION AXIOM,
    MEASURED BOTH WAYS.  Design (a), unions over an index type at the
    points' universe, is the record [p457_PTopIdx].  The index of the
    subspace's union witness under (a), (index, open) pairs
    ([p457_idx_witness_index]), is a union index above [Set]
    ([p457_idx_union_above], under [Set < o]); at [Set], N8:
      The term "p457_idx_witness_index X S h I V" has type "Type" while it
      is expected to have type "Set" (universe inconsistency: Cannot
      enforce Set+1 <= Set).
    Design (a) gives the chosen design (b) above [Set]
    ([p457_idx_to_family]); the direct derivation at [Set], N9:
      The term "{U : X → Prop | F U}" has type "Type" while it is expected
      to have type "Set" (universe inconsistency: Cannot enforce Set+1 <=
      Set).
    Under (b) the subspace is formed at [PTop@{Set}] ([p457_psub_at_set])
    and (a) holds at every index universe, under the CLOSED binder
    [@{o i}] ([p457_union_indexed], restating [popen_union_indexed]).
    That (b) is strictly stronger than (a) at [Set] is not claimed here or
    there.

    ** Instance/Top/Subspace.v

    Controls.  The subspace's opens are the book's verbatim, at [eq_refl]
    under the CLOSED binder [@{o}] ([p457_psub_open]); the universal
    properties over ARBITRARY spaces mapping in and out
    ([p457_psub_universal], [p457_pquot_universal]); Exercise 7.32's
    definition at [eq_refl] ([p457_ex732_def]) and its part 3
    ([p457_ex732_part3]).

    N10, N11 (CONVERSION).  Instance/Top/Subspace.v's header, STRENGTHS: the
    object equations, that the sliced forgetful functor after [L] (and the
    cosliced one after [M]) is the identity on objects, are Leibniz and
    not [eq_refl] at a variable, slice objects being stdlib [sigT] pairs
    with no eta.  They are stated here at Structure/SlicedInverse.v's
    [Sliced PForget X] and [Cosliced PForget X], the functors Proposition
    1 and its dual consume.  At an explicit pair they hold at [eq_refl]
    ([p457_psub_obj_pair], [p457_pquot_obj_pair]), at a variable the first
    component does ([p457_psub_obj_carrier]), and the equations hold by
    [psub_obj] and [pquot_obj] ([p457_psub_obj], [p457_pquot_obj]).  At
    [eq_refl] and a variable, N10:
      The term "eq_refl" has type "fobj[Sliced PForget X] (fobj[PSub_Functor
      X] c) = fobj[Sliced PForget X] (fobj[PSub_Functor X] c)" while it is
      expected to have type "fobj[Sliced PForget X] (fobj[PSub_Functor X]
      c) = c" (cannot unify "fobj[Sliced PForget X] (fobj[PSub_Functor X]
      c)" and "c").
    and N11 the same with [Cosliced] and [PQuot_Functor].

    N12 (CONVERSION).  The same header: [psub_obj] is [Defined] because
    the counit's triangle fact needs its transport to reduce.  The counit
    is [id_cast] of [psub_obj] by the tactic [psub_counit] is proved with
    ([p457_psub_counit]); with the same equation closed [Qed]
    ([p457_psub_obj_opaque]), N12:
      Unable to unify "projT1 (id_cast (p457_psub_obj_opaque X (x; h)))
      t" with "t".

    Controls of the packaging and of the witnesses.  [subspace_RARI] and
    [quotient_LARI] at the types #457's plan states, [∀ X : PTop@{o},
    RightAdjointRightInverse (Sliced PForget@{o so} X)] and [∀ X :
    PTop@{o}, LeftAdjointRightInverse (Cosliced PForget@{o so} X)]
    ([p457_subspace_RARI], [p457_quotient_LARI]), with [rari_right],
    [rari_obj] and [lari_left] read back at [eq_refl] as [PSub_Functor X],
    [psub_obj X] and [PQuot_Functor X] ([p457_subspace_RARI_right],
    [p457_subspace_RARI_obj], [p457_quotient_LARI_left]).
    [PTop_HasEqualizers] and [PTop_HasCoequalizers] at
    [@HasEqualizers PTopCat@{o so}] and [@HasCoequalizers PTopCat@{o so}]
    ([p457_ptop_equalizers], [p457_ptop_coequalizers]; that they are the
    book forms at [PForget] is under N3-N6).  The four readbacks restated
    at [eq_refl]: the equalizer is [PSub] on the equalizer in [Sets] and
    its arrow [psub_incl], the coequalizer is [PQuot] on the coequalizer
    in [Sets] and its arrow [pquot_proj] ([p457_ptop_equalizer_obj],
    [p457_ptop_equalizer_arrow], [p457_ptop_coequalizer_obj],
    [p457_ptop_coequalizer_arrow]); and the equalizer object is the value
    of [rari_right (subspace_RARI x)] at the downstairs equalizer, as
    Proposition 1 builds it ([p457_ptop_equalizer_rari]).

    Controls of the witnesses at concrete spaces.  The two constructions at
    [PBool] at their types, their adjoints read back at [eq_refl]
    ([p457_pbool_subspace_RARI], [p457_pbool_quotient_LARI],
    [p457_pbool_subspace_RARI_right], [p457_pbool_quotient_LARI_left]).
    The two pairs are pairs of different maps: the constant [pbool_true]
    against the identity of [PBool], and the two points of [PBool] out of
    [PPoint] ([p457_pbool_true_map], [p457_pbool_maps_differ],
    [p457_ppoint_maps], [p457_ppoint_maps_differ]).  The equalizer of the
    first is [PSub PBool] on the equalizer in [Sets] and the value of
    [rari_right] of the subspace construction at [PBool] there
    ([p457_pbool_equalizer_obj], [p457_pbool_equalizer_rari], at
    [eq_refl]), and exactly [true] lies in it
    ([p457_pbool_equalizer_points]); the coequalizer of the second is
    [PQuot PBool] on the coequalizer in [Sets] and the value of
    [lari_left] of the quotient construction at [PBool] there
    ([p457_pbool_coequalizer_obj], [p457_pbool_coequalizer_lari], at
    [eq_refl]), and every point is identified with [true] in it
    ([p457_pbool_coequalizer_points]).

    ** Instance/Top/Subspace/TypeValued.v

    N13 (UNIVERSE).  TypeValued.v's header, THE SUBSPACE DOES NOT: the
    book's predicate, quantifying over the opens of X, is formed one
    universe up ([p457_tsub_open], restating [tsub_open] at [o < o1], and
    [p457_tsub_open_body], its body there); at [Type@{o}], N13:
      The term "∃ U : X → Type, IsOpen X U ∧ ∀ s : S, V s ↔ U (h s)" has
      type "Type@{max(o+1,<1>,<2>)}" while it is expected to have type
      "Type@{o}" (universe inconsistency: Cannot enforce o < o because o =
      o).

    N14 (UNIVERSE).  The same: supplied as the [IsOpen] of a
    [TopSpace@{o}] it is refused.  Its five axioms are formed
    ([p457_tsub_axioms]), and the same record literal at the quotient's
    opens is a [TopSpace@{o}] ([p457_tquot_package]; [p457_tquot] restates
    [TQuot]); N14:
      The term "tsub_open X S h" has type "(S → Type@{o}) → Type@{o1}"
      while it is expected to have type "(S → Type@{o}) → Type@{o}"
      (universe inconsistency: Cannot enforce o1 <= o because o < o1).
    The universal properties over ARBITRARY spaces are restated
    ([p457_tsub_universal], [p457_tquot_universal]).

    N15-N17, N26 (UNIVERSE).  The same header, THE SLICED FUNCTORS: the
    sliced underlying-set functors at Instance/Top/Forgetful.v's
    [Top_Forget] land in the slices of the LIFTED [Sets@{h so}].  An
    object of the slice of the unlifted [Sets@{o so}] carries the discrete
    topology at the points' universe ([p457_unlifted_slice_space]) and one
    of the lifted slice carries it one universe up
    ([p457_lifted_slice_space_h]); at the points' universe, N15:
      The term "Discrete_Top `1 (x)" has type "TopSpace@{h}" while it is
      expected to have type "TopSpace@{o}" (universe inconsistency: Cannot
      enforce h = o because o < h).
    and N16 the same for the coslice, whose controls are
    [p457_unlifted_coslice_space] and [p457_lifted_coslice_space_h].
    [Top_Forget] is restated into the lifted [Sets] ([p457_top_forget]);
    the TYPE of a functor from [Top@{h o}] into a [Sets] whose objects are
    the point setoids, Instance/Top/Forgetful.v's first wall, is not
    formed, N17:
      The term "Sets" has type "Category@{h o o}" while it is expected to
      have type "Category@{<1> <2> <3>}" (universe inconsistency: Cannot
      enforce o = <2> because o < h <= <2>).
    N17 takes the universe of that [Sets]'s objects to be [h]; at
    Forgetful.v's own [Sets@{o so}], [so] fresh, the type into the lifted
    [Sets@{h so}] is formed ([p457_top_to_lifted_sets]) and the type into
    [Sets@{o so}] is not, N26:
      The term "Sets" has type "Category@{so o o}" while it is expected to
      have type "Category@{<1> <2> <3>}" (universe inconsistency: Cannot
      enforce o = <2> because o < h <= <2>).

    N18 (UNIVERSE).  The same header: the adjunction
    [TQuot_Functor X ⊣ Top_Forget_under X] is refused.  Each functor is
    formed ([p457_tquot_functor], [p457_top_forget_under]), the
    transposition between them is the identity on underlying maps
    ([p457_tquot_adj_to_map], at [eq_refl]), and [Top_Forget_under X y] is
    the lift of [tstrip_under X y] ([p457_forget_under_lift], at
    [eq_refl]); the adjunction's type, N18:
      The term "TQuot_Functor X" has type "@Functor@{so o o h h h}
      (Coslice@{so so h o} Sets@{o so} (top_carrier X)) (Coslice@{h h <1>
      h} Top@{h o} X)" while it is expected to have type
      "@Functor@{<2> <3> <3> <4> <3> <3>} ?D ?C" (universe inconsistency:
      Cannot enforce h = o because o < h).
    The adjunction asks its two categories for one hom universe
    (Theory/Adjunction.v's [Adjunction], [About]: [h1 = h2]); the
    quotient functor's domain has its homs at [o] and its codomain at
    [h].

    N19 (CONVERSION).  The same header, STRENGTHS: [tquot_obj_stripped]
    is Leibniz by [destruct].  At a pair it holds at [eq_refl]
    ([p457_tquot_obj_stripped_pair]) and at a variable by the lemma
    ([p457_tquot_obj_stripped]); at [eq_refl] and a variable, N19:
      The term "eq_refl" has type "tstrip_under X (fobj[TQuot_Functor X]
      c) = tstrip_under X (fobj[TQuot_Functor X] c)" while it is expected
      to have type "tstrip_under X (fobj[TQuot_Functor X] c) = c" (cannot
      unify "tstrip_under X (fobj[TQuot_Functor X] c)" and "c").

    N25 (CONVERSION).  The same paragraph: [tquot_obj_stripped] is
    [Defined], and load-bearing.  The transposed identity is [id_cast] of
    its inverse by the tactic [tquot_unit_stripped] is proved with
    ([p457_tquot_unit]); with the same equation closed [Qed]
    ([p457_tquot_obj_stripped_opaque]), N25:
      Unable to unify "projT1 (id_cast (Compat.eq_sym
      (p457_tquot_obj_stripped_opaque X (x; h)))) t" with "t".
    Rocq prints the constant [eq_sym] through its abbreviation
    [Compat.eq_sym] of Lib/Tactics.v.

    N20-N22 (UNIVERSE).  The same header: a squashed, local encoding fits
    in a [TopSpace@{o}] and is not stated there, the "if" half of its
    universal property being refused along both routes a proof would
    take.  The encoding is rebuilt here from #457's scouting prototype:
    [p457_sq_box] (an open of X around the image of a point, with its
    preimage inside V, at [o1]), [p457_sq_open] (V respects [≈] and each
    of its points MERELY has a box) and [p457_sq_subspace], a
    [TopSpace@{o}] with [h] continuous out of it ([p457_sq_h_cont]) and
    the "only if" half ([p457_sq_only_if]).  Its opens include the book's,
    [tsub_open], for predicates respecting the points' equality
    ([p457_sq_global_to_local]).  The truncation eliminates into a
    proposition ([p457_sq_elim_prop]); into the Type-valued [IsOpen Z],
    the first route, N20:
      The term "IsOpen Z (λ z : Z, V (g z))" has type "Type" while it is
      expected to have type "Prop" (universe inconsistency: Cannot enforce
      o <= Prop).
    A union indexed by the points of Z is a union ([p457_union_by_points]);
    one indexed by the box data, the second route, N21:
      The term "p457_sq_box X S h V (g z0)" has type "Type@{o1}" while it
      is expected to have type "Type@{o}" (universe inconsistency: Cannot
      enforce o1 <= o because o < o1).
    And the local form does not give back the book's global witness, N22:
      The term "∃ U : X → Type, IsOpen X U ∧ ∀ s : S, V s ↔ U (h s)" has
      type "Type" while it is expected to have type "Prop" (universe
      inconsistency: Cannot enforce max(o+1, <1>, <2>) <= Prop).
    That the squashed encoding is not the subspace topology is not a
    theorem here: two proof routes are refused, nothing more.

    N23, N24 (UNIVERSE).  Two further encodings, neither adopted by a
    target.  Instance/Top/Kolmogorov.v's small-opens idea puts the
    predicate at [o] when the opens quantified over are valued at [s < o]
    ([p457_small_sub_open]), and, given an open [HV] of that encoding,
    whose type forces [s < o], a union of [s]-valued witnesses over an
    index at [s] is [s]-valued ([p457_small_union_at_s]); over an index at
    [o], the index [open_union] takes, N23:
      The term "∃ i : I, U i x" has type "Type@{max(s,o)}" while it is
      expected to have type "Type@{s}" (universe inconsistency: Cannot
      enforce o <= s because s < o).
    A two-level record whose opens are valued one universe above the
    points ([p457_Top2]) hosts the book's predicate ([p457_sub2_open]),
    but its continuity is a type one universe up ([p457_cont2]); at the
    points' universe, N24:
      The term "∀ U : Y → Type, p457_IsOpen2 Y U → p457_IsOpen2 X (λ x :
      X, U (f x))" has type "Type@{max(o+1,o1)}" while it is expected to
      have type "Type@{o}" (universe inconsistency: Cannot enforce o < o
      because o = o).
    So that encoding moves the subspace's wall and keeps the homs above
    the points.

    NOT PINNED HERE.  (a) [About] readbacks as such: the constraint blocks
    the headers list, the donors Structure/SlicedInverse.v's Universes
    section isolates, and the minimization of the unannotated
    [One_HasEqualizers] to a [Set] hom level; pinned here only where a
    CLOSED binder carries them ([p457_pmor_at_o], [p457_psub_open],
    [p457_union_indexed] and the controls of the concrete spaces under
    [@{o}]) or a refusal does.  (b) Flip censuses ([Defined] against
    [Qed]) other than N12's and N25's, among them builder B's review's
    measurement that [psub_adjunction] and [pquot_adjunction] closed [Qed]
    refuse the triangle facts and Instance/Top/Prop.v's measurement that
    [PDiscrete] built in proof mode and closed [Qed] refuses its points'
    readback at [eq_refl], and the closure of the targets under [Print
    Assumptions]: measurements of the build rather than of commands; the
    Makefile's print-assumptions gate is where closure is kept.  (c) The
    universal property of Instance/Top/Presheaf.v's [OpenSub], re-derived
    in #457's scratch files: Presheaf.v requires the stdlib reals, which no
    target imports.  (d) The sliced functor in comma form,
    Construction/Comma/Functorial.v's [Comma_reindex] at [Top_Forget],
    measured by #457's scouts and cited by Structure/SlicedInverse.v.

    The guard block at the end names the three hundred and forty-three
    constants of the five targets, so that a rename breaks this file:
    seventy-three of Structure/SlicedInverse.v, thirty-nine of
    Structure/SlicedInverse/Strict.v, fifty-one of Instance/Top/Prop.v,
    one hundred and eleven of Instance/Top/Subspace.v and sixty-nine of
    Instance/Top/Subspace/TypeValued.v.  They are the [def], [prf],
    [proj], [rec] and [inst] entries of the targets' .glob files (two
    hundred and fifty; the [abbrev] entries, the local notations [B],
    [PT], [G] and [SetsEq], left out), the ninety [Program] obligations
    and the three record constructors, which is exactly the list
    [Print Module] gives for each (compared by script); the three records
    have no elimination scheme ([Locate] of the [_rect], [_ind], [_rec],
    [_sind] and [_cases] names finds none).  The obligations are not
    reachable by their short names under this import list; each is named
    by the shortest qualified name [Locate] gives for it,
    Instance/Top/Prop.v's by [Top.Prop.], [Prop] being a keyword.  Under
    the full import list, [Locate] lists exactly one object for each of
    the three hundred and forty-three. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.One.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Structure.SlicedInverse.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Determination.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.SlicedInverse.Strict.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Sets.Powerset.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

(* The instrument *)
Fail Check probe457_absent_name.

(** ** Structure/SlicedInverse.v: the sliced functors and Proposition 1 *)

(* CONTROL: [Sliced_fobj] and [Cosliced_fobj], restated. *)
Example p457_sliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Slice A a) :
  Sliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

Example p457_cosliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Coslice A a) :
  Cosliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

(* CONTROL: Proposition 1, restated at its stated type; it IS the form
   over whole right adjoints applied to [rari_right] and [rari_adj]. *)
Definition p457_prop1@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) : @HasEqualizers A :=
  equalizers_from_sliced_RARI G L.

Example p457_prop1_by_adjoints@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) :
  equalizers_from_sliced_RARI G L
    = equalizers_from_sliced_right_adjoints G (fun a => rari_right (L a))
        (fun a => rari_adj (L a)) := eq_refl.

(* CONTROL: the readbacks of [equalizers_from_sliced_RARI_obj] and
   [_arrow], restated: the equalizer built IS the lift of the downstairs
   one. *)
Example p457_prop1_obj@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g)
    = `1 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example p457_prop1_arrow@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (`2 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g))
    = `2 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* The same book form with the downstairs equalizer read by [destruct],
   builder A's out-of-tree measurement restated. *)
Definition p457_eq_by_match@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) : @HasEqualizers A.
Proof.
  constructor; intros x y f g.
  destruct (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g)) as [S [s E]].
  pose (U := adj_counit_couniversal (rari_adj (L x))
               ((S; s) : @Slice X (G x))).
  exact (sliced_eq_obj G s U;
         (sliced_eq_arrow G s U; sliced_equalizer G f g s E U)).
Defined.

(* N1 *)
Fail Example p457_eq_by_match_obj@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@equalizer A (p457_eq_by_match G L) x y f g)
    = `1 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* CONTROL: [rari_eq_obj] restated, and [rari_over] at its Leibniz type. *)
Example p457_rari_eq_obj@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) {x y : A} (f g : x ~> y) {S : X}
  (s : S ~> G x) (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s)
  (L : RightAdjointRightInverse (Sliced G x)) :
  sliced_eq_obj G s (rari_couniversal G s L) = `1 (rari_right L (S; s)) :=
  eq_refl.

Definition p457_rari_over@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) {x : A} {S : X} (s : S ~> G x)
  (L : RightAdjointRightInverse (Sliced G x)) :
  G (`1 (rari_right L (S; s))) = S :=
  rari_over G s L.

(* N2 *)
Fail Example p457_rari_over_refl@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) {x : A} {S : X} (s : S ~> G x)
  (L : RightAdjointRightInverse (Sliced G x)) :
  G (`1 (rari_right L (S; s))) = S := eq_refl.

(** ** Structure/SlicedInverse.v: where faithfulness is spent *)

(* The countermodel's data: an equalizer in [_1] of the erased pair, and
   the couniversal arrow of the right-adjoint-right-inverse at [ParX]. *)
Definition p457_erase_eq :=
  @equalizer _1 One_HasEqualizers _ _
    (fmap[Erase Parallel] par_arrow_one) (fmap[Erase Parallel] par_arrow_two).

Definition p457_erase_U :=
  rari_couniversal (Erase Parallel) (`1 (`2 p457_erase_eq))
    (erase_slice_RARI ParX).

(* CONTROL: descent at [Erase Parallel], where no [Faithful] instance
   exists: [sliced_desc] takes none. *)
Definition p457_desc_at_erase :=
  @sliced_desc _ _ (Erase Parallel) ParX ParY par_arrow_one par_arrow_two
    _ (`1 (`2 p457_erase_eq)) (`2 (`2 p457_erase_eq)) p457_erase_U.

(* CONTROL: the fork equation of the lift is FALSE there. *)
Definition p457_fork_refuted_at_erase :
  par_arrow_one
    ∘ sliced_eq_arrow (Erase Parallel) (`1 (`2 p457_erase_eq)) p457_erase_U
  ≈ par_arrow_two
    ∘ sliced_eq_arrow (Erase Parallel) (`1 (`2 p457_erase_eq)) p457_erase_U
  → False :=
  parallel_pair_unforked _.

(* N3 *)
Fail Definition p457_fork_at_erase :=
  @sliced_fork _ _ (Erase Parallel) ParX ParY par_arrow_one par_arrow_two
    _ (`1 (`2 p457_erase_eq)) (`2 (`2 p457_erase_eq)) p457_erase_U _.

(* CONTROL: the same application at [PForget], its faithfulness found by
   resolution, IS Instance/Top/Subspace.v's [PTop_HasEqualizers]. *)
Definition p457_prop1_at_pforget@{o so +| o < so +} :=
  @equalizers_from_sliced_RARI _ _ PForget@{o so} _
    (@HasEqualizers_of_HasPullbacks_Terminal Sets Sets_Terminal
       Sets_HasPullbacks)
    subspace_RARI.

Example p457_prop1_at_pforget_is_ptop@{o so +| o < so +} :
  @eq (@HasEqualizers PTopCat@{o so}) p457_prop1_at_pforget
    PTop_HasEqualizers := eq_refl.

(* N4 *)
Fail Definition p457_prop1_at_erase :=
  @equalizers_from_sliced_RARI _ _ (Erase Parallel) _ One_HasEqualizers
    erase_slice_RARI.

(* The dual, over [Erase Parallel]'s coslices. *)
Definition p457_erase_coeq :=
  @coeq _1 One_HasCoequalizers _ _
    (fmap[Erase Parallel] par_arrow_one) (fmap[Erase Parallel] par_arrow_two).

Definition p457_erase_V :=
  lari_universal (Erase Parallel) (`1 (`2 p457_erase_coeq))
    (erase_coslice_LARI ParY).

Definition p457_codesc_at_erase :=
  @cosliced_desc _ _ (Erase Parallel) ParX ParY par_arrow_one par_arrow_two
    _ (`1 (`2 p457_erase_coeq)) (`2 (`2 p457_erase_coeq)) p457_erase_V.

Definition p457_cofork_refuted_at_erase :
  cosliced_coeq_arrow (Erase Parallel) (`1 (`2 p457_erase_coeq)) p457_erase_V
    ∘ par_arrow_one
  ≈ cosliced_coeq_arrow (Erase Parallel) (`1 (`2 p457_erase_coeq))
      p457_erase_V ∘ par_arrow_two
  → False :=
  parallel_pair_uncoforked _.

(* CONTROL: the cofork lemma, at its stated type, with faithfulness. *)
Definition p457_cofork@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) {x y : A} (f g : x ~> y) {Q : X}
  (q : G y ~> Q) (E : IsCoequalizer (fmap[G] f) (fmap[G] g) Q q)
  (U : UniversalArrow ((Q; q) : @Coslice X (G y)) (Cosliced G y))
  `{GF : @Faithful A X G} :
  cosliced_coeq_arrow G q U ∘ f ≈ cosliced_coeq_arrow G q U ∘ g :=
  cosliced_cofork G f g q E U.

(* N5 *)
Fail Definition p457_cofork_at_erase :=
  @cosliced_cofork _ _ (Erase Parallel) ParX ParY par_arrow_one par_arrow_two
    _ (`1 (`2 p457_erase_coeq)) (`2 (`2 p457_erase_coeq)) p457_erase_V _.

(* CONTROL: the same application at [PForget] IS
   [PTop_HasCoequalizers]. *)
Definition p457_prop1_dual_at_pforget@{o so +| o < so +} :=
  @coequalizers_from_sliced_LARI _ _ PForget@{o so} _ Sets_HasCoequalizers
    quotient_LARI.

Example p457_prop1_dual_at_pforget_is_ptop@{o so +| o < so +} :
  @eq (@HasCoequalizers PTopCat@{o so}) p457_prop1_dual_at_pforget
    PTop_HasCoequalizers := eq_refl.

(* N6 *)
Fail Definition p457_prop1_dual_at_erase :=
  @coequalizers_from_sliced_LARI _ _ (Erase Parallel) _ One_HasCoequalizers
    erase_coslice_LARI.

(* The same boundary read by [Proof using], builder A's measurement. *)
Section ForkUsing.

Local Set Warnings "-undo-batch-mode".

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {S : X} (s : S ~> G x).
Context (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s).
Context (U : CouniversalArrow ((S; s) : @Slice X (G x)) (Sliced G x)).
Context `{GF : @Faithful A X G}.

(* CONTROL: descent under [Proof using E U]. *)
Lemma p457_desc_using {z : A} (k : z ~> x) (Hk : f ∘ k ≈ g ∘ k) :
  ∃! u : z ~> sliced_eq_obj G s U, sliced_eq_arrow G s U ∘ u ≈ k.
Proof using E U. exact (sliced_desc G f g s E U k Hk). Qed.

Lemma p457_fork_using :
  Faithful G → f ∘ sliced_eq_arrow G s U ≈ g ∘ sliced_eq_arrow G s U.
Proof using E U.
  intros _. exact (sliced_fork G f g s E U).
(* N7 *)
Fail Qed.
Restart.
  intros GF'. exact (@sliced_fork _ _ G _ _ f g _ s E U GF').
Qed.

End ForkUsing.

(** ** Structure/SlicedInverse.v and its satellite: the refutations *)

(* CONTROL: [prop1_needs_faithfulness] and the satellite's dual, restated. *)
Definition p457_prop1_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasEqualizers X →
     (∀ a : A, RightAdjointRightInverse (Sliced G a)) → @HasEqualizers A)
  → False :=
  prop1_needs_faithfulness.

Definition p457_prop1_dual_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasCoequalizers X →
     (∀ a : A, LeftAdjointRightInverse (Cosliced G a)) → @HasCoequalizers A)
  → False :=
  prop1_dual_needs_faithfulness.

(** ** Structure/SlicedInverse/Strict.v: the bridge and the dual form *)

(* CONTROL: the round trip, and the dual's object readback, restated. *)
Example p457_rari_lali_rari@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} {S : A ⟶ C} (P : RightAdjointRightInverse S) :
  lali_rari (rari_lali P) = P := eq_refl.

Definition p457_prop1_dual@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) :
  @HasCoequalizers A :=
  coequalizers_from_sliced_LARI G L.

Example p457_prop1_dual_obj@{oA oX h +} {A : Category@{oA h h}}
  {X : Category@{oX h h}} (G : A ⟶ X) `{GF : @Faithful A X G}
  `{HX : @HasCoequalizers X}
  (L : ∀ a : A, LeftAdjointRightInverse (Cosliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@coeq A (coequalizers_from_sliced_LARI G L) x y f g)
    = `1 (lari_left (L y)
            (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(** ** Instance/Top/Prop.v: the category and its forgetful functor *)

(* CONTROL: the homs sit at the points' universe, under the CLOSED binder
   [@{o}]; the category and the forgetful functor land in ONE [Sets]. *)
Definition p457_pmor_at_o@{o} (X Y : PTop@{o}) : Type@{o} := PMor@{o} X Y.

Definition p457_ptopcat@{o so | o < so +} : Category@{so o o} :=
  PTopCat@{o so}.

Definition p457_pforget@{o so | o < so +} : PTopCat@{o so} ⟶ Sets@{o so} :=
  PForget@{o so}.

Example p457_pforget_fobj@{o so | o < so +} (X : PTop@{o}) :
  fobj[PForget@{o so}] X = pt_carrier X := eq_refl.

Example p457_pforget_fmap@{o so | o < so +} {X Y : PTop@{o}}
  (f : X ~{PTopCat@{o so}}~> Y) : fmap[PForget@{o so}] f = pmap f := eq_refl.

Definition p457_pforget_faithful@{o so | o < so +} :
  Faithful PForget@{o so} := _.

(** ** Instance/Top/Prop.v: the union axiom, measured both ways *)

(* The alternative design (a): unions over an index TYPE at the points'
   universe, Test/ProbeStoneCech455.v's [p455_TopP] completed. *)
Record p457_PTopIdx@{o} := {
  p457_pi_carrier :> SetoidObject@{o o};
  p457_PIOpen : (p457_pi_carrier → Prop) → Prop;
  p457_piopen_respects (U V : p457_pi_carrier → Prop) :
    (∀ x, U x <-> V x) → p457_PIOpen U → p457_PIOpen V;
  p457_piopen_proper (U : p457_pi_carrier → Prop) :
    p457_PIOpen U → ∀ x y : p457_pi_carrier, x ≈ y → U x → U y;
  p457_piopen_union (I : Type@{o}) (U : I → p457_pi_carrier → Prop) :
    (∀ i, p457_PIOpen (U i)) → p457_PIOpen (fun x => ex (fun i => U i x));
  p457_piopen_whole : p457_PIOpen (fun _ => True);
  p457_piopen_inter (U V : p457_pi_carrier → Prop) :
    p457_PIOpen U → p457_PIOpen V → p457_PIOpen (fun x => U x /\ V x)
}.

(* The index of the subspace's union witness under (a): (index, open)
   pairs whose open witnesses the member. *)
Definition p457_idx_witness_index@{o +} (X : p457_PTopIdx@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X) (I : Type@{o})
  (V : I → S → Prop) :=
  { p : (I * (X → Prop))%type &
    (p457_PIOpen X (snd p) /\ ∀ s, V (fst p) s <-> snd p (h s)) }.

(* CONTROL: above [Set] it is a union index. *)
Definition p457_idx_union_above@{o | Set < o +} (X : p457_PTopIdx@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X)
  (I : Type@{o}) (V : I → S → Prop) :=
  p457_piopen_union X (p457_idx_witness_index X S h I V).

(* N8 *)
Fail Definition p457_idx_union_at_set (X : p457_PTopIdx@{Set})
  (S : SetoidObject@{Set Set}) (h : SetoidMorphism@{Set Set Set} S X)
  (I : Set) (V : I → S → Prop) :=
  p457_piopen_union X (p457_idx_witness_index X S h I V).

(* CONTROL: design (a) gives (b) above [Set] ... *)
Lemma p457_idx_to_family@{o | Set < o +} (X : p457_PTopIdx@{o})
  (F : (X → Prop) → Prop) :
  (∀ U, F U → p457_PIOpen X U) →
  p457_PIOpen X (fun x => ex (fun U => F U /\ U x)).
Proof.
  intro HF.
  apply (p457_piopen_respects X
           (fun x => ex (fun i : { U : X → Prop | F U } => proj1_sig i x))).
  - intro x; split.
    + intros [[U FU] u]; exists U; split; assumption.
    + intros [U [FU u]]; exists (exist _ U FU); exact u.
  - apply p457_piopen_union. intros [U FU]; exact (HF U FU).
Qed.

(* ... and the direct derivation at [Set] is refused. *)
(* N9 *)
Fail Definition p457_idx_to_family_at_set (X : p457_PTopIdx@{Set})
  (F : (X → Prop) → Prop) :=
  p457_piopen_union X { U : X → Prop | F U }.

(* CONTROL: under the chosen design (b) the subspace is formed at [Set],
   and (a) follows at every index universe. *)
Definition p457_psub_at_set (X : PTop@{Set}) (S : SetoidObject@{Set Set})
  (h : SetoidMorphism@{Set Set Set} S X) : PTop@{Set} := PSub X S h.

Definition p457_union_indexed@{o i} (X : PTop@{o}) (I : Type@{i})
  (U : I → pt_carrier X → Prop) :
  (∀ k, POpen X (U k)) → POpen X (fun x => ex (fun k => U k x)) :=
  popen_union_indexed X I U.

(** ** Instance/Top/Prop.v: the concrete spaces *)

(* CONTROL: the discrete space's points and opens read back at [eq_refl]
   under the CLOSED binder [@{o}], its five axioms are formed, and every
   setoid map out of it is continuous. *)
Example p457_pdiscrete_carrier@{o} (S : SetoidObject@{o o}) :
  pt_carrier (PDiscrete S) = S := eq_refl.

Example p457_pdiscrete_open@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  POpen (PDiscrete S) U = pdisc_open S U := eq_refl.

Example p457_pdisc_open_body@{o} (S : SetoidObject@{o o}) (U : S → Prop) :
  pdisc_open S U = (∀ x y : S, x ≈ y → U x → U y) := eq_refl.

Definition p457_pdisc_axioms@{o} (S : SetoidObject@{o o}) :=
  conj (pdisc_open_respects S)
    (conj (pdisc_open_proper S)
       (conj (pdisc_open_union S)
          (conj (pdisc_open_whole S) (pdisc_open_inter S)))).

Definition p457_pdisc_cont@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : @PCont (PDiscrete S) Y f :=
  pdisc_cont S Y f.

Example p457_pdisc_mor_map@{o} (S : SetoidObject@{o o}) (Y : PTop@{o})
  (f : SetoidMorphism@{o o o} S Y) : pmap (pdisc_mor S Y f) = f := eq_refl.

Example p457_pconst_at@{o} (S : SetoidObject@{o o}) (Y : PTop@{o}) (y : Y)
  (s : S) : pconst S Y y s = y := eq_refl.

(* CONTROL: the point and the two points, on Instance/Sets.v's setoids,
   and the two points of [PBool] are distinct. *)
Example p457_ppoint@{o} :
  pt_carrier PPoint@{o} = unit_setoid_object@{o o} := eq_refl.

Example p457_pbool@{o} :
  pt_carrier PBool@{o} = bool_setoid_object@{o o} := eq_refl.

Definition p457_pbool_points_distinct@{o} :
  @equiv _ PBool@{o} false true → False := PBool_points_distinct.

(** ** Instance/Top/Subspace.v: the constructions *)

(* CONTROL: the book's opens verbatim, the universal properties over
   ARBITRARY spaces, and Exercise 7.32's definition, restated. *)
Example p457_psub_open@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (h : SetoidMorphism@{o o o} S X) (V : S → Prop) :
  POpen (PSub X S h) V
  = ex (fun U : X → Prop => POpen X U /\ ∀ s, V s <-> U (h s)) := eq_refl.

Definition p457_psub_universal@{o +} (X : PTop@{o}) (S : SetoidObject@{o o})
  (h : SetoidMorphism@{o o o} S X) (Z : PTop@{o})
  (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z (PSub X S h) g <-> @PCont Z X (setoid_morphism_compose h g) :=
  psub_universal X S h Z g.

Definition p457_pquot_universal@{o +} (X : PTop@{o}) (T : SetoidObject@{o o})
  (q : SetoidMorphism@{o o o} X T) (Z : PTop@{o})
  (k : SetoidMorphism@{o o o} T Z) :
  @PCont (PQuot X T q) Z k <-> @PCont X Z (setoid_morphism_compose k q) :=
  pquot_universal X T q Z k.

Example p457_ex732_def@{o +} (X : PTop@{o}) (P : X → Prop)
  (A : ex732_Y X P → Prop) :
  POpen (ex732_Sub X P) A
  = ex (fun B : X → Prop =>
          POpen X B /\ ∀ y : ex732_Y X P, A y <-> B (proj1_sig y)) :=
  eq_refl.

Definition p457_ex732_part3@{o +} (X : PTop@{o}) (P : X → Prop) :
  @PCont (ex732_Sub X P) X (ex732_incl X P) :=
  ex732_part3 X P.

(** ** Instance/Top/Subspace.v: the object equations *)

(* CONTROL: at an explicit pair the object equation holds at [eq_refl],
   and at a variable its first component does. *)
Example p457_psub_obj_pair@{o so +| o < so +} (X : PTop@{o})
  (S : SetoidObject@{o o}) (h : S ~{Sets@{o so}}~> PForget@{o so} X) :
  Sliced PForget@{o so} X (PSub_Functor X (S; h)) = (S; h) := eq_refl.

Example p457_psub_obj_carrier@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  `1 (Sliced PForget@{o so} X (PSub_Functor X c)) = `1 c := eq_refl.

(* CONTROL: at a variable it holds by [psub_obj], Leibniz. *)
Definition p457_psub_obj@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  Sliced PForget@{o so} X (PSub_Functor X c) = c := psub_obj X c.

(* N10 *)
Fail Example p457_psub_obj_refl@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  Sliced PForget@{o so} X (PSub_Functor X c) = c := eq_refl.

Example p457_pquot_obj_pair@{o so +| o < so +} (X : PTop@{o})
  (T : SetoidObject@{o o}) (q : PForget@{o so} X ~{Sets@{o so}}~> T) :
  Cosliced PForget@{o so} X (PQuot_Functor X (T; q)) = (T; q) := eq_refl.

Definition p457_pquot_obj@{o so +| o < so +} (X : PTop@{o})
  (c : @Coslice Sets@{o so} (PForget@{o so} X)) :
  Cosliced PForget@{o so} X (PQuot_Functor X c) = c := pquot_obj X c.

(* N11 *)
Fail Example p457_pquot_obj_refl@{o so +| o < so +} (X : PTop@{o})
  (c : @Coslice Sets@{o so} (PForget@{o so} X)) :
  Cosliced PForget@{o so} X (PQuot_Functor X c) = c := eq_refl.

(* The object equation closed [Qed] instead of [Defined]. *)
Lemma p457_psub_obj_opaque@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  Sliced PForget@{o so} X (PSub_Functor X c) = c.
Proof. destruct c; reflexivity. Qed.

(* CONTROL: the counit is [id_cast] of [psub_obj], by the tactic
   [psub_counit] is proved with. *)
Definition p457_psub_counit@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  @counit _ _ _ _ (psub_adjunction X) c ≈ id_cast (psub_obj X c) :=
  ltac:(destruct c; intro t; simpl; reflexivity).

(* N12 *)
Fail Definition p457_psub_counit_opaque@{o so +| o < so +} (X : PTop@{o})
  (c : @Slice Sets@{o so} (PForget@{o so} X)) :
  @counit _ _ _ _ (psub_adjunction X) c ≈ id_cast (p457_psub_obj_opaque X c) :=
  ltac:(destruct c; intro t; simpl; reflexivity).

(** ** Instance/Top/Subspace.v: the packaging and the witnesses *)

(* CONTROL: the subspace and quotient constructions in the two records, at
   the types #457's plan states, with their adjoints and the subspace's
   object equation read back. *)
Definition p457_subspace_RARI@{o so +| o < so +} :
  ∀ X : PTop@{o}, RightAdjointRightInverse (Sliced PForget@{o so} X) :=
  subspace_RARI.

Definition p457_quotient_LARI@{o so +| o < so +} :
  ∀ X : PTop@{o}, LeftAdjointRightInverse (Cosliced PForget@{o so} X) :=
  quotient_LARI.

Example p457_subspace_RARI_right@{o so +| o < so +} (X : PTop@{o}) :
  @rari_right _ _ (Sliced PForget@{o so} X) (subspace_RARI X)
    = PSub_Functor X := eq_refl.

Example p457_subspace_RARI_obj@{o so +| o < so +} (X : PTop@{o}) :
  @rari_obj _ _ (Sliced PForget@{o so} X) (subspace_RARI X) = psub_obj X :=
  eq_refl.

Example p457_quotient_LARI_left@{o so +| o < so +} (X : PTop@{o}) :
  @lari_left _ _ (Cosliced PForget@{o so} X) (quotient_LARI X)
    = PQuot_Functor X := eq_refl.

(* CONTROL: Proposition 1 and its dual at [PForget], at the plan's
   types. *)
Definition p457_ptop_equalizers@{o so +| o < so +} :
  @HasEqualizers PTopCat@{o so} := PTop_HasEqualizers.

Definition p457_ptop_coequalizers@{o so +| o < so +} :
  @HasCoequalizers PTopCat@{o so} := PTop_HasCoequalizers.

(* CONTROL: the four readbacks, restated at [eq_refl]: the equalizer is
   the subspace on the equalizer in [Sets] and its arrow the inclusion,
   the coequalizer the quotient topology on the coequalizer in [Sets] and
   its arrow the projection; and the equalizer object is the value of
   [rari_right (subspace_RARI x)] at the downstairs equalizer, as
   Proposition 1 builds it. *)
Example p457_ptop_equalizer_obj@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@equalizer _ PTop_HasEqualizers x y f g)
    = PSub x
        (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                             Sets_Terminal Sets_HasPullbacks)
               _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ (fmap[PForget] f) (fmap[PForget] g)))) := eq_refl.

Example p457_ptop_equalizer_arrow@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@equalizer _ PTop_HasEqualizers x y f g))
    = psub_incl x
        (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                             Sets_Terminal Sets_HasPullbacks)
               _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ (fmap[PForget] f) (fmap[PForget] g)))) := eq_refl.

Example p457_ptop_equalizer_rari@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@equalizer _ PTop_HasEqualizers x y f g)
    = `1 (rari_right (subspace_RARI x)
            (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ (fmap[PForget] f) (fmap[PForget] g));
             `1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal
                                     Sets Sets_Terminal Sets_HasPullbacks)
                       _ _ (fmap[PForget] f) (fmap[PForget] g))))) :=
  eq_refl.

Example p457_ptop_coequalizer_obj@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@coeq _ PTop_HasCoequalizers x y f g)
    = PQuot y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

Example p457_ptop_coequalizer_arrow@{o so +| o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@coeq _ PTop_HasCoequalizers x y f g))
    = pquot_proj y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

(** ** Instance/Top/Subspace.v: the witnesses at concrete spaces *)

(* CONTROL: the two constructions at the concrete two-point space, with
   their adjoints read back at [eq_refl]. *)
Definition p457_pbool_subspace_RARI@{o so +| o < so +} :
  RightAdjointRightInverse (Sliced PForget@{o so} PBool@{o}) :=
  PBool_subspace_RARI.

Definition p457_pbool_quotient_LARI@{o so +| o < so +} :
  LeftAdjointRightInverse (Cosliced PForget@{o so} PBool@{o}) :=
  PBool_quotient_LARI.

Example p457_pbool_subspace_RARI_right@{o so +| o < so +} :
  @rari_right _ _ (Sliced PForget@{o so} PBool@{o}) PBool_subspace_RARI
    = PSub_Functor PBool := eq_refl.

Example p457_pbool_quotient_LARI_left@{o so +| o < so +} :
  @lari_left _ _ (Cosliced PForget@{o so} PBool@{o}) PBool_quotient_LARI
    = PQuot_Functor PBool := eq_refl.

(* CONTROL: the two pairs are pairs of DIFFERENT maps. *)
Example p457_pbool_true_map@{o} :
  pmap pbool_true@{o} = pconst bool_setoid_object PBool true := eq_refl.

Definition p457_pbool_maps_differ@{o so | o < so +} :
  pid PBool ≈[PTopCat@{o so}] pbool_true → False := pbool_maps_differ.

Example p457_ppoint_maps@{o} :
  pmap ppoint_false@{o} = pconst unit_setoid_object PBool false
  /\ pmap ppoint_true@{o} = pconst unit_setoid_object PBool true :=
  conj eq_refl eq_refl.

Definition p457_ppoint_maps_differ@{o so | o < so +} :
  ppoint_false ≈[PTopCat@{o so}] ppoint_true → False := ppoint_maps_differ.

(* CONTROL: the equalizer of the identity and the constant [true] is the
   subspace on the [Sets] equalizer of the underlying maps, the value of
   the subspace construction at [PBool] there, and exactly [true] lies in
   it. *)
Example p457_pbool_equalizer_obj@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = PSub PBool
        (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                             Sets_Terminal Sets_HasPullbacks)
               _ _ setoid_morphism_id (pconst bool_setoid_object PBool true)))
        (`1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true)))) := eq_refl.

Example p457_pbool_equalizer_rari@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = `1 (rari_right PBool_subspace_RARI@{o so _ _}
            (`1 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal Sets
                                 Sets_Terminal Sets_HasPullbacks)
                   _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true));
             `1 (`2 (@equalizer _ (@HasEqualizers_of_HasPullbacks_Terminal
                                     Sets Sets_Terminal Sets_HasPullbacks)
                       _ _ setoid_morphism_id
                       (pconst bool_setoid_object PBool true))))) :=
  eq_refl.

Definition p457_pbool_equalizer_points@{o so +| o < so +} (b : bool) :
  ex (fun e : pt_carrier (`1 PBool_equalizer@{o so _ _ _ _ _}) =>
        pmap (`1 (`2 PBool_equalizer@{o so _ _ _ _ _})) e = b)
  <-> b = true :=
  PBool_equalizer_points b.

(* CONTROL: the coequalizer of the two points is the quotient topology on
   the [Sets] coequalizer of the underlying maps, the value of the
   quotient construction at [PBool] there, and every point is identified
   with [true] in it. *)
Example p457_pbool_coequalizer_obj@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = PQuot PBool
        (SetsCoeq (pconst unit_setoid_object PBool false)
                  (pconst unit_setoid_object PBool true))
        (sets_coeq_proj (pconst unit_setoid_object PBool false)
                        (pconst unit_setoid_object PBool true)) := eq_refl.

Example p457_pbool_coequalizer_lari@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = `1 (lari_left PBool_quotient_LARI@{o so _ _}
            (SetsCoeq (pconst unit_setoid_object PBool false)
                      (pconst unit_setoid_object PBool true);
             sets_coeq_proj (pconst unit_setoid_object PBool false)
                            (pconst unit_setoid_object PBool true)))
  := eq_refl.

Definition p457_pbool_coequalizer_points@{o so +| o < so +} (b : bool) :
  @equiv _ (`1 PBool_coequalizer@{o so _ _ _ _ _ _}) b true :=
  PBool_coequalizer_points b.

(** ** Instance/Top/Subspace/TypeValued.v: the subspace predicate *)

(* CONTROL: the book's predicate is formed one universe up, as
   [tsub_open], and its body is accepted there. *)
Definition p457_tsub_open@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o1} :=
  tsub_open X S h V.

Definition p457_tsub_open_body@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o1} :=
  { U : top_carrier X → Type@{o} &
    (IsOpen X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

(* N13 *)
Fail Definition p457_tsub_open_at_o@{o +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o} :=
  { U : top_carrier X → Type@{o} &
    (IsOpen X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

(* CONTROL: the quotient is a space at the points' universe. *)
Definition p457_tquot@{o +} (X : TopSpace@{o}) (T : SetoidObject@{o o})
  (q : SetoidMorphism@{o o o} (top_carrier X) T) : TopSpace@{o} :=
  TQuot X T q.

(* CONTROL: the five axioms of the unpackaged subspace, and the same
   record literal at the quotient's opens, packaged at [o]. *)
Definition p457_tsub_axioms@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X)) :=
  (tsub_open_respects@{o o1} X S h, tsub_open_proper@{o o1} X S h,
   tsub_open_union@{o o1} X S h, tsub_open_whole@{o o1} X S h,
   tsub_open_inter@{o o1} X S h).

Definition p457_tquot_package@{o +} (X : TopSpace@{o})
  (T : SetoidObject@{o o}) (q : SetoidMorphism@{o o o} (top_carrier X) T) :
  TopSpace@{o} := {|
  top_carrier   := T;
  IsOpen        := tquot_open X T q;
  open_respects := tquot_open_respects X T q;
  open_proper   := tquot_open_proper X T q;
  open_union    := tquot_open_union X T q;
  open_whole    := tquot_open_whole X T q;
  open_inter    := tquot_open_inter X T q |}.

(* N14 *)
Fail Definition p457_tsub_package@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X)) :
  TopSpace@{o} := {|
  top_carrier   := S;
  IsOpen        := tsub_open@{o o1} X S h;
  open_respects := tsub_open_respects X S h;
  open_proper   := tsub_open_proper X S h;
  open_union    := tsub_open_union X S h;
  open_whole    := tsub_open_whole X S h;
  open_inter    := tsub_open_inter X S h |}.

(* CONTROL: the universal properties over ARBITRARY spaces, restated. *)
Definition p457_tsub_universal@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S) :
  tsub_continuous@{o o1} X S h Z g
    ↔ Continuous Z X (setoid_morphism_compose h g) :=
  tsub_universal X S h Z g.

Definition p457_tquot_universal@{o +} (X : TopSpace@{o})
  (T : SetoidObject@{o o}) (q : SetoidMorphism@{o o o} (top_carrier X) T)
  (Z : TopSpace@{o}) (k : SetoidMorphism@{o o o} T (top_carrier Z)) :
  Continuous (TQuot X T q) Z k
    ↔ Continuous X Z (setoid_morphism_compose k q) :=
  tquot_universal X T q Z k.

(** ** Instance/Top/Subspace/TypeValued.v: the slices of the two [Sets] *)

(* CONTROL: an object of the slice of the UNLIFTED [Sets] carries the
   discrete topology at the points' universe; one of the LIFTED [Sets]
   carries it one universe up. *)
Definition p457_unlifted_slice_space@{o so +| o < so +} (X : TopSpace@{o})
  (x : @Slice Sets@{o so} (top_carrier X)) : TopSpace@{o} :=
  Discrete_Top (`1 x).

Definition p457_lifted_slice_space_h@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) (x : @Slice Sets@{h so} (Top_Forget@{o h so} X)) :
  TopSpace@{h} :=
  Discrete_Top (`1 x).

(* N15 *)
Fail Definition p457_lifted_slice_space@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) (x : @Slice Sets@{h so} (Top_Forget@{o h so} X)) :
  TopSpace@{o} :=
  Discrete_Top (`1 x).

(* CONTROL: the same for the coslices. *)
Definition p457_unlifted_coslice_space@{o so +| o < so +} (X : TopSpace@{o})
  (x : @Coslice Sets@{o so} (top_carrier X)) : TopSpace@{o} :=
  Discrete_Top (`1 x).

Definition p457_lifted_coslice_space_h@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) (x : @Coslice Sets@{h so} (Top_Forget@{o h so} X)) :
  TopSpace@{h} :=
  Discrete_Top (`1 x).

(* N16 *)
Fail Definition p457_lifted_coslice_space@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) (x : @Coslice Sets@{h so} (Top_Forget@{o h so} X)) :
  TopSpace@{o} :=
  Discrete_Top (`1 x).

(* CONTROL: [Top_Forget] into the LIFTED [Sets], restated; the type of a
   functor into the [Sets] whose objects are the point setoids is not
   formed. *)
Definition p457_top_forget@{o h so +| o < h, h < so +} :
  Top@{h o} ⟶ Sets@{h so} :=
  Top_Forget@{o h so}.

(* N17 *)
Fail Definition p457_top_to_point_sets@{o h +| o < h +} :=
  (Top@{h o} ⟶ Sets@{o h}).

(* CONTROL: the type of a functor into the lifted [Sets@{h so}] is
   formed; into Instance/Top/Forgetful.v's own [Sets@{o so}], the
   universe [so] of its objects fresh, it is not. *)
Definition p457_top_to_lifted_sets@{o h so +| o < h +} :=
  (Top@{h o} ⟶ Sets@{h so}).

(* N26 *)
Fail Definition p457_top_to_point_sets_so@{o h so +| o < h +} :=
  (Top@{h o} ⟶ Sets@{o so}).

(* CONTROL: the sliced forgetful functor at [Top_Forget] and the quotient
   functor are each formed, and the transposition between them is the
   identity on underlying maps; the adjunction is not formed. *)
Definition p457_top_forget_under@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) :
  @Coslice Top@{h o} X ⟶ @Coslice Sets@{h so} (Top_Forget@{o h so} X) :=
  Top_Forget_under X.

Definition p457_tquot_functor@{o h so +| o < h, o < so +} (X : TopSpace@{o}) :
  @Coslice Sets@{o so} (top_carrier X) ⟶ @Coslice Top@{h o} X :=
  TQuot_Functor X.

Example p457_tquot_adj_to_map@{o h so +| o < h, o < so +} (X : TopSpace@{o})
  (x : @Coslice Sets@{o so} (top_carrier X)) (y : @Coslice Top@{h o} X)
  (k : TQuot_Functor X x ~{@Coslice Top@{h o} X}~> y) :
  `1 (to (tquot_adj X x y) k) = continuous_map (`1 k) := eq_refl.

(* CONTROL: [Top_Forget_under X y] IS the lift of [tstrip_under X y]. *)
Example p457_forget_under_lift@{o h so +| o < h, h < so +} (X : TopSpace@{o})
  (y : @Coslice Top@{h o} X) :
  Top_Forget_under@{o h so} X y
    = (Setoid_Lift (`1 (tstrip_under X y));
       SetoidMorphism_Lift (`2 (tstrip_under X y))) := eq_refl.

(* N18 *)
Fail Definition p457_tquot_adjunction@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) :=
  (TQuot_Functor@{o h so _} X ⊣ Top_Forget_under@{o h so} X).

(* The stripped object equation: Leibniz, [eq_refl] only at a pair. *)
Example p457_tquot_obj_stripped_pair@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (T : SetoidObject@{o o})
  (q : top_carrier X ~{Sets@{o so}}~> T) :
  tstrip_under@{o h so _ _} X (TQuot_Functor X (T; q)) = (T; q) := eq_refl.

Definition p457_tquot_obj_stripped@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  tstrip_under@{o h so _ _} X (TQuot_Functor X c) = c :=
  tquot_obj_stripped X c.

(* N19 *)
Fail Example p457_tquot_obj_stripped_refl@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  tstrip_under@{o h so _ _} X (TQuot_Functor X c) = c := eq_refl.

(* The stripped object equation closed [Qed] instead of [Defined]. *)
Lemma p457_tquot_obj_stripped_opaque@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  tstrip_under@{o h so _ _} X (TQuot_Functor X c) = c.
Proof. destruct c; reflexivity. Qed.

(* CONTROL: the transposed identity is [id_cast] of the inverse of
   [tquot_obj_stripped], by the tactic [tquot_unit_stripped] is proved
   with. *)
Definition p457_tquot_unit@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  to (tquot_adj X c (TQuot_Functor X c)) id
    ≈[@Coslice Sets@{o so} (top_carrier X)]
  id_cast (eq_sym (tquot_obj_stripped X c)) :=
  ltac:(destruct c; intro t; simpl; reflexivity).

(* N25 *)
Fail Definition p457_tquot_unit_opaque@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) (c : @Coslice Sets@{o so} (top_carrier X)) :
  to (tquot_adj X c (TQuot_Functor X c)) id
    ≈[@Coslice Sets@{o so} (top_carrier X)]
  id_cast (eq_sym (p457_tquot_obj_stripped_opaque X c)) :=
  ltac:(destruct c; intro t; simpl; reflexivity).

(** ** The squashed, local subspace over [Top] *)

(* Scout A's local encoding, rebuilt: V is open when it respects [≈] and
   each point of V MERELY has an open of X around its image whose preimage
   lies in V.  Instance/Sets/Powerset.v's [Powerset_squash] is the
   truncation. *)
Definition p457_sq_box@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) (s : S) : Type@{o1} :=
  { U : top_carrier X → Type@{o} &
    (IsOpen X U ∧ U (h s) ∧ (∀ t : S, U (h t) → V t))%type }.

Definition p457_sq_open@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o} :=
  ((∀ s t : S, s ≈ t → V s → V t)
   ∧ (∀ s : S, V s → Powerset_squash@{o1} (p457_sq_box@{o o1} X S h V s)))%type.

Lemma p457_sq_map@{o1} {A B : Type@{o1}} (f : A → B) :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B.
Proof. intros a Q k; exact (a Q (fun x => k (f x))). Qed.

Lemma p457_sq_pair@{o1} {A B : Type@{o1}} :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B →
  Powerset_squash@{o1} (A * B)%type.
Proof. intros a b Q k; exact (a Q (fun x => b Q (fun y => k (x, y)))). Qed.

(* CONTROL: it IS a space at the points' universe. *)
Definition p457_sq_subspace@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X)) :
  TopSpace@{o}.
Proof.
  unshelve refine {| top_carrier := S; IsOpen := p457_sq_open@{o o1} X S h |}.
  - intros U V H [Hp Hb]; split.
    + intros s t e v. apply (fst (H t)), (Hp s t e), (snd (H s)), v.
    + intros s v. apply (p457_sq_map (A := p457_sq_box X S h U s)).
      * intros [B [HB [Bs Hin]]]. exists B.
        repeat split; try assumption.
        intros t b; exact (fst (H t) (Hin t b)).
      * exact (Hb s (snd (H s) v)).
  - intros U [Hp _]; exact Hp.
  - intros I U HU; split.
    + intros s t e [i u]; exact (i; fst (HU i) s t e u).
    + intros s [i u]. apply (p457_sq_map (A := p457_sq_box X S h (U i) s)).
      * intros [B [HB [Bs Hin]]]. exists B.
        repeat split; try assumption.
        intros t b; exact (i; Hin t b).
      * exact (snd (HU i) s u).
  - split.
    + intros; exact ttt.
    + intros s _. apply Powerset_squash_intro.
      exists (fun _ => poly_unit@{o}).
      repeat split; try exact ttt; try apply open_whole.
  - intros U V [HpU HbU] [HpV HbV]; split.
    + intros s t e [u v]; exact (HpU s t e u, HpV s t e v).
    + intros s [u v].
      apply (p457_sq_map (A := (p457_sq_box X S h U s
                                * p457_sq_box X S h V s)%type)).
      * intros [[A [HA [As HinA]]] [B [HB [Bs HinB]]]].
        exists (fun x => (A x ∧ B x)%type).
        split; [apply open_inter; assumption|].
        split; [split; assumption|].
        intros t [a b]; exact (HinA t a, HinB t b).
      * apply p457_sq_pair; [exact (HbU s u) | exact (HbV s v)].
Defined.

(* CONTROL: [h] is continuous out of it, and the "only if" half of the
   universal property holds. *)
Lemma p457_sq_h_cont@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X)) :
  Continuous (p457_sq_subspace@{o o1} X S h) X h.
Proof.
  intros U HU; split.
  - intros s t e u. exact (open_proper X U HU (h s) (h t)
                             (proper_morphism h s t e) u).
  - intros s u. apply Powerset_squash_intro.
    exists U; repeat split; try assumption.
    intros t b; exact b.
Qed.

Lemma p457_sq_only_if@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S) :
  Continuous Z (p457_sq_subspace@{o o1} X S h) g →
  Continuous Z X (setoid_morphism_compose h g).
Proof. intros Hg U HU. exact (Hg _ (p457_sq_h_cont X S h U HU)). Qed.

(* CONTROL: its opens include the book's, [tsub_open], for predicates
   respecting the points' equality. *)
Lemma p457_sq_global_to_local@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) :
  (∀ s t : S, s ≈ t → V s → V t) →
  tsub_open@{o o1} X S h V → p457_sq_open@{o o1} X S h V.
Proof.
  intros Hp [U [HU HVU]]; split; [exact Hp|].
  intros s v. apply Powerset_squash_intro.
  exists U; repeat split; [exact HU | exact (fst (HVU s) v) |].
  intros t b; exact (snd (HVU t) b).
Qed.

(* CONTROL: the squashed box eliminates into a proposition. *)
Definition p457_sq_elim_prop@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S)
  (V : S → Type@{o}) (HV : p457_sq_open@{o o1} X S h V)
  (z0 : top_carrier Z) (v : V (g z0)) :=
  (snd HV (g z0) v) True.

(* N20 *)
Fail Definition p457_sq_elim_open@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S)
  (V : S → Type@{o}) (HV : p457_sq_open@{o o1} X S h V)
  (z0 : top_carrier Z) (v : V (g z0)) :=
  (snd HV (g z0) v) (IsOpen Z (fun z => V (g z))).

(* CONTROL: a union indexed by the points of Z. *)
Definition p457_union_by_points@{o +} (Z : TopSpace@{o}) :=
  @open_union Z (top_carrier Z).

(* N21 *)
Fail Definition p457_sq_union_by_boxes@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (Z : TopSpace@{o}) (g : SetoidMorphism@{o o o} (top_carrier Z) S)
  (V : S → Type@{o}) (z0 : top_carrier Z) :=
  @open_union Z (p457_sq_box@{o o1} X S h V (g z0)).

(* N22 *)
Fail Definition p457_sq_local_to_global@{o o1 +| o < o1 +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) (HV : p457_sq_open@{o o1} X S h V) (s0 : S)
  (v : V s0) :=
  (snd HV s0 v)
    { U : top_carrier X → Type@{o} &
      (IsOpen X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

(** ** Two further encodings of the subspace over Type-valued opens *)

(* Instance/Top/Kolmogorov.v's small-opens idea: quantifying over opens
   valued at [s < o] puts the predicate at [o] ... *)
Definition p457_small_sub_open@{s o +| s < o +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) : Type@{o} :=
  { U : top_carrier X → Type@{s} &
    (IsOpen X U ∧ (∀ s0 : S, V s0 ↔ U (h s0)))%type }.

(* CONTROL: ... and, given an open of that encoding (whose type forces
   [s < o]), the union of [s]-valued witnesses over an index at [s] is
   [s]-valued ... *)
Definition p457_small_union_at_s@{s o +| s < o +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) (HV : p457_small_sub_open@{s o} X S h V)
  (I : Type@{s}) (U : I → top_carrier X → Type@{s}) :
  top_carrier X → Type@{s} :=
  fun x => { i : I & U i x }.

(* ... but over an index at [o], the index [open_union] takes, it is not. *)
(* N23 *)
Fail Definition p457_small_union_at_o@{s o +| s < o +} (X : TopSpace@{o})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S (top_carrier X))
  (V : S → Type@{o}) (HV : p457_small_sub_open@{s o} X S h V)
  (I : Type@{o}) (U : I → top_carrier X → Type@{s}) :
  top_carrier X → Type@{s} :=
  fun x => { i : I & U i x }.

(* A two-level record, its opens valued one universe above the points. *)
Record p457_Top2@{o o1} := {
  p457_t2_carrier :> SetoidObject@{o o};
  p457_IsOpen2 : (p457_t2_carrier → Type@{o}) → Type@{o1};
  p457_open2_respects (U V : p457_t2_carrier → Type@{o}) :
    (∀ x, U x ↔ V x) → p457_IsOpen2 U → p457_IsOpen2 V;
  p457_open2_proper (U : p457_t2_carrier → Type@{o}) :
    p457_IsOpen2 U → ∀ x y : p457_t2_carrier, x ≈ y → U x → U y;
  p457_open2_union (I : Type@{o}) (U : I → (p457_t2_carrier → Type@{o})) :
    (∀ i, p457_IsOpen2 (U i)) → p457_IsOpen2 (fun x => { i : I & U i x });
  p457_open2_whole : p457_IsOpen2 (fun _ => poly_unit@{o});
  p457_open2_inter (U V : p457_t2_carrier → Type@{o}) :
    p457_IsOpen2 U → p457_IsOpen2 V → p457_IsOpen2 (fun x => U x ∧ V x)
}.

(* CONTROL: it hosts the book's subspace predicate ... *)
Definition p457_sub2_open@{o o1 +| o < o1 +} (X : p457_Top2@{o o1})
  (S : SetoidObject@{o o}) (h : SetoidMorphism@{o o o} S X)
  (V : S → Type@{o}) : Type@{o1} :=
  { U : X → Type@{o} &
    (p457_IsOpen2 X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

(* ... and its continuity is a type one universe up ... *)
Definition p457_cont2@{o o1 +| o < o1 +} (X Y : p457_Top2@{o o1})
  (f : SetoidMorphism@{o o o} X Y) : Type@{o1} :=
  ∀ U : Y → Type@{o}, p457_IsOpen2 Y U → p457_IsOpen2 X (fun x => U (f x)).

(* ... not at the points' universe. *)
(* N24 *)
Fail Definition p457_cont2_at_o@{o o1 +| o < o1 +} (X Y : p457_Top2@{o o1})
  (f : SetoidMorphism@{o o o} X Y) : Type@{o} :=
  ∀ U : Y → Type@{o}, p457_IsOpen2 Y U → p457_IsOpen2 X (fun x => U (f x)).

(** ** Guard block *)

(* Structure/SlicedInverse.v: 73 names, 19 obligations *)
Check @Sliced.
Check @Cosliced.
Check @Sliced_fobj.
Check @Sliced_fmap.
Check @Cosliced_fobj.
Check @Cosliced_fmap.
Check @rari_right.
Check @rari_adj.
Check @rari_obj.
Check @rari_counit.
Check @adj_unit_universal_op.
Check @adj_unit_universal_op_obj.
Check @adj_unit_universal_op_arrow.
Check @sliced_eq_obj.
Check @sliced_eq_arrow.
Check @sliced_fork.
Check @sliced_desc.
Check @sliced_equalizer.
Check @cosliced_coeq_obj.
Check @cosliced_coeq_arrow.
Check @cosliced_cofork.
Check @cosliced_desc.
Check @cosliced_coequalizer.
Check @equalizers_from_sliced_right_adjoints.
Check @equalizers_from_sliced_RARI.
Check @equalizers_from_sliced_RARI_obj.
Check @equalizers_from_sliced_RARI_arrow.
Check @coequalizers_from_sliced_left_adjoints.
Check @coequalizers_from_sliced_left_adjoints_obj.
Check @coequalizers_from_sliced_left_adjoints_arrow.
Check @slice_id_cast_1.
Check @IsEqualizer_transport.
Check @rari_couniversal.
Check @rari_eq_obj.
Check @rari_eq_arrow.
Check @rari_over.
Check @rari_arrow_over.
Check @rari_preserves.
Check @equalizers_from_sliced_RARI_preserved.
Check @par_arrow_one.
Check @par_arrow_two.
Check @parallel_pair_unforked.
Check @Parallel_no_equalizers.
Check @Erase_Parallel_not_faithful.
Check @One_HasEqualizers.
Check @slice_one_hom_eq.
Check @erase_slice_right.
Check @erase_slice_hom_iso.
Check @erase_slice_adj.
Check @erase_slice_RARI.
Check @sliced_RARI_without_faithfulness.
Check @prop1_needs_faithfulness.
Check @RightAdjointRightInverse.
Check @Build_RightAdjointRightInverse.
Check @SlicedInverse.Sliced_obligation_1.
Check @SlicedInverse.Sliced_obligation_2.
Check @SlicedInverse.Sliced_obligation_3.
Check @SlicedInverse.Sliced_obligation_4.
Check @SlicedInverse.Cosliced_obligation_1.
Check @SlicedInverse.Cosliced_obligation_2.
Check @SlicedInverse.Cosliced_obligation_3.
Check @SlicedInverse.Cosliced_obligation_4.
Check @SlicedInverse.One_HasEqualizers_obligation_1.
Check @SlicedInverse.One_HasEqualizers_obligation_2.
Check @SlicedInverse.erase_slice_right_obligation_1.
Check @SlicedInverse.erase_slice_right_obligation_2.
Check @SlicedInverse.erase_slice_right_obligation_3.
Check @SlicedInverse.erase_slice_hom_iso_obligation_1.
Check @SlicedInverse.erase_slice_hom_iso_obligation_2.
Check @SlicedInverse.erase_slice_hom_iso_obligation_3.
Check @SlicedInverse.erase_slice_hom_iso_obligation_4.
Check @SlicedInverse.erase_slice_hom_iso_obligation_5.
Check @SlicedInverse.erase_slice_hom_iso_obligation_6.

(* Structure/SlicedInverse/Strict.v: 39 names, 11 obligations *)
Check @rari_lali.
Check @lali_rari.
Check @rari_lali_left.
Check @lali_rari_right.
Check @rari_lali_rari.
Check @lali_rari_lali.
Check @coequalizers_from_sliced_LARI.
Check @coequalizers_from_sliced_LARI_obj.
Check @coequalizers_from_sliced_LARI_arrow.
Check @coslice_id_cast_1.
Check @IsCoequalizer_transport.
Check @lari_universal.
Check @lari_coeq_obj.
Check @lari_coeq_arrow.
Check @lari_under.
Check @lari_arrow_under.
Check @lari_preserves.
Check @coequalizers_from_sliced_LARI_preserved.
Check @parallel_pair_uncoforked.
Check @Parallel_no_coequalizers.
Check @One_HasCoequalizers.
Check @coslice_one_hom_eq.
Check @erase_coslice_left.
Check @erase_coslice_hom_iso.
Check @erase_coslice_adj.
Check @erase_coslice_LARI.
Check @cosliced_LARI_without_faithfulness.
Check @prop1_dual_needs_faithfulness.
Check @Strict.One_HasCoequalizers_obligation_1.
Check @Strict.One_HasCoequalizers_obligation_2.
Check @Strict.erase_coslice_left_obligation_1.
Check @Strict.erase_coslice_left_obligation_2.
Check @Strict.erase_coslice_left_obligation_3.
Check @Strict.erase_coslice_hom_iso_obligation_1.
Check @Strict.erase_coslice_hom_iso_obligation_2.
Check @Strict.erase_coslice_hom_iso_obligation_3.
Check @Strict.erase_coslice_hom_iso_obligation_4.
Check @Strict.erase_coslice_hom_iso_obligation_5.
Check @Strict.erase_coslice_hom_iso_obligation_6.

(* Instance/Top/Prop.v: 51 names, 8 obligations *)
Check @pt_carrier.
Check @POpen.
Check @popen_respects.
Check @popen_proper.
Check @popen_union.
Check @popen_whole.
Check @popen_inter.
Check @popen_union_indexed.
Check @popen_const.
Check @popen_empty.
Check @PCont.
Check @pcont_respects.
Check @pmap.
Check @pcont.
Check @PMor_Setoid.
Check @pid.
Check @pcompose.
Check @pcompose_respects.
Check @PTopCat.
Check @PForget.
Check @PForget_fobj.
Check @PForget_fmap.
Check @PForget_Faithful.
Check @PTop.
Check @Build_PTop.
Check @PMor.
Check @Build_PMor.
Check @pdisc_open.
Check @pdisc_open_respects.
Check @pdisc_open_proper.
Check @pdisc_open_union.
Check @pdisc_open_whole.
Check @pdisc_open_inter.
Check @PDiscrete.
Check @PDiscrete_carrier.
Check @PDiscrete_open.
Check @pdisc_cont.
Check @pdisc_mor.
Check @pdisc_mor_map.
Check @pconst.
Check @PPoint.
Check @PBool.
Check @PBool_points_distinct.
Check @Top.Prop.PMor_Setoid_obligation_1.
Check @Top.Prop.PTopCat_obligation_1.
Check @Top.Prop.PTopCat_obligation_2.
Check @Top.Prop.PTopCat_obligation_3.
Check @Top.Prop.PTopCat_obligation_4.
Check @Top.Prop.PForget_obligation_1.
Check @Top.Prop.PForget_obligation_2.
Check @Top.Prop.PForget_obligation_3.

(* Instance/Top/Subspace.v: 111 names, 26 obligations *)
Check @psub_open.
Check @psub_open_respects.
Check @psub_open_proper.
Check @psub_open_union.
Check @psub_open_whole.
Check @psub_open_inter.
Check @PSub.
Check @PSub_carrier.
Check @PSub_open.
Check @psub_incl_cont.
Check @psub_incl.
Check @psub_universal.
Check @psub_lift.
Check @psub_lift_map.
Check @psub_lift_comm.
Check @ex732_Y.
Check @ex732_incl.
Check @ex732_Sub.
Check @ex732_def.
Check @ex732_part1.
Check @ex732_part2.
Check @ex732_part3.
Check @ex732_incl_mor.
Check @pquot_open.
Check @pquot_open_respects.
Check @pquot_open_proper.
Check @pquot_open_union.
Check @pquot_open_whole.
Check @pquot_open_inter.
Check @PQuot.
Check @PQuot_carrier.
Check @PQuot_open.
Check @pquot_proj_cont.
Check @pquot_proj.
Check @pquot_universal.
Check @pquot_desc.
Check @pquot_desc_map.
Check @pquot_desc_comm.
Check @PForget_over.
Check @PForget_under.
Check @PForget_over_Sliced.
Check @PForget_under_Cosliced.
Check @PSub_Functor.
Check @PSub_Functor_obj.
Check @psub_adj_iso.
Check @psub_adj_to_map.
Check @psub_adj_from_map.
Check @psub_adjunction.
Check @psub_obj.
Check @psub_obj_pair.
Check @psub_counit.
Check @PQuot_Functor.
Check @PQuot_Functor_obj.
Check @pquot_adj_iso.
Check @pquot_adj_to_map.
Check @pquot_adj_from_map.
Check @pquot_adjunction.
Check @pquot_obj.
Check @pquot_obj_pair.
Check @pquot_unit.
Check @subspace_RARI.
Check @subspace_RARI_right.
Check @quotient_LARI.
Check @quotient_LARI_left.
Check @PTop_HasEqualizers.
Check @PTop_equalizer_obj.
Check @PTop_equalizer_arrow.
Check @PTop_HasCoequalizers.
Check @PTop_coequalizer_obj.
Check @PTop_coequalizer_arrow.
Check @PBool_subspace_RARI.
Check @PBool_quotient_LARI.
Check @pbool_true.
Check @pbool_maps_differ.
Check @PBool_equalizer.
Check @PBool_equalizer_obj.
Check @PBool_equalizer_rari.
Check @PBool_equalizer_points.
Check @ppoint_false.
Check @ppoint_true.
Check @ppoint_maps_differ.
Check @PBool_coequalizer.
Check @PBool_coequalizer_obj.
Check @PBool_coequalizer_lari.
Check @PBool_coequalizer_points.
Check @Subspace.ex732_Y_obligation_1.
Check @Subspace.ex732_incl_obligation_1.
Check @Subspace.PSub_Functor_obligation_1.
Check @Subspace.PSub_Functor_obligation_2.
Check @Subspace.PSub_Functor_obligation_3.
Check @Subspace.PSub_Functor_obligation_4.
Check @Subspace.PSub_Functor_obligation_5.
Check @Subspace.psub_adj_iso_obligation_1.
Check @Subspace.psub_adj_iso_obligation_2.
Check @Subspace.psub_adj_iso_obligation_3.
Check @Subspace.psub_adj_iso_obligation_4.
Check @Subspace.psub_adj_iso_obligation_5.
Check @Subspace.psub_adj_iso_obligation_6.
Check @Subspace.psub_adj_iso_obligation_7.
Check @Subspace.PQuot_Functor_obligation_1.
Check @Subspace.PQuot_Functor_obligation_2.
Check @Subspace.PQuot_Functor_obligation_3.
Check @Subspace.PQuot_Functor_obligation_4.
Check @Subspace.PQuot_Functor_obligation_5.
Check @Subspace.pquot_adj_iso_obligation_1.
Check @Subspace.pquot_adj_iso_obligation_2.
Check @Subspace.pquot_adj_iso_obligation_3.
Check @Subspace.pquot_adj_iso_obligation_4.
Check @Subspace.pquot_adj_iso_obligation_5.
Check @Subspace.pquot_adj_iso_obligation_6.
Check @Subspace.pquot_adj_iso_obligation_7.

(* Instance/Top/Subspace/TypeValued.v: 69 names, 26 obligations *)
Check @tcont_respects.
Check @tquot_open.
Check @tquot_open_respects.
Check @tquot_open_proper.
Check @tquot_open_union.
Check @tquot_open_whole.
Check @tquot_open_inter.
Check @TQuot.
Check @TQuot_carrier.
Check @TQuot_open.
Check @tquot_proj_cont.
Check @tquot_proj.
Check @tquot_universal.
Check @tquot_desc.
Check @tquot_desc_map.
Check @tsub_open.
Check @tsub_open_respects.
Check @tsub_open_proper.
Check @tsub_open_union.
Check @tsub_open_whole.
Check @tsub_open_inter.
Check @tsub_preimage_open.
Check @tsub_continuous.
Check @tsub_universal.
Check @tsub_lift.
Check @Top_Forget_over.
Check @Top_Forget_under.
Check @TQuot_Functor.
Check @tstrip_under.
Check @tstrip_under_lift.
Check @tstrip_under_map.
Check @tquot_adj.
Check @tquot_adj_to_map.
Check @tquot_adj_from_map.
Check @tquot_adj_nat_l.
Check @tquot_adj_nat_r.
Check @tquot_obj_stripped.
Check @tquot_obj_stripped_pair.
Check @tquot_unit_stripped.
Check @tsub_hom.
Check @tsub_hom_setoid.
Check @tsub_adj.
Check @tsub_adj_to_map.
Check @TypeValued.Top_Forget_over_obligation_1.
Check @TypeValued.Top_Forget_over_obligation_2.
Check @TypeValued.Top_Forget_over_obligation_3.
Check @TypeValued.Top_Forget_over_obligation_4.
Check @TypeValued.Top_Forget_under_obligation_1.
Check @TypeValued.Top_Forget_under_obligation_2.
Check @TypeValued.Top_Forget_under_obligation_3.
Check @TypeValued.Top_Forget_under_obligation_4.
Check @TypeValued.TQuot_Functor_obligation_1.
Check @TypeValued.TQuot_Functor_obligation_2.
Check @TypeValued.TQuot_Functor_obligation_3.
Check @TypeValued.TQuot_Functor_obligation_4.
Check @TypeValued.TQuot_Functor_obligation_5.
Check @TypeValued.tquot_adj_obligation_1.
Check @TypeValued.tquot_adj_obligation_2.
Check @TypeValued.tquot_adj_obligation_3.
Check @TypeValued.tquot_adj_obligation_4.
Check @TypeValued.tquot_adj_obligation_5.
Check @TypeValued.tsub_hom_setoid_obligation_1.
Check @TypeValued.tsub_adj_obligation_1.
Check @TypeValued.tsub_adj_obligation_2.
Check @TypeValued.tsub_adj_obligation_3.
Check @TypeValued.tsub_adj_obligation_4.
Check @TypeValued.tsub_adj_obligation_5.
Check @TypeValued.tsub_adj_obligation_6.
Check @TypeValued.tsub_adj_obligation_7.
