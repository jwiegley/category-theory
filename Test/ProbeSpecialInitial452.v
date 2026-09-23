(** * Probe for the special initial-object theorem (issue #452)

    Pins the measured boundaries of Adjunction/SAFT/InitialObject.v (Mac
    Lane §V.8 Theorem 1, book p. 128; Riehl Lemma 4.7.11, printed p. 177)
    and of the three files #452 added beside it: Adjunction/SAFT/
    InitialObject/Examples.v, Instance/Sets/Cogenerator.v and Instance/
    Sets/SpecialInitial.v.  Every negative but two restates a refusal
    measured on #452 by its scouts, builders or review; N7, a peel of N6,
    and N14, the theorem beside N13's product, are this file's own.  The
    positive controls restate the files' claims independently.

    THE IMPORT LIST, measured by comparing [Require] lines.  First
    Adjunction/SAFT/InitialObject.v's twenty-one lines verbatim and in
    order; then the lines each other target adds, file by file, the target
    modules aside: Adjunction/SAFT/InitialObject/Examples.v five, Instance/
    Sets/Cogenerator.v two and Instance/Sets/SpecialInitial.v seven; then
    the four target modules in dependency order.  No supplier module is
    added.  Adjunction/SAFT.v is imported after Theory/Subobject.v, so the
    short names [sub_dom] and [sub_mono] are [SubobjectIndex]'s fields
    ([Locate] lists Adjunction/SAFT.v's first), and a subobject's are
    written [Subobject.sub_dom].  Instance/Discrete.v is loaded by the list
    but not imported ([Locate] gives the shorter name
    [Discrete.DiscreteCat_Functor]), so N5 and its control write
    [Category.Instance.Discrete.DiscreteCat_Functor] in full: it is the
    term Adjunction/SAFT.v's [cogen_power_limit] is built from.  A shorter
    import list is what makes a probe pass for no reason.

    DISCIPLINE.  The instrument was checked both ways: the refutation of an
    absent name is refused for that reason, and wrapping a control in a
    refutation, in a copy of this WHOLE file, stops the build with the
    report that the guarded command had been accepted (done five times,
    at [p452_obj], [p452_binder_ok], [p452_sets_iem_direct],
    [p452_large_cog] and [p452_large_prod_abstract]).  Every negative
    other than that instrument is a [Definition] or an [Example], never a
    [Check], so that an open evar or a missing instance cannot satisfy it.
    Each negative was stripped of its refutation keyword in a copy of this
    WHOLE file, one at a time, compiled, and its error read; the kind
    recorded is the kind of that error, and each has positive controls
    beside it that between them name the same library constants.  Every
    UNIVERSE negative is a top-level definition whose universes are
    declared in its own binder or left to inference, never those of a
    [Section], so that the stripped error names the bound where Rocq can.
    Quotations are Rocq 9.1.1's under this file's import list; Rocq prints
    the "cannot unify" parenthetical with the short names in scope, and a
    universe the stripped copy names after itself and a serial number is
    written <1>, <2>, ..., numbered afresh in each quotation in order of
    first appearance.  The file also compiles on Coq 8.19.2 and 8.20.1,
    against the nix store's builds of this library for those versions with
    the four target files compiled on each, and the stripped copies were
    compiled there as well.  Every one is refused on both at the same
    construct, and at the same character range except N13 and N14, whose
    range there also covers the family's explicit universe instance.
    Under 8.20.1 every error is the Rocq 9.1.1 one up to the serial
    numbers (compared by a script over the copies).  Under 8.19.2 nine of
    the universe refusals (N2, N3, N8, N9, N11, N13-N16) print as type
    mismatches with no universe-inconsistency clause, N4 names its two
    universes by serial numbers, and N5's chain reads "so < <5> <= <4> <=
    <1>" in place of "so < h <= <4> <= <1>", <5> being a universe the
    Rocq 9.1.1 error does not print.

    KINDS.  Nineteen refutations, counted as the lines that open with the
    refutation keyword: NAME-ABSENCE (the instrument), CONVERSION (N1,
    N17, N18) and UNIVERSE (N2-N16).

    LABELS.  Three pins also carry the names under which #452's review
    asked for them, and the target headers cite each by that label, its
    N-number and its constants: P_H_le_so is N5, P_type_truth is N11 and
    N12, P_large_cog is N13 and N14.  The labels appear in this header and
    in the section titles below; they are not constants.

    ** The theorem's object

    N1 (CONVERSION).  [special_initial_object]'s object IS
    [Subobject.sub_dom w] by [eq_refl] ([p452_obj]), and its arrow to [c]
    is the pullback leg after the lower-bound factor ([p452_zero]), both
    restated from Adjunction/SAFT/InitialObject.v's readbacks;
    [p452_is_initial] states the conclusion in the type.  The readback
    discriminates: the product itself is refused,
      The term "eq_refl" has type "0 = 0" while it is expected to have
      type "0 = cogen_prod comp G" (cannot unify "0" and "cogen_prod comp
      G").
    [0] being Structure/Initial.v's notation for [initial_obj].

    ** The two donor collapses

    N2 (UNIVERSE).  Adjunction/SAFT.v's unannotated [cogen_prod] takes the
    family's index universe AT [Complete]'s shape universe, and a family
    indexed strictly below it is refused:
      The term "G" has type "Cogenerator@{c o h} C" while it is expected
      to have type "Cogenerator@{so o h} C" (universe inconsistency:
      Cannot enforce c = so because c < so).
    The controls: [cogen_prod] at [c = so] ([p452_prod_at_so]), and
    [cogen_power], whose shape is a Σ over the index, at the same [c < so]
    ([p452_power_low_index]).

    N3 (UNIVERSE).  The unannotated [cogen_power] takes [Complete]'s
    limit-datum universe, its first slot, AT the shape universe, and a
    datum above it is refused:
      The term "comp" has type "Complete@{r so h o}" while it is expected
      to have type "Complete@{so so h o}" (universe inconsistency: Cannot
      enforce r = so because so < r).
    The controls: [cogen_power] at [r = so] ([p452_power_at_so]), and
    [cogen_prod] at the same [so < r] ([p452_prod_high_datum]).  N2 and N3
    are why Adjunction/SAFT/InitialObject.v's statements take
    [Complete@{so so h o}] and [Cogenerator@{so o h}].

    ** Small hom-sets

    N4, N5 (UNIVERSE; N5 is P_H_le_so).  The bound [h <= so], the book's
    "small hom-sets", was first measured on #452 at [cogen_power] and at
    [special_initial_object] under the binder [Complete@{so so h o}] with
    [so < h], and quoted as "Universe inconsistency. Cannot enforce h <= so
    because so < h."  That text is the binder's own.  N4, whose body is its
    argument [x] and names neither [cogen_power] nor the theorem, is
    refused with exactly it, over the whole command rather than at an
    argument:
      Universe inconsistency. Cannot enforce h <= so because so < h.
    [Complete@{r so h o}] declares [h <= r] (Structure/Complete.v) and the
    binder puts [r] at [so], so a refutation in that shape holds whatever
    its body and guards nothing about [cogen_power]; what N4 does pin is
    that declared [h <= r], read at [r = so], the shape N3's collapse gives
    the statements.  N5 is the body's own bound, with [r] kept apart.  The
    instrument [p452_binder_ok], whose body is trivial, shows the binder
    formable at [so < h <= r], and [cogen_prod] is accepted there
    ([p452_prod_small_shape]); [cogen_power_limit]'s body, written out
    because [cogen_power] itself would meet N3 first, with its shape
    argument left to unification where [Print cogen_power_limit] shows
    [Discrete.DiscreteCat (cogen_power_index G c)], is refused at the
    functor:
      The term "Discrete.DiscreteCat_Functor (cogen_power_fam G c)" has
      type "@Functor@{<1> <2> <3> o h h} (Discrete.DiscreteCat@{<1> <2>
      <3>} (@cogen_power_index@{<4> so o h} C G c)) C" while it is
      expected to have type "@Functor@{so h h o h h} ?D C" (universe
      inconsistency: Cannot enforce <1> = so because so < h <= <4> <=
      <1>).
    The chain is the bound: [cogen_power_index G c], a Σ over the family's
    index and the arrows [c ~> cog_obj G j], lies at or above the hom
    universe [h], and the discrete shape on it must sit at the shape
    universe [so].  The control is the same body at [h <= so <= r]
    ([p452_power_limit_ok]).

    ** Small objects

    N6, N7 (UNIVERSE).  [special_initial_object_small]'s route,
    [complete_intersection_IsIntersection] over the family of ALL
    subobjects of the product, at [so < o]:
      Found type "SubObj (cogen_prod comp G)" where "?J" was expected
      (unable to find a well-typed instantiation for "?J": cannot ensure
      that "Type@{max(o,h)}" is a subtype of "Type@{<1>}").
    the refusal Adjunction/SAFT/InitialObject.v's header records for the
    small route, a universe comparison reported while instantiating an
    evar.  N7 peels it, the index given explicitly:
      The term "SubObj (cogen_prod comp G)" has type "Type@{max(o,h)}"
      while it is expected to have type "Type@{<1>}" (universe
      inconsistency: Cannot enforce o <= <1> because <1> <= <2> < o).
    The controls: both terms at [o <= so] ([p452_small_route_ok],
    [p452_small_index_ok]), and the library constant there
    ([p452_small_const]).

    ** Freyd's construction

    N8 (UNIVERSE).  [special_vs_freyd]'s statement at [h < so]:
      The term "comp" has type "Complete@{so so h o}" while it is expected
      to have type "Complete@{<1> <1> <1> <2>}" (universe inconsistency:
      Cannot enforce h = so because h < so).
    Theory/WeaklyInitial.v's [initial_from_weakly_initial_complete] takes
    one universe for the shape objects, the limit datum and the homs, so
    the in-tree comparison is stated at [so = h] only; the control is the
    same statement and body there ([p452_freyd_at_h]).  Any two initial
    objects are isomorphic, so N8 bounds the route through that constant,
    not the comparison as such.

    N9 (UNIVERSE).  Freyd's construction fed [wif_of_cogenerator] with its
    index [w] strictly below the homs:
      The term "wif_of_cogenerator comp G W" has type
      "WeaklyInitialFamily@{w o h} C" while it is expected to have type
      "WeaklyInitialFamily@{h o h} C" (universe inconsistency: Cannot
      enforce w = h because w < h).
    The controls: [wif_of_cogenerator] alone at [w < h] ([p452_wif_low]),
    and the same body at [w = h] ([p452_freyd_wif_at_h], which is
    [freyd_of_cogenerator]'s body).

    ** [Sets] and [Sets^op]

    N10 (UNIVERSE).  [special_initial_object_small] at [Sets], with
    [Sets_Complete] ascribed its universes, as N13 does, and
    [Sets_Cogenerator_IEM E], the refusal Instance/Sets/SpecialInitial.v's
    header records:
      The term "Sets_Complete : Complete" has type "Complete@{o o o so}"
      while it is expected to have type "Complete@{o o o <1>}" (universe
      inconsistency: Cannot enforce <1> = so because <1> <= <2> < so).
    [Complete]'s last slot is the object universe: the small form bounds
    it by its shape universe, which at [Sets_Complete] is [o], and the
    chain puts it strictly below [so], where the objects of [Sets@{o so}]
    live.  The shape first measured on #452 left [Sets_Complete]'s
    universes to inference; a whole-file copy with that form in place of
    N10 is refused at the same argument, with every universe a serial
    number ("Cannot enforce <1> = <2> because <1> <= <3> < <2>").  The
    controls: [sets_special_initial_IEM E] at the same universes
    ([p452_sets_iem]); its body, [special_initial_object] over the least
    subobject with the ascribed [Sets_Complete] and [Sets_Cogenerator_IEM
    E] named directly ([p452_sets_iem_direct]); and
    [special_initial_object_small] itself where objects fit the shapes
    ([p452_small_const]).

    N11, N12 (UNIVERSE; P_type_truth).  The [Type]-valued route to a
    cogenerator of [Sets], which Instance/Sets/Cogenerator.v records as
    refused, quoting these two.  The object of truth values is [Type@{l}]
    under [iffT] ([p452_iff_setoid], its equivalence proved in full, so
    that each negative differs from its control in a universe only).  N11,
    the truth setoid at the carrier level itself:
      The term "{| carrier := Type; is_setoid := p452_iff_setoid |}" has
      type "SetoidObject" while it is expected to have type "obj[Sets]"
      (universe inconsistency: Cannot enforce <1> = o because o < <1>).
    Its control is the same one level down, [l < o] ([p452_truth_low]).
    N12, the test map at a point [y0] of an arbitrary object into that
    lower truth setoid, written [@equiv _ (is_setoid Y) y0 b] so that no
    class search is involved:
      The term "y0 ≈ b" has type "Type" while it is expected to have type
      "carrier {| carrier := Type; is_setoid := p452_iff_setoid |}"
      (universe inconsistency: Cannot enforce o <= l because l < o).
    Its control is the same map for [Y : SetoidObject@{l l}]
    ([p452_char_low]), and [Sets_Cogenerator_untruncate U] is accepted at
    the same universes ([p452_cog_untruncate]).  N11 is not the form first
    measured on #452, whose scratch probe left the equivalence proof as a
    hole; the kind and the bound are the same.
    Both refuse one construction; neither shows that no small cogenerator
    of [Sets] exists.

    N13, N14 (UNIVERSE; P_large_cog).  [Sets] has a [Cogenerator] with no
    hypothesis: Instance/Sets/Cogenerator.v's [Sets_Cogenerator_large],
    every object, each tested by its identity, accepted at the universes
    that file's header states ([p452_large_cog]; [About] reads
    [Cogenerator@{c so o} Sets@{o so}] under [o < c, o < so], stdlib
    bounds aside).  Its index, the type of all objects, sits strictly
    above [Sets_Complete]'s shape universe [o], where [cogen_prod] needs
    it (N2's collapse).  N13, its product at [Sets_Complete]:
      The term "Sets_Cogenerator_large" has type "Cogenerator@{c so o}
      Sets@{o so}" while it is expected to have type "Cogenerator@{o so o}
      Sets@{o so}" (universe inconsistency: Cannot enforce c = o because
      o < c).
    N14, [special_initial_object] at [Sets_Complete] over the least
    subobject [sets_special_initial_untruncate] uses, is refused with the
    same text.  Both give the family its universe instance and ascribe
    [Sets_Complete] its universes, so that the error names the bound; a
    first draft of this file left them to inference and was refused with
    the same kind, every universe then a serial number.  The controls:
    [cogen_prod] and [special_initial_object_least] take the family over a
    completeness datum [Complete@{c c o so}] whose shape universe is its
    index universe ([p452_large_prod_abstract],
    [p452_large_sio_abstract]), a hypothetical datum taken as a variable,
    [Sets_Complete] being [Complete@{o o o so}], its shape universe [o]
    and not [c]; and at [Sets_Complete] the conditional cogenerator is
    accepted in both places ([p452_small_prod_sets],
    [p452_small_sio_sets]).  What [Sets] lacks unconditionally in tree is
    a SMALL cogenerator, indexed at the shape universe of [Sets_Complete],
    and not a cogenerator.

    N15, N16 (UNIVERSE).  [Sets^op] through well-poweredness.  The only
    co-well-poweredness of [Sets] in tree, Instance/Sets/WellPowered.v's
    [Sets_CoWellPoweredAt_up], has its index at its own [t], one universe
    above the homs ([p452_sets_cowp_up], accepted per object).  N15, at
    the corollary [special_initial_object_wellpowered]:
      The term "Sets_CoWellPoweredAt_up X" has type "WellPoweredAt@{<1> <2>
      <2> o <1>} X" while it is expected to have type "WellPoweredAt@{<3>
      so <4> o <5>} X" (universe inconsistency: Cannot enforce <3> = <5>
      because <3> <= <6> < <5>).
    [WellPowered] pins the index at or below the homs, which lie strictly
    below [t].  N16, at the per-object corollary
    [special_initial_object_wellpowered_at] and the one object
    [cogen_prod setsop_comp setsop_cog], which bounds the index by
    [Complete]'s shape universe instead (at [setsop_comp] that is the hom
    universe):
      The term "Sets_CoWellPoweredAt_up (cogen_prod setsop_comp
      setsop_cog)" has type "WellPoweredAt@{<1> <2> <2> <3> <1>} (…)"
      while it is expected to have type "WellPoweredAt@{<4> <5> <6> <7>
      <8>} (…)" (universe inconsistency: Cannot enforce <4> = <8> because
      <4> <= <7> < <8>).
    with the product's universe instances elided as (…), and the numbering
    taken over the text as quoted.  The controls:
    both corollaries with the datum left free ([p452_setsop_wp_free],
    [p452_setsop_wp_at_free]).  So the hand-built least subobject
    [setsop_L] is what makes [Sets^op] unconditional, as Instance/Sets/
    SpecialInitial.v says.

    N17, N18 (CONVERSION).  Instance/Sets/SpecialInitial.v's readbacks by
    [eq_refl] discriminate: at [Sets^op] the object IS [Sets_Terminal]'s
    singleton ([p452_setsop_obj]), and at [Sets] under [IEM] it IS
    [Sets_Initial]'s empty setoid ([p452_sets_iem_obj]).  N17, the
    [Sets^op] object against the empty setoid, the error printed with
    explicit arguments throughout:
      (cannot unify "@initial_obj (Opposite Sets) setsop_special_initial"
      and "@initial_obj Sets Sets_Initial")
    N18, the [IEM] object against the singleton:
      The term "eq_refl" has type "0 = 0" while it is expected to have
      type "0 = 1" (cannot unify "0" and "1").
    Both objects are the ones handed to the theorem (the circularity
    caveat of that file's header); N17 and N18 show that the readbacks say
    which.

    CONTROLS WITHOUT A NEGATIVE.  [Indiscrete_types_special_initial]'s
    object IS [unit] by [eq_refl] ([p452_indiscrete_obj]);
    [Subsets_special_initial_is_empty] and [Sets_terminal_not_cogenerates]
    at their stated types; the book's form at [Sets] over the #451
    intersection ([p452_sets_book]).  The guard block at the end names all
    seventy constants of the four target files (twenty-nine, twelve, seven
    and twenty-two, counted as the lines of each that open with
    [Definition], [Lemma] or [Example]), so that a rename breaks this
    file. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.WellPowered.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Construction.Product.Limit.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Generator.
Require Import Category.Instance.Sets.SubobjectLattice.
Require Import Category.Instance.Sets.WellPowered.
Require Import Category.Adjunction.SAFT.InitialObject.
Require Import Category.Adjunction.SAFT.InitialObject.Examples.
Require Import Category.Instance.Sets.Cogenerator.
Require Import Category.Instance.Sets.SpecialInitial.

Generalizable All Variables.

(** ** Instrument: the refutation keyword is live *)

Fail Check probe452_absent_name.

(** ** N1 (CONVERSION): the object IS the intersection, and not the product *)

(* CONTROL: the object readback, restated. *)
Example p452_obj@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @initial_obj C (special_initial_object comp G w Hw) = Subobject.sub_dom w :=
  eq_refl.

(* CONTROL: the zero-arrow readback, restated. *)
Example p452_zero@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w)
  (c : C) :
  @zero C (special_initial_object comp G w Hw) c
    = cogen_pullback_to comp G c
        ∘ `1 (inter_le _ _ Hw (cogen_pullback_sub comp G c)) :=
  eq_refl.

(* CONTROL: the conclusion in the type. *)
Definition p452_is_initial@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  IsInitialObj (Subobject.sub_dom w) :=
  special_initial_IsInitialObj comp G w Hw.

Fail Example p452_n1_obj_is_product@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @initial_obj C (special_initial_object comp G w Hw) = cogen_prod comp G :=
  eq_refl.

(** ** N2, N3 (UNIVERSE): the two donor collapses *)

(* CONTROL: [cogen_prod] at the collapsed index universe, [c = so]. *)
Definition p452_prod_at_so@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

(* CONTROL: [cogen_power], whose shape is a Σ over the index, takes an index
   universe below the shape universe. *)
Definition p452_power_low_index@{o h so c +| h <= so, c < so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (x : C) : C :=
  cogen_power comp G x.

Fail Definition p452_n2_prod_low_index@{o h so c +| h <= so, c < so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) : C :=
  cogen_prod comp G.

(* CONTROL: [cogen_power] at the collapsed limit-datum universe, [r = so]. *)
Definition p452_power_at_so@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (x : C) : C :=
  cogen_power comp G x.

(* CONTROL: [cogen_prod] takes a limit-datum universe above the shape
   universe. *)
Definition p452_prod_high_datum@{o h r so +| h <= so, so < r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

Fail Definition p452_n3_power_high_datum@{o h r so +| h <= so, so < r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (x : C) : C :=
  cogen_power comp G x.

(** ** N4, N5 (UNIVERSE; N5 is P_H_le_so): small hom-sets, [h <= so] *)

(* INSTRUMENT: with the limit-datum universe [r] kept apart, the binder is
   formable at [so < h], so a refusal under it is about the body. *)
Definition p452_binder_ok@{o h r so +| so < h, h <= r +} {C : Category@{o h h}}
  (comp : @Complete@{r so h o} C) (G : Cogenerator@{so o h} C) (x : C) : C :=
  x.

(* With [r = so] the binder alone is refused, whatever the body. *)
Fail Definition p452_n4_binder_collapsed@{o h so +| so < h +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (x : C) : C :=
  x.

(* CONTROL: [cogen_prod] at [so < h <= r]. *)
Definition p452_prod_small_shape@{o h r so +| so < h, h <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) : C :=
  cogen_prod comp G.

(* CONTROL: [cogen_power_limit]'s body at [h <= so <= r]. *)
Definition p452_power_limit_ok@{o h r so +| h <= so, so <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :=
  comp _ (Category.Instance.Discrete.DiscreteCat_Functor (cogen_power_fam G c)).

Fail Definition p452_n5_power_limit_small_shape@{o h r so +| so < h, h <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :=
  comp _ (Category.Instance.Discrete.DiscreteCat_Functor (cogen_power_fam G c)).

(** ** N6, N7 (UNIVERSE): the small-objects route at [so < o] *)

(* CONTROL: [special_initial_object_small]'s body, objects at or below the
   shape universe. *)
Definition p452_small_route_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (complete_intersection_IsIntersection comp
       (fun m : SubObj (cogen_prod comp G) => m)).

(* CONTROL: the library constant at the same universes. *)
Definition p452_small_const@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object_small comp G.

Fail Definition p452_n6_small_route@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (complete_intersection_IsIntersection comp
       (fun m : SubObj (cogen_prod comp G) => m)).

(* CONTROL: N7's term, the family's index explicit, at [o <= so]. *)
Definition p452_small_index_ok@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) :=
  @complete_intersection_IsIntersection C comp (cogen_prod comp G)
    (SubObj (cogen_prod comp G)) (fun m : SubObj (cogen_prod comp G) => m).

Fail Definition p452_n7_small_index@{o h so +| h <= so, so < o +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) :=
  @complete_intersection_IsIntersection C comp (cogen_prod comp G)
    (SubObj (cogen_prod comp G)) (fun m : SubObj (cogen_prod comp G) => m).

(** ** N8, N9 (UNIVERSE): the comparison with Freyd's construction *)

(* CONTROL: [special_vs_freyd]'s statement and body at [so = h]. *)
Definition p452_freyd_at_h@{o h +} {C : Category@{o h h}}
  (comp : @Complete@{h h h o} C) (G : Cogenerator@{h o h} C)
  (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  @initial_obj C (special_initial_object_least comp G w Hw)
  ≅ @initial_obj C
      (initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
         (wif_of_weakly_initial (special_weakly_initial comp G w Hw))) :=
  initial_unique _ _.

Fail Definition p452_n8_freyd_above@{o h so +| h < so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  @initial_obj C (special_initial_object_least comp G w Hw)
  ≅ @initial_obj C
      (initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
         (wif_of_weakly_initial (special_weakly_initial comp G w Hw))) :=
  initial_unique _ _.

(* CONTROL: the weakly initial family of subobjects is formed with its index
   strictly below the homs. *)
Definition p452_wif_low@{o h w s t d +| w < h, h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{h d h o h} comp G)) :
  WeaklyInitialFamily C :=
  wif_of_cogenerator comp G W.

(* CONTROL: Freyd's construction takes it with the index AT the homs, which
   is [freyd_of_cogenerator]'s body. *)
Definition p452_freyd_wif_at_h@{o h s t d +| h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{h o s h t} (cogen_prod@{h d h o h} comp G)) :
  @Initial C :=
  initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
    (wif_of_cogenerator comp G W).

Fail Definition p452_n9_freyd_wif_low@{o h w s t d +|
    w < h, h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{h d h o h} comp G)) :
  @Initial C :=
  initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
    (wif_of_cogenerator comp G W).

(** ** N10 (UNIVERSE): the small-objects form at [Sets] *)

(* CONTROL: the least-subobject form at the same universes. *)
Definition p452_sets_iem@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  sets_special_initial_IEM E.

(* CONTROL: its body, with [Sets_Complete], ascribed as in N10, and
   [Sets_Cogenerator_IEM E] named directly. *)
Definition p452_sets_iem_direct@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_IEM E)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Fail Definition p452_n10_small_at_sets@{o so +| o < so +} (E : IEM@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object_small
    (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_IEM E).

(** ** N11, N12 (UNIVERSE; P_type_truth): the [Type]-valued truth setoid *)

(* [Type@{l}] under [iffT]: the classical object of truth values, with the
   library's [Type]-valued equivalence. *)
Definition p452_iff_setoid@{l m p +| l < m, l <= p +} :
  Setoid@{m p} Type@{l}.
Proof.
  refine (@Build_Setoid Type@{l} (fun P Q : Type@{l} => iffT P Q) _).
  constructor.
  - intro P; split; intro x; exact x.
  - intros P Q [a b]; split; assumption.
  - intros P Q R [a b] [c d]; split; intro x; auto.
Defined.

(* CONTROL: one level down, it IS an object of [Sets@{o so}]. *)
Definition p452_truth_low@{l o so +| l < o, o < so +} : obj[Sets@{o so}] :=
  @Build_SetoidObject Type@{l} p452_iff_setoid.

Fail Definition p452_n11_truth_at@{o so +| o < so +} : obj[Sets@{o so}] :=
  @Build_SetoidObject Type@{o} p452_iff_setoid.

(* CONTROL: the test map at a point [y0], for a setoid one level down. *)
Definition p452_char_low@{l o so +| l < o, o < so +}
  (Y : SetoidObject@{l l}) (y0 : carrier Y) :
  carrier Y → carrier (@Build_SetoidObject Type@{l} p452_iff_setoid) :=
  fun b => @equiv _ (is_setoid Y) y0 b.

Fail Definition p452_n12_char_at@{l o so +| l < o, o < so +}
  (Y : SetoidObject@{o o}) (y0 : carrier Y) :
  carrier Y → carrier (@Build_SetoidObject Type@{l} p452_iff_setoid) :=
  fun b => @equiv _ (is_setoid Y) y0 b.

(* CONTROL: the conditional cogenerator at the same universes. *)
Definition p452_cog_untruncate@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : Cogenerator Sets@{o so} :=
  Sets_Cogenerator_untruncate U.

(** ** N13, N14 (UNIVERSE; P_large_cog): a large cogenerator of [Sets] *)

(* CONTROL: Instance/Sets/Cogenerator.v's [Sets_Cogenerator_large], every
   object tested by its identity, IS a [Cogenerator] of [Sets] with no
   hypothesis, at the universes that file's header states; its index is
   the type of all objects. *)
Definition p452_large_cog@{c o so +| o < so, o < c +} :
  Cogenerator@{c so o} Sets@{o so} :=
  Sets_Cogenerator_large@{c o so}.

(* CONTROL: [cogen_prod] takes it over a completeness datum whose shape
   universe is the family's index universe.  The datum is hypothetical, a
   variable: [Sets_Complete] is [Complete@{o o o so}], its shape universe
   [o] and not the [c] above it. *)
Definition p452_large_prod_abstract@{c o so +| o < so, o < c +}
  (comp : @Complete@{c c o so} Sets@{o so}) : obj[Sets@{o so}] :=
  cogen_prod comp Sets_Cogenerator_large@{c o so}.

(* CONTROL: and so does the theorem, over any least subobject, the datum
   hypothetical as above. *)
Definition p452_large_sio_abstract@{c o so +| o < so, o < c +}
  (comp : @Complete@{c c o so} Sets@{o so})
  (w : SubObj (cogen_prod comp Sets_Cogenerator_large@{c o so}))
  (Hw : ∀ v : SubObj (cogen_prod comp Sets_Cogenerator_large@{c o so}),
          sub_le w v) :
  @Initial Sets@{o so} :=
  special_initial_object_least comp Sets_Cogenerator_large@{c o so} w Hw.

(* CONTROL: a small cogenerator's product at [Sets_Complete]. *)
Definition p452_small_prod_sets@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : obj[Sets@{o so}] :=
  cogen_prod (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_untruncate U).

Fail Definition p452_n13_large_prod_sets@{c o so +| o < so, o < c +} :
  obj[Sets@{o so}] :=
  cogen_prod (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    Sets_Cogenerator_large@{c o so}.

(* CONTROL: [sets_special_initial_untruncate]'s body, the small cogenerator
   at [Sets_Complete]. *)
Definition p452_small_sio_sets@{o so +| Set < o, o < so +}
  (U : Untruncate@{o}) : @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    (Sets_Cogenerator_untruncate U)
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

Fail Definition p452_n14_large_sio_sets@{c o so +| o < so, o < c +} :
  @Initial Sets@{o so} :=
  special_initial_object (Sets_Complete : @Complete@{o o o so} Sets@{o so})
    Sets_Cogenerator_large@{c o so}
    (sub_bot (Sets_zero_monic _))
    (intersection_all_of_least _ (sub_bot_least (Sets_zero_monic _))).

(** ** N15, N16 (UNIVERSE): [Sets^op] through well-poweredness *)

(* CONTROL: the corollary at [Sets^op] with the datum left free. *)
Definition p452_setsop_wp_free@{o so +| o < so +}
  (WP : WellPowered (Sets@{o so}^op)) : @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered WP setsop_comp setsop_cog.

(* CONTROL: the co-well-powered datum one universe up, per object. *)
Definition p452_sets_cowp_up@{o so +| o < so +} (X : SetoidObject@{o o}) :=
  Sets_CoWellPoweredAt_up@{o so so} X.

Fail Definition p452_n15_setsop_wp_up@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered (C := Sets@{o so}^op)
    (fun X => Sets_CoWellPoweredAt_up X) setsop_comp setsop_cog.

(* CONTROL: the per-object corollary at [Sets^op] with the datum left
   free. *)
Definition p452_setsop_wp_at_free@{o so +| o < so +}
  (W : WellPoweredAt (C := Sets@{o so}^op)
         (cogen_prod setsop_comp setsop_cog)) :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered_at setsop_comp setsop_cog W.

Fail Definition p452_n16_setsop_wp_at_up@{o so +| o < so +} :
  @Initial (Sets@{o so}^op) :=
  special_initial_object_wellpowered_at setsop_comp setsop_cog
    (Sets_CoWellPoweredAt_up (cogen_prod setsop_comp setsop_cog)).

(** ** N17, N18 (CONVERSION): the objects at [Sets^op] and at [Sets] *)

(* CONTROL: at [Sets^op] the object IS the singleton. *)
Example p452_setsop_obj@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

Fail Example p452_n17_setsop_obj_empty@{o so +| o < so +} :
  @initial_obj (Sets@{o so}^op) setsop_special_initial
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

(* CONTROL: at [Sets] under [IEM] the object IS the empty setoid. *)
Example p452_sets_iem_obj@{o so +| o < so +} (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @initial_obj Sets@{o so} Sets_Initial := eq_refl.

Fail Example p452_n18_sets_iem_obj_singleton@{o so +| o < so +}
  (E : IEM@{o}) :
  @initial_obj Sets@{o so} (sets_special_initial_IEM E)
    = @terminal_obj Sets@{o so} Sets_Terminal := eq_refl.

(** ** Controls without a negative *)

(* The degenerate generic witness reads back as [unit]. *)
Example p452_indiscrete_obj@{j o t +| j < o, j < t +} :
  @initial_obj (Indiscrete@{o j j} Type@{j}) Indiscrete_types_special_initial
    = (Datatypes.unit : Type@{j}) := eq_refl.

(* The non-degenerate generic witness has no members. *)
Check (Subsets_special_initial_is_empty :
  ∀ (X : SetoidObject) (G : Cogenerator (Subsets X)) (x : carrier X),
    (@initial_obj _ (Subsets_special_initial X G)
       : carrier (Powerset_Prop_obj X)) x → False).

(* The book's form at [Sets], from the #451 intersection. *)
Definition p452_sets_book@{o so +| Set < o, o < so +} (U : Untruncate@{o}) :
  @Initial Sets@{o so} :=
  special_initial_object_book Sets_Complete (Sets_Cogenerator_untruncate U)
    (Sets_HasClassIntersections_untruncate U).

(* No family of copies of the terminal object cogenerates [Sets]. *)
Check (Sets_terminal_not_cogenerates :
  ∀ I : Type,
    ¬ (∀ (x y : SetoidObject) (f g : x ~{Sets}~> y),
         (I → ∀ k : y ~{Sets}~> @terminal_obj Sets Sets_Terminal,
                k ∘ f ≈ k ∘ g) → f ≈ g)).

(** ** Guard block *)

Check @equalizer_sub.
Check @least_sub_arrows_agree.
Check @cogen_prod_to_power.
Check @cogen_canonical_sub.
Check @complete_pullbacks.
Check @cogen_pullback_sub.
Check @cogen_pullback_to.
Check @special_initial_zero.
Check @special_initial_object_least.
Check @least_of_intersection_all.
Check @intersection_all_of_least.
Check @special_initial_object.
Check @special_initial_object_obj.
Check @special_initial_object_zero.
Check @special_initial_IsInitialObj.
Check @HasClassIntersections.
Check @special_initial_object_book.
Check @special_initial_object_book_obj.
Check @wellpowered_class_intersections.
Check @special_initial_object_wellpowered.
Check @special_initial_object_wellpowered_obj.
Check @special_initial_object_wellpowered_at.
Check @special_initial_object_wellpowered_at_obj.
Check @special_initial_object_small.
Check @special_weakly_initial.
Check @special_vs_freyd.
Check @wif_of_cogenerator.
Check @freyd_of_cogenerator.
Check @special_vs_freyd_of_cogenerator.
Check @Subsets_Cogenerator_empty.
Check @Subsets_Cogenerator_bot.
Check @Subsets_special_initial.
Check @Subsets_special_initial_obj.
Check @Subsets_special_initial_empty.
Check @Subsets_special_initial_bot.
Check @Subsets_special_vs_bot.
Check @Subsets_special_initial_is_empty.
Check @Subsets_special_initial_not_top.
Check @Indiscrete_Cogenerator_empty.
Check @Indiscrete_types_special_initial.
Check @Indiscrete_types_special_initial_obj.
Check @Sets_Cogenerator_untruncate.
Check @sets_cogenerator_untruncate_obj.
Check @sets_bool_char.
Check @Sets_Cogenerator_IEM.
Check @sets_cogenerator_IEM_obj.
Check @Sets_Cogenerator_large.
Check @Sets_terminal_not_cogenerates.
Check @setsop_comp.
Check @setsop_cog.
Check @setsop_point.
Check @setsop_L.
Check @setsop_L_least.
Check @setsop_special_initial.
Check @setsop_special_obj.
Check @setsop_special_vs_known.
Check @setsop_terminal_IsInitialObj.
Check @sets_special_initial_untruncate.
Check @sets_special_untruncate_obj.
Check @sets_special_initial_wellpowered.
Check @sets_special_wellpowered_obj.
Check @sets_special_wellpowered_vs_known.
Check @sets_special_wellpowered_empty.
Check @Sets_HasClassIntersections_untruncate.
Check @sets_special_initial_book.
Check @sets_special_book_obj.
Check @sets_special_book_vs_known.
Check @sets_special_initial_IEM.
Check @sets_special_IEM_obj.
Check @sets_special_initial_IEM_at_Set.
