Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Resize.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Spanning.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The tensor product of modules from the adjoint functor theorem

    nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
    nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
    nLab:      https://ncatlab.org/nlab/show/representable+functor
    nLab:      https://ncatlab.org/nlab/show/solution+set+condition
    Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules
    Riehl:     Category Theory in Context, §4.6 and §5.6

    Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
    §V.7, book p. 128 (PDF p. 137), is the source: the unnumbered
    construction of the tensor product from the adjoint functor theorem
    (catalog id `maclane:V.7:construction1`) and Exercise 3 (catalog id
    `maclane:V.7:ex3`).  CITED BY LOCATION AND BY THE IN-TREE CATALOG
    (doc/plan/books/maclane/inventory/V.json); the printed text was not
    consulted and no sentence of it is reproduced here.  Instance/Mod/
    Spanning.v quotes the two catalog summaries in full and is not repeated.

    Mac Lane's argument has three premises and a conclusion.  The premises
    are that K-Mod is small-complete, that Bilin(A,B;-) : K-Mod -> Set is
    continuous, and that the bilinear maps which SPAN their target form a
    solution set.  The conclusion is that Bilin(A,B;-) is representable, so
    that a universal bilinear map A x B -> A (x) B exists without any
    construction by generators and relations.

    THIS FILE DELIVERS THE THREE PREMISES AND THE CONCLUSION
    UNCONDITIONALLY, and says exactly what that costs.  Two of the premises
    are discharged the obvious way: [RMod_Complete] (Instance/Mod/Limit.v,
    imported) and [Bilin_PreservesImageLimit] below.  The third is BUILT
    here twice over.

    CORRECTION, PR "algebraic carriers are sets" (2026-09-17).  Until this
    commit the paragraph above ended "THIS FILE DELIVERS THE THREE PREMISES
    AND THE CONCLUSION AS A CONDITIONAL", and this one read: "What does NOT
    go through is FEEDING it to the theorem: the index of an
    [ElementSolutionSet] that [representability_theorem] will accept must
    live at the ring's CARRIER universe, which that theorem also pins to
    [Set], while Mac Lane's index is a sigma over the OBJECTS of [RMod R],
    one universe up. ... So [tensor_via_AFT] takes its solution set as a
    hypothesis, and the same for Exercise 3."  THREE of those clauses are
    now false and one is still true.

    STILL TRUE: [tensor_esols_direct] -- Mac Lane's COVERING FAMILY, WITH
    NO SMALLNESS, indexed by the spanning bilinear maps out of V x V' -- is
    a sigma over the OBJECTS of [RMod R] and is STILL refused by the
    theorem, as NEGATIVE 1 of Test/ProbeModTensorAFT449.v pins.

    FALSE NOW: (i) the [Set], which went with the annotation of
    [DiscreteCat_Functor] in this same PR; (ii) that no solution set at the
    carrier universe exists -- section 3A builds one, [tensor_esols_prop],
    indexed by the [Prop]-valued CONGRUENCES on the term module, and it is
    accepted; (iii) that [tensor_via_AFT] takes a hypothesis -- it does
    not, and neither does [bal_tensor_via_AFT].  The conditionals are kept
    under the names [tensor_via_AFT_of_esols] and
    [bal_tensor_via_AFT_of_esols], statement for statement, so nothing is
    lost.

    THE COST, stated once and pinned: one new side condition,
    [Set < carrier] at [RMod R], the sort of [Prop] reaching the index
    universe.  Section 3A measures it and NEGATIVE 8 of the probe pins it
    with the conditional form as its control.

    AND MAC LANE'S OWN ARGUMENT IS NOT ABANDONED.  Section 10 proves his
    §V.7 Lemma 2 at [RMod R] -- the spanning family IS small up to
    isomorphism, the small index being the same congruences -- and feeds
    the resizing to the theorem as [tensor_via_AFT_maclane], a second route
    to the same statement through p. 128's argument rather than through the
    kernel congruence directly.

    ** 1. WHAT IS DELIVERED, IN NINE STEPS, AND AT WHAT STRENGTH

    (1) ELEMENTS OF A LIMITING CONE IN [Sets].  [slim_family_cone],
    [slim_elem], [slim_elem_leg] and [slim_ext]: a compatible family of
    elements is a cone out of the singleton, its mediator evaluated at [ttt]
    is the element it names, and the legs of a limiting cone are jointly
    monic on elements.  The last is not reproved -- it is
    Instance/Ab/Limit.v:292's [absets_limit_ext], which this file consumes
    rather than copying, exactly as Instance/Mod/Limit.v does.  These four
    are the whole element calculus, and BOTH continuity proofs below are
    stated against them.

    (2) MAC LANE'S COVERING FAMILY, WITH NO SMALLNESS, UNCONDITIONALLY.
    [tensor_esols_direct : ElementSolutionSet (Bilin V V')] is his p. 128
    argument: given an arbitrary bilinear beta : V x V' -> C, corestrict it
    to the submodule generated by its image
    (Instance/Mod/Spanning.v's [rbl_gen_corestrict]), observe that the
    corestriction SPANS ([rbl_corestrict_spanning], by induction on the
    generation witness -- the one new lemma the step needs), and cover beta
    by the submodule inclusion.  The index is
    [SpanningArrowsOutOf (Bilin V V') SetsOne] at [eq_refl], the SAME index
    as the conditional [tensor_esols] of Instance/Mod/Spanning.v's section 7
    -- [tensor_esols_same_index] pins that, with the wide-pullback
    hypothesis passed EXPLICITLY, since the exported instance
    [RMod_HasWidePullbacks] would be found by resolution and then refused at
    the application.  Mac Lane's Lemma 2 route (wide intersections of
    subobjects, Instance/Mod/Spanning.v) and his p. 128 route (corestrict to
    the generated submodule, here) therefore agree on the nose about WHAT
    the solution set is indexed by, and differ only in what they assume.
    CORRECTION, PR "algebraic carriers are sets" (2026-09-17).  This step
    read: "NOTHING BELOW CONSUMES [tensor_esols_direct]: the theorem will
    not accept it, for the universe reason of section 2, so the only
    solution set ever fed to [tensor_via_AFT] in tree is the CIRCULAR
    [tensor_esols_from_tensor] of step (5).  [tensor_esols_direct]'s only
    consumers are its own three [eq_refl] readbacks and
    [tensor_esols_same_index]."  The first clause is still true -- the
    theorem still will not accept THIS family -- and the rest is false.
    [tensor_esols_direct] is now the SUBJECT of section 10:
    [tensor_spanning_SmallUpToIso] proves it small up to isomorphism and
    [tensor_esols_resized] resizes it into a family the theorem does
    accept.  And the solution set fed to the AFT by default is
    [tensor_esols_prop] of section 3A, not the circular one.

    NO SMALLNESS HERE, and that is now a statement about THIS constant
    rather than about the file.  [esol_index] is a bare [Type], so Mac
    Lane's cardinality bound ("such a C consists of all finite sums") is
    not part of what the record asks for and this step supplies none.
    Section 10 supplies the SMALLNESS separately, as [SmallUpToIso]
    (Adjunction/GAFT/Resize.v), which is the shape Mac Lane's Lemma 2
    actually proves -- representatives up to isomorphism, not a cardinality
    bound.

    (3) CONTINUITY OF [Bilin V V'], UNCONDITIONALLY AND NOT VIA THE TENSOR.
    [Bilin_continuous : ContinuousFunctor (Bilin V V')] is proved
    ELEMENTWISE against an arbitrary limiting cone: the underlying cone of
    sets is limiting by Instance/Mod/Limit.v's
    [RMod_Forget_creates_continuous] (creation from [Sets_Complete], no
    adjunction presupposed), a bilinear map into the apex is exactly a
    compatible family of bilinear maps into the [K j], and the five laws
    come from joint monicity plus the law in each [K j].  No transport is
    needed and none is used: the argument never mentions the CHOSEN limit,
    so Structure/Limit/Preservation.v's [limitcone_transport] and
    [FCone_iso] -- which would have carried the statement from the created
    limit to an arbitrary one -- are available but not consumed.

    THE CIRCULAR ROUTE IS NAMED AND NOT USED.
    [preserves_image_of_representable (tensor_repr_of_UE V V')]
    (Adjunction/Representability/Sets.v:365) inhabits the same type in one
    line, and is CIRCULAR: it derives the theorem's hypothesis from the very
    tensor the theorem is meant to construct.  That is the circularity
    Instance/Ab/Limit.v:57-67 warns against and Instance/Grp/FreeAFT.v:
    182-185 discloses for its own solution set.  It is checked as a positive
    control in the probe, and NEGATIVE 6 there pins that the delivered term
    is a different one.

    (4) [Bilin_PreservesImageLimit] is [Continuous_PreservesImageLimit
    Bilin_continuous] (Construction/Comma/Creation.v:232).  That bridge is
    LOAD-BEARING and cannot be skipped: a [ContinuousFunctor] does not
    ascribe where the theorem asks for [PreservesImageLimit], the refusal
    being "cannot unify \"Limit.Limit K\" and \"Cone.Cone K\"", quoted at
    Instance/Ab/Limit.v:70-80.

    (5) THE CONSTRUCTION.  [tensor_via_AFT V V' E : Representable
    (Bilin V V')] is [representability_theorem] at [RMod_Complete R],
    [Bilin_PreservesImageLimit V V'] and a solution set [E].  It is stated
    at TOP LEVEL, outside any [Section], for the reason
    Adjunction/Representability/Sets.v:301-305 gives.
    [tensor_esols_from_tensor] -- index [unit], object [TensorMod V V'],
    element [tensor_gen] -- inhabits the hypothesis and is CIRCULAR, named
    so that the circularity is visible at every use site, exactly as
    Instance/Grp/FreeAFT.v:183's [Grp_Forget_solution_set_from_adjunction]
    is.  Its only role is to show the conditional is not vacuous;
    [tensor_via_AFT_from_tensor] is that instantiation.

    (6) THE COMPARISON, AT `≅` AND NOT AT [eq_refl].  [tensor_AFT_iso] is
    [repr_unique_iso] (Functor/Representable.v:395) against
    [tensor_repr_of_UE], the representation read off Instance/Mod/Tensor.v's
    [tensor_UniversalElement] through the DIRECT route
    [Representable_of_UniversalElement] (Theory/Universal/Element.v:695;
    the header at :638-648 says why the Yoneda-composed route at :621 is the
    wrong one at a category whose objects sit above its homs).  The
    uniqueness clause is [tensor_AFT_iso_universal]
    ([repr_unique_iso_universal], Functor/Representable.v:402 -- the bare
    line number would otherwise read as Element.v's, which it is not), and
    the two [eq_refl] legs are
    [repr_of_ue_obj] (Theory/Universal/Element.v:705) and
    [tensor_UniversalElement_obj]
    (Instance/Mod/Tensor.v:830), read back here as
    [tensor_repr_of_UE_obj].  THE OBJECT COMPARISON IS `≅`, NOT [eq_refl]:
    the adjoint functor theorem builds its object as a limit inside the
    comma category and [TensorMod] is a quotient of formal terms.
    NEGATIVE 5 of the probe pins that.

    (7) AND THE COMPARISON CARRIES THE UNIVERSAL ELEMENT.
    [tensor_AFT_iso_carries_elem] says the AFT's universal bilinear map,
    transported along [tensor_AFT_iso] itself, IS [tensor_gen] at `≈`; the
    proof is naturality of the representation followed by
    [repr_induced_compatible] at the identity, and nothing about the
    solution set enters.  [tensor_AFT_elem_iso] is the element-level
    comparison ([universal_element_iso], Theory/Universal/Element.v:766),
    [tensor_AFT_elem_unique] its uniqueness clause
    ([universal_element_unique], :784), and [tensor_AFT_isos_agree] proves
    the two comparisons are the same isomorphism at `≈`.

    (8) EXERCISE 3: THE BALANCED TENSOR.  The balanced tensor of a right and
    a left module over a possibly non-commutative ring already exists
    (Instance/Mod/Bimodule.v:676's [BalTensor], landing in [Ab]); what did
    not exist is the FUNCTOR it represents.  [BalBiadd N M : Ab ⟶ Sets] is
    it -- object part [BalBiadditive N M A] with the pointwise setoid,
    arrow part postcomposition, on the pattern of Instance/Mod/
    Tensor.v:736-790 -- together with [bal_universal_element :
    AUniversalElement (BalBiadd N M) (BalTensor N M)] built from [bal_med]
    and [bal_med_unique], whose object and element read back at [eq_refl].
    [BalBiadd_continuous] is the continuity, elementwise over [Ab]'s created
    limits ([Ab_Forget_creates_continuous], Instance/Ab/Limit.v:764) through
    the SAME four lemmas of step (1); [bal_tensor_via_AFT N M E] is the
    construction over [Ab_Complete]; [bal_AFT_iso] and
    [bal_AFT_iso_carries_elem] are the comparison with [BalTensor] and its
    element clause, and [bal_AFT_isos_agree] identifies the two.

    (9) EXERCISE 3'S SOLUTION SET, UNCONDITIONALLY.  [bal_esols_direct] is
    Mac Lane's argument over [Ab], and it needed four pieces of [Ab]
    vocabulary that were not in tree: [ABGenSub] (Instance/Mod/Spanning.v's
    [ABGen] has exactly the five fields of Instance/Ab/DirectedColimit.v:
    273's [AbSubgroup], so this is repackaging with no obligation),
    [AbImageSub] (the image of a homomorphism as a subgroup, the [Ab]
    counterpart of Instance/Mod/Quotient.v:761's [ImageSubmod]), [ab_split]
    (a bijective homomorphism splits) and [abg_subobj] (a subgroup as a
    [SubObj Ab], through [ab_injective_monic]).
    [bal_spanning_to_spanning] is then the [Ab] form of Instance/Mod/
    Spanning.v's [rbilinear_spanning_to_spanning], and
    [bal_gen_corestrict]/[bal_corestrict_spanning] the [Ab] form of the
    corestriction of step (2).

    ** 2. THE UNIVERSE WALL, MEASURED -- A HISTORY SECTION AND ONE LIVE
       CLAIM

    READ THIS SECTION AS THE RECORD OF A WALL THAT WAS ROUTED AROUND, not
    as a live limitation of the file.  Exactly one claim in it is still
    live: [tensor_esols_direct], the OBJECT-indexed family, is still
    refused by [representability_theorem].  Everything the section says
    about that refusal stands.  What it used to conclude from it -- that no
    unconditional construction was possible -- was corrected in the PR
    "algebraic carriers are sets" (2026-09-17) and is marked below.

    The chain.  The solution set's INDEX universe is also the SHAPE
    universe of the [Complete] the theorem is handed, and [RMod_Complete]
    puts that at the ring's carrier universe.  The current signature of
    [representability_theorem] is carried by
    Adjunction/Representability/Sets.v:386-393 and is CITED rather than
    re-quoted here: an earlier revision of this comment quoted it as

      representability_theorem@{u u0 … u9} :
        ∀ {C : Category@{u8 Set Set}} (K : C ⟶ Sets@{Set u9}),
          Complete@{u7 u7 Set u8} → … ElementSolutionSet@{u8 Set u9 u7} K
          → Representable@{u u8 u9 u8 Set} K

    with FOUR literal [Set]s, every one of them a universe-minimization
    artifact of Instance/Discrete.v's then-unannotated
    [DiscreteCat_Functor], repaired in the same PR.  The quote is stale;
    the ARITHMETIC it illustrated is not, and Structure/Complete.v's SIZE
    NOTE, item 2, is the authority for it.

    Mac Lane's index is [SpanningArrowsOutOf (Bilin V V') SetsOne], a sigma
    over [obj[RMod R]], and [RModObject] is a record over a [SetoidObject],
    so its objects sit STRICTLY ABOVE its carriers.  The two cannot meet,
    and

      Definition n1 {R : RingObject} (V V' : RModObject R) :
        Representable (Bilin V V') :=
        representability_theorem (Bilin V V') (RMod_Complete R)
          (Bilin_PreservesImageLimit V V') (tensor_esols_direct V V').

    is refused.  THE REFUSAL IS NOT RE-QUOTED HERE.
    Test/ProbeModTensorAFT449.v's NEGATIVE 1 carries the re-measured,
    [Set]-free text with its own recorded correction, and is the single
    place it is maintained; an earlier revision of this comment quoted the
    pre-repair form, with "Cannot enforce Set = u_obj' because
    Set < u_obj'", and that message no longer occurs.

    The spanning-arrow route is refused for a related reason seen from the
    other side:

      @GAFT_from_spanning (RMod R) Sets (Bilin V V') HWP
        (Bilin_PreservesWidePullbacks V V') (RMod_Complete R)
        (Bilin_PreservesImageLimit V V')

    is refused, and that refusal has MOVED TWICE.  An earlier revision of
    this comment quoted it at the completeness argument, "The term
    \"RMod_Complete R\" has type \"Complete@{Set Set Set u}\" …"; it then
    moved to the ambient category argument when [DiscreteCat_Functor] was
    annotated, and moved again when this PR widened
    Adjunction/SpanningArrow.v's [Section GAFTFromSpanning] off [Set].  It
    now reads, with the generated universe names replaced by readable ones
    positionally and everything else verbatim,

      The term "RMod R" has type "Category@{u_obj u_hom u_hom}"
      while it is expected to have type "Category@{u_obj' u_hom' u_hom'}"
      (universe inconsistency: Cannot enforce u_hom = u_hom' because
       u_hom < u_obj <= u_hom')

    -- the widened theorem wants objects at or below homs, and [RMod R] has
    homs strictly below objects.  So NO ADJUNCTION is delivered here, only
    a representation; see NOT DELIVERED (2), which is unchanged.  Exercise
    3 meets the index refusal at [Ab] ([bal_esols_direct] into
    [bal_tensor_via_AFT_of_esols]).  All three are NEGATIVES 1, 2 and 3 of
    Test/ProbeModTensorAFT449.v, each stripped and re-run in a copy of the
    whole probe so the refusal kind could be read rather than guessed.

    A WALL OF THE SAME FAMILY AS #1309, MEASURED NOT TO BE LIFTED BY IT.
    Instance/Grp/FreeAFT.v:91-110 measures a wall of this family at [Grp]
    -- Mac Lane's literal index [Subgroup Gfix] refused there too -- and
    attributes the [Set] to a universe-MINIMIZATION artifact of
    Instance/Discrete.v's [DiscreteCat_Functor], which carries no universe
    binders; it reports the repair as three annotated lines, measured
    against eleven recorded boundaries, filed as #1309, and records at
    :128-140 that WITH that repair the [Grp] solution set IS accepted.
    THE REPAIR WAS APPLIED AND MEASURED; IT DOES NOT LIFT THIS WALL.
    With only the #1309 edit
    ([Program Definition DiscreteCat_Functor@{o h p co ch cp +} ...])
    applied in a full copy of the worktree and the tree rebuilt, the
    literal [Set] vanishes from the refusal but the refusal remains, now
    as the identification of the index universe with the ring's carrier
    universe: the [n1] quoted above then reports "The term
    \"tensor_esols_direct V V'\" has type \"ElementSolutionSet@{u_a u_b
    u_c u_a} ...\" while it is expected to have type
    \"ElementSolutionSet@{u_d u_b u_e u_b} ...\" (universe inconsistency:
    Cannot enforce u_d = u_b because u_b < u_d)", with NO [Set] anywhere
    in the message, and the [Ab] refusal of Exercise 3 likewise ("Cannot
    enforce u_f = u_g because u_g < u_f").  The structural reason survives
    the repair: [Sets_Complete@{u u0} : Complete@{u u u u0}] fixes the
    shape universe at the carrier universe, while the index is a sigma
    over objects and [Submodule W : Type@{u}] with [carrier < u] puts any
    subobject-shaped index strictly above the carrier.  Three further
    repair attempts -- an explicitly annotated [ElementSolutionSet] with
    [Constraint Set < iu], a fully named [@representability_theorem], and
    the same with [RMod_Complete] replaced by an abstract
    [comp : @Complete (RMod R)] -- are each refused too, the last showing
    the identification is not [RMod_Complete]'s.

    AND THE WALL WAS NOT LIFTED; IT WAS ROUTED AROUND.  CORRECTION, PR
    "algebraic carriers are sets" (2026-09-17).  The paragraph above used
    to end: "Nothing here claims the wall is unavoidable.  What is claimed
    is that until it moves -- and landing #1309 alone is measured NOT to
    move it -- an AFT construction of the tensor product at [RMod R] is
    either conditional on a solution set at the ring's carrier universe, or
    circular.  This file delivers both readings and labels each."  That was
    the headline sentence of the file and it is FALSE.  The wall has not
    moved: every refusal recorded above still stands, verbatim in substance,
    and the structural reason still holds of any index shaped as a sigma
    over objects or as a [Type]-valued congruence.  What changed is that an
    index of a THIRD shape was built -- the [Prop]-valued congruences on
    the term module (section 3A) -- and [Prop] is carrier-sized
    (Structure/Complete.v's SIZE NOTE, item 1).  A solution set at that
    index is accepted, so the construction is UNCONDITIONAL and
    NON-CIRCULAR, at an arbitrary ring, at the cost of the one side
    condition [Set < carrier].  Section 10 then shows the two readings were
    never as far apart as this section suggested: Mac Lane's OWN family IS
    small up to isomorphism, with the congruences as its small index.

    ** 3. MEASURED

    RE-MEASURED after the PR "algebraic carriers are sets" (2026-09-17);
    an earlier revision read 111 constants (78 heads, 33 obligations) and
    the criteria below are unchanged, only the counts.

    161 constants: 121 [.glob] declaration heads (94 [def], 27 [prf]) plus
    40 [Program] obligations, which appear in NEITHER the [.glob] heads NOR
    [Search inside].  The heads were counted with
    [awk '/^(def|prf) /{print $4}' Instance/Mod/TensorAFT.glob | sort -u];
    the obligations with
    [strings Instance/Mod/TensorAFT.vo | grep -o
    '[A-Za-z0-9_]*_obligation_[0-9]*' | sed 's/^[0-9]*//' | sort -u] -- the
    junk digit prefix STRIPPED, not dropped, most appearing in the census
    only prefixed ([5BalBiadd_obligation_1], [6Bilin_med_obligation_1] and
    the rest).  ALL 161 report "Closed under the global context", with zero
    [Axioms:] lines, run through a generated scratch file of
    [Print Assumptions Category.Instance.Mod.TensorAFT.<name>] -- the
    obligations answer only to the qualified name.

    Counted BY TOKEN over the whole file with the criterion
    [grep -o 'Qed\.'] and [grep -o 'Defined\.'] -- the trailing period is
    what keeps the words used in this comment out of the count -- the
    numbers are 54 proof terminators of the first kind and FIFTEEN of the
    second (an earlier revision read 50 and EIGHT).

    WHICH OF THE FIFTEEN ARE LOAD-BEARING: SIX, each shown so by making it
    opaque in a copy of the WHOLE file and naming what stops.

    The two the earlier revision named are unchanged: [tensor_esols_direct]
    (then [tensor_esols_direct_index] and its two siblings stop, their
    [eq_refl] having the wrong type) and [bal_esols_direct] (then
    [bal_esols_direct_index] and its two siblings stop).

    Of the SEVEN added by this PR, FOUR are load-bearing, measured by
    flipping each one individually and recompiling the file and then
    Test/ProbeModTensorAFT449.v:
      [ker_iso]                     -- THE FILE stops: section 10's arrow
                                       clause needs its [to] component
                                       convertible.
      [tensor_esols_prop]           -- the PROBE stops ([p449_prop_obj],
                                       [p449_prop_elem]).
      [bal_esols_prop]              -- the PROBE stops
                                       ([p449_bal_prop_obj]).
      [tensor_spanning_SmallUpToIso] -- the PROBE stops
                                       ([p449_maclane_small_index]).
    The other three added here -- [QMod_gen_spanning], [mgen_preimage] and
    [ker_med_surjective] -- were flipped individually and BOTH file and
    probe still compile; their transparency is a choice, kept so the
    covering data stays computable.

    The five older non-load-bearing ones -- [rbl_corestrict_spanning],
    [tensor_esols_from_tensor], [bal_esols_from_tensor],
    [bal_restrict_image], [bal_spanning_to_spanning] and
    [bal_corestrict_spanning] -- are as the earlier revision recorded them
    and were not re-flipped in this PR.  (That list names six; the earlier
    revision's arithmetic "the other six" counted them against eight
    terminators and is left as written, since the names are what a reader
    needs.)

    UNIVERSES ([About] under [Set Printing Universes], all 161).
    RE-MEASURED, and the previous paragraph is withdrawn in full.  It read:
    "EXACTLY 21 of the 111 carry a word-bounded [Set], and they are
    precisely the two AFT applications and everything downstream of them",
    and it quoted [tensor_via_AFT@{…} : ∀ {R : RingObject@{Set u8 u8}} …],
    [tensor_AFT_iso@{…} : ∀ {R : RingObject@{Set Set Set}} …] and
    [bal_tensor_via_AFT@{…} : ∀ {X : RingObject@{Set u5 u5}} …] as its
    headlines, with a paragraph attributing the [RingObject@{Set Set Set}]
    pin by isolation.  ALL OF IT IS STALE: every one of those [Set]s was
    the universe-minimization artifact of Instance/Discrete.v's
    [DiscreteCat_Functor], repaired in the PR "algebraic carriers are
    sets".

    Measured now, with the criterion "a word-bounded [Set] appearing as a
    universe ARGUMENT inside an [@{…}] list in the printed type":
    ZERO of the 161.  The command was an [About] of every name, generated
    from the [.glob] heads and the obligation census above, with
    [grep -E '@\{[^}]*\bSet\b'] over the output -- no hits, against 144
    lines that do print [RingObject@{…}], which is the instrument control.

    A DIFFERENT criterion, and the one that now matters: "a [Set < …] line
    in the CONSTRAINT block".  Of the 133 names that print a universe list
    at all, 100 carry one.  These are bounds, not pins -- [Set < u] only
    says [u] is above [Set], which Lib.v:17's
    [Unset Universe Minimization ToSet] makes the default -- and the one
    that is a genuine SIDE CONDITION rather than noise is section 3A's
    [Set < carrier] on the unconditional constants.  Headlines:

      tensor_via_AFT@{u u0 u1 u2 …} :
        ∀ {R : RingObject@{u10 u2 u11}} (V V' : obj[RMod … R]),
        Representable@{u u0 u1 u0 u2} (Bilin … V V')
      (* … Set < u2 / u2 < u0 / u2 < u1 … *)      <-- u2 IS the carrier

      tensor_via_AFT_of_esols@{… u2 …} :
        ∀ {R : RingObject@{u13 u2 u14}} … ElementSolutionSet@{u0 u2 u1 u2}
        (Bilin … V V') → Representable@{u u0 u1 u0 u2} (Bilin … V V')
      (* … Set < u0 / Set < u11 / u2 < u0 / u2 < u1 / u2 < u11 … *)
                                                  <-- NO bound on u2

      CongIdx@{u u0 u1 u2 u3 u4} : ∀ {R : RingObject@{u u0 u1}},
        obj[RMod@{u2 u3 u u1 u0} R] → obj[RMod@{u2 u3 u u1 u0} R] → Type@{u4}
      (* … u0 <= u4 … *)          <-- the index may be taken AT the carrier

    THE ASYMMETRY AT [Ab], measured and not explained.  The same comparison
    for Exercise 3 shows [bal_tensor_via_AFT]'s block gaining exactly ONE
    line over [bal_tensor_via_AFT_of_esols]'s -- [Set < Projections.u0], a
    bound on a stdlib constant -- and NO new bound on the ring's carrier
    slot.  So the [Ab] half pays nothing the conditional was not already
    paying, while the [RMod R] half pays [Set < carrier].  Why the two
    differ is not established here.

    [Require] discipline: THIRTY-ONE imports (an earlier revision read 28;
    the PR "algebraic carriers are sets" added Category.Lib.Setoid.
    Propositional for [PropEquiv], and Category.Adjunction.GAFT together
    with Category.Adjunction.GAFT.Resize for section 10's [SolutionSet] and
    [SmallUpToIso]).  The earlier revision's closure figure of 169 files,
    and its record that four imports the first draft carried were droppable
    -- Category.Theory.Morphisms, Category.Structure.Limit,
    Category.Structure.Complete and Category.Adjunction.GAFT -- stand as
    written, except that the LAST of those four is now back, and is now
    load-bearing.  The closure was NOT recomputed in this PR and the figure
    169 should be read as the earlier measurement, not as current.

    Zero DECLARATION-HEAD COLLISIONS was measured for the earlier 111
    names by scanning every other [.glob] file in the landed tree for a
    [def]/[prf]/[ind]/[constr]/[scheme]/[inst] head equal to one of them,
    the file list produced by [find] and fed through [xargs] so that no
    [.gitignore] traversal rule can apply (ugrep honours [.gitignore] on
    traversal and returns nothing for names that exist).  THE SCAN WAS NOT
    RE-RUN for the 50 names this PR adds; a later reader should not cite
    the zero as covering them.

    [make todo] gains hits only from Test/ProbeModTensorAFT449.v, which now
    carries EIGHT guarded commands (seven before this PR) and NINE
    case-insensitive hits, the ninth being one prose mention of the guard's
    name; this file contributes none, measured by running the Makefile's
    own [MISSING] pattern over it.

    ** 4. NOT DELIVERED

    (1) WITHDRAWN.  This clause read "NO UNCONDITIONAL REPRESENTATION.
    [tensor_via_AFT] and [bal_tensor_via_AFT] take a solution set as a
    hypothesis, for the measured universe reason of section 2.  The only
    in-tree inhabitants of that hypothesis are the two CIRCULAR ones,
    [tensor_esols_from_tensor] and [bal_esols_from_tensor], read off the
    tensor products the theorem is meant to construct.  So what is
    demonstrated is that the machinery applies and that its output agrees
    with the explicit construction -- NOT that the tensor product exists
    independently of the explicit construction.  Instance/Grp/FreeAFT.v is
    in exactly this position and says so."  The PR "algebraic carriers are
    sets" (2026-09-17) makes every sentence of it false, at both [RMod R]
    and [Ab], and Instance/Grp/FreeAFT.v moved with it.  WHAT IS DELIVERED
    IN ITS PLACE: [tensor_via_AFT] and [bal_tensor_via_AFT] take nothing
    beyond the ring and the modules; the tensor product of modules EXISTS
    by the adjoint functor theorem independently of the explicit
    construction, and [tensor_AFT_iso] then compares the two.  The
    circular constants are kept as remarks and are removal candidates.

    (1') THE SIDE CONDITION THAT REPLACES IT, so that this list is not
    shorter than it should be: the unconditional constants at [RMod R]
    carry [Set < carrier].  Section 3A states it, section 3 measures it
    against the conditional forms, and NEGATIVE 8 of the probe pins it.

    (2) NO ADJUNCTION.  [GAFT] and [GAFT_from_spanning] produce a left
    adjoint; both are refused at [RMod R] (section 2), so nothing here is a
    functor [Sets ⟶ RMod R] and no [⊣] appears below.  UNCHANGED by this
    PR and re-measured under the widening of
    Adjunction/SpanningArrow.v's [Section GAFTFromSpanning]: the refusal
    survives, with a new message, quoted in section 2.  Section 10's
    discharge of Mac Lane's Lemma 2 does NOT change this -- what Lemma 2
    supplies is the SMALLNESS premise, not [GAFT_from_spanning]'s wide
    pullbacks.  The tensor's parametrized adjunctions already in tree
    (Instance/Mod/Closed.v's [RMod_SymMonClosed],
    Instance/Mod/Bimodule.v:1494) are untouched and unrelated.

    (3) NO CARDINALITY BOUND, and a correction.  This clause read "NO
    SMALLNESS, hence no cardinality bound: [esol_index] is a bare [Type],
    as Adjunction/SpanningArrow.v:199-206 says of itself."  The premise is
    still true of [esol_index] and of [tensor_esols_direct], and the
    conclusion no longer follows for the file: section 10 proves the
    spanning family SMALL UP TO ISOMORPHISM ([SmallUpToIso],
    Adjunction/GAFT/Resize.v), which is what Mac Lane's Lemma 2 actually
    asserts.  What is still not delivered is a CARDINALITY bound -- "such a
    C consists of all finite sums" -- which nothing here supplies and which
    [SmallUpToIso] does not imply.

    (4) NO [eq_refl] OBJECT COMPARISON, only `≅` with a uniqueness clause
    (probe NEGATIVE 5).

    (5) HALF WITHDRAWN.  This clause read "NO CONCRETE WITNESS.  Nothing
    below instantiates [R] at a named ring, so nothing exhibits the AFT
    object at [Int_Ring] or anywhere else".  THAT HALF IS FALSE: nothing in
    THIS FILE instantiates [R], but Test/ProbeModTensorAFT449.v's
    [Section UnconditionalPayoff] now does, at [Int_Ring], at [Q_Ring] and
    at [Ring_op Int_Ring], for both the direct and the Mac Lane routes and
    for Exercise 3 -- which was impossible while the construction took a
    solution set it had no honest inhabitant for.  THE OTHER HALF STANDS:
    the tree still has no non-commutative ring at all
    (Instance/Mod/Tensor.v:119-175 records that gap), so Exercise 3's
    non-commutative reading stays uninstantiated here as elsewhere, the
    opposite ring of a commutative one being commutative.

    (6) NOTHING ABOUT THE BASE-CHANGE CLAUSE of Exercise 3.  Instance/Mod/
    Spanning.v's [bal_change] and [bal_change_surjective] are that clause
    and are not extended here; the kernel of the comparison is still not
    described.

    (7) WITHDRAWN AS TO ITS FIRST CLAUSE.  It read "NO REPAIR OF THE
    UNIVERSE ARTIFACT.  Instance/Discrete.v is not touched, and #1309 stays
    open".  The annotation landed in the PR "algebraic carriers are sets"
    (2026-09-17) and every [Set] this file used to quote went with it.  The
    SECOND clause stands and was the point of recording it: landing #1309
    did not lift this file's wall, as section 2 measures, and the wall was
    routed around by a different index rather than moved.

    (8) NOTHING IS REGISTERED AS AN [Instance] -- a representation and a
    solution set must not become globally resolvable.  The constants ARE
    registered in the Makefile's [make print-assumptions] gate block, one
    [Print Assumptions Category.Instance.Mod.TensorAFT.<name>] line each,
    so the axiom-free report of section 3 is re-run by that target rather
    than only by the scratch file it was first measured with.  (An earlier
    revision said "All 111 constants"; the count is now 161, and the gate
    block was extended in the same PR.)

    (9) NO UNIQUENESS FOR THE RESIZING.  [SmallUpToIso] is data, not a
    property (Adjunction/GAFT/Resize.v's header says so), so section 10
    chooses ONE small family of representatives and nothing here says a
    different choice gives the same [tensor_via_AFT_maclane].  The AFT's
    output is determined only up to isomorphism in any case, and
    [tensor_AFT_iso] is where that is made explicit. *)

(** ** 1. Elements of a limiting cone in [Sets] *)

Section SetsLimitElements.

Context {J : Category}.
Context {G : J ⟶ Sets}.
Context {N : Cone G}.
Context (HN : IsLimitCone N).

(* A compatible family of elements is a cone out of the singleton. *)
Definition slim_family_cone (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) : Cone G :=
  @Build_Cone J Sets G SetsOne
    (@Build_ACone J Sets SetsOne G (fun x => global_element (b x))
       (fun x y f _ => Hb x y f)).

Definition slim_elem (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) :
  carrier (vertex_obj[N]) :=
  unique_obj (HN (slim_family_cone b Hb)) ttt.

Lemma slim_elem_leg (b : ∀ x : J, carrier (G x))
  (Hb : ∀ (x y : J) (f : x ~{J}~> y), fmap[G] f (b x) ≈ b y) (x : J) :
  cone_leg N x (slim_elem b Hb) ≈ b x.
Proof using All.
  exact (unique_property (HN (slim_family_cone b Hb)) x ttt).
Qed.

Lemma slim_ext (u v : carrier (vertex_obj[N]))
  (H : ∀ x : J, cone_leg N x u ≈ cone_leg N x v) : u ≈ v.
Proof using All. exact (absets_limit_ext (limitcone_isalimit HN) u v H). Qed.

End SetsLimitElements.

(** ** 2. Mac Lane's direct solution set for [Bilin V V'] *)

Section DirectSolutionSet.

Context {R : RingObject}.
Context (V V' : RModObject R).

(* The corestriction of a bilinear map to the submodule generated by its
   image spans that submodule, by induction on the generation witness. *)
Lemma rbl_corestrict_spanning {W : RModObject R} (β : RBilinear V V' W) :
  RBilinearSpanning (rbl_gen_corestrict β).
Proof using.
  intros [a D].
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|r a D IH].
  - refine (mgen_base (rbl_image (rbl_gen_corestrict β)) _ _).
    destruct Ha as [v [w Hvw]].
    exists v, w; exact Hvw.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _ IH).
    exact Hab.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_zero (rbl_image (rbl_gen_corestrict β)))).
    reflexivity.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_plus (rbl_image (rbl_gen_corestrict β)) _ _ IH1 IH2)).
    reflexivity.
  - refine (mgen_resp (rbl_image (rbl_gen_corestrict β)) _ _ _
              (mgen_smul (rbl_image (rbl_gen_corestrict β)) r _ IH)).
    reflexivity.
Defined.

Definition tensor_esols_direct : ElementSolutionSet (Bilin V V').
Proof using.
  unshelve refine
    {| esol_index := SpanningArrowsOutOf (Bilin V V') SetsOne
     ; esol_obj := fun i => `1 i
     ; esol_elem := fun i => `1 (`2 i) ttt |}.
  intros c β.
  unshelve eexists.
  - refine (existT _ (SubmoduleMod (SubGenMod (rbl_image β))) _).
    refine (existT _ (global_element
                        (X := Bilin V V' (SubmoduleMod
                                (SubGenMod (rbl_image β))))
                        (rbl_gen_corestrict β)) _).
    exact (rbilinear_spanning_to_spanning (rbl_gen_corestrict β)
             (rbl_corestrict_spanning β)).
  - exists (smod_incl (SubGenMod (rbl_image β))).
    intros v w; reflexivity.
Defined.

Example tensor_esols_direct_index :
  esol_index tensor_esols_direct = SpanningArrowsOutOf (Bilin V V') SetsOne
  := eq_refl.

Example tensor_esols_direct_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj tensor_esols_direct i = `1 i := eq_refl.

Example tensor_esols_direct_elem
  (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem tensor_esols_direct i = `1 (`2 i) ttt := eq_refl.

(* The conditional solution set of Instance/Mod/Spanning.v and the
   unconditional one above are indexed by the SAME type, on the nose. *)
Example tensor_esols_same_index
  (HWP : @HasWidePullbacks (RMod R)) :
  esol_index (@tensor_esols R V V' HWP) = esol_index tensor_esols_direct
  := eq_refl.

End DirectSolutionSet.

(** ** 3. [Bilin V V'] is continuous *)

Section BilinContinuity.

Context {R : RingObject}.
Context (V V' : RModObject R).

Section AtALimitingCone.

Context {J : Category}.
Context {K : J ⟶ RMod R}.
Context {N : Cone K}.
Context (HN : IsLimitCone N).

(* The underlying cone of SETS is limiting, by Instance/Mod/Limit.v's
   creation result -- the only input from the module side. *)
Definition bilin_sets_limit : IsLimitCone (FCone (RMod_Forget R) N) :=
  RMod_Forget_creates_continuous R J K N HN.

(* Joint monicity of the legs on ELEMENTS, in the spelling the module laws
   below present their goals in.  [slim_ext] states the same thing with
   [cone_leg (FCone (RMod_Forget R) N) x]; the two are convertible, and
   only this spelling is rewritable against [cmon_map_plus]. *)
Lemma bilin_lim_ext (u v : carrier (cmon_setoid vertex_obj[N]))
  (H : ∀ x : J, cmon_map (rm_hom (cone_leg N x)) u
                  ≈ cmon_map (rm_hom (cone_leg N x)) v) : u ≈ v.
Proof using All. exact (slim_ext bilin_sets_limit u v H). Qed.

Section AtACone.

Context (Q : Cone (Bilin V V' ◯ K)).

Lemma bilin_family_compat (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V'))
  (x y : J) (f : x ~{J}~> y) :
  fmap[RMod_Forget R ◯ K] f (rbl_map (cone_leg Q x q) v w)
    ≈ rbl_map (cone_leg Q y q) v w.
Proof using All.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ Q) x y f q v w).
Qed.

Definition bilin_med_elem (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  carrier (cmon_setoid vertex_obj[N]) :=
  slim_elem bilin_sets_limit (fun x => rbl_map (cone_leg Q x q) v w)
    (fun x y f => bilin_family_compat q v w x y f).

Lemma bilin_med_elem_leg (q : carrier (vertex_obj[Q]))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) (x : J) :
  cmon_map (rm_hom (cone_leg N x)) (bilin_med_elem q v w)
    ≈ rbl_map (cone_leg Q x q) v w.
Proof using All.
  exact (slim_elem_leg bilin_sets_limit
           (fun x => rbl_map (cone_leg Q x q) v w)
           (fun x y f => bilin_family_compat q v w x y f) x).
Qed.

Program Definition Bilin_med (q : carrier (vertex_obj[Q])) :
  RBilinear V V' vertex_obj[N] := {|
  rbl_map := bilin_med_elem q
|}.
Next Obligation.
  intros q v v' Hv w w' Hw.
  apply bilin_lim_ext; intro x.
  rewrite !bilin_med_elem_leg.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros q v v' w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (cmon_map_plus (rm_hom (cone_leg N x))).
  rewrite !bilin_med_elem_leg.
  apply rbl_add_l.
Qed.
Next Obligation.
  intros q v w w'.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (cmon_map_plus (rm_hom (cone_leg N x))).
  rewrite !bilin_med_elem_leg.
  apply rbl_add_r.
Qed.
Next Obligation.
  intros q r v w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (rm_map_smul (cone_leg N x)).
  rewrite !bilin_med_elem_leg.
  apply rbl_smul_l.
Qed.
Next Obligation.
  intros q r v w.
  apply bilin_lim_ext; intro x.
  rewrite bilin_med_elem_leg.
  rewrite (rm_map_smul (cone_leg N x)).
  rewrite !bilin_med_elem_leg.
  apply rbl_smul_r.
Qed.

Program Definition Bilin_cone_med :
  vertex_obj[Q] ~{Sets}~> vertex_obj[FCone (Bilin V V') N] :=
  {| morphism := Bilin_med |}.
Next Obligation.
  intros q q' Hq v w.
  change (bilin_med_elem q v w ≈ bilin_med_elem q' v w).
  apply bilin_lim_ext; intro x.
  rewrite !bilin_med_elem_leg.
  exact (proper_morphism (cone_leg Q x) q q' Hq v w).
Qed.

End AtACone.

Theorem Bilin_preserves_cone : IsLimitCone (FCone (Bilin V V') N).
Proof using All.
  intro Q.
  unshelve refine {| unique_obj := Bilin_cone_med Q |}.
  - intros x q v w.
    exact (bilin_med_elem_leg Q q v w x).
  - intros u Hu q v w.
    apply bilin_lim_ext; intro x.
    rewrite (bilin_med_elem_leg Q q v w x).
    symmetry; exact (Hu x q v w).
Qed.

End AtALimitingCone.

Definition Bilin_continuous : ContinuousFunctor (Bilin V V') :=
  fun J K N HN => Bilin_preserves_cone HN.

Definition Bilin_PreservesImageLimit :
  @PreservesImageLimit (RMod R) Sets (Bilin V V') :=
  Continuous_PreservesImageLimit Bilin_continuous.

End BilinContinuity.

(** ** 3A. [Prop] congruences on the term module: a solution set AT the
       carrier universe *)

(* THE REPAIR OF THE WALL OF SECTION 2 OF THE HEADER, AND WHY IT WORKS.

   Mac Lane's index is a sigma over the OBJECTS of [RMod R], which sit
   strictly above its carriers; the theorem wants the index AT the carrier
   universe (Structure/Complete.v's SIZE NOTE, item 2(b), is the authority
   and is not restated).  What is built here is a DIFFERENT index for the
   same job: the [Prop]-valued congruences on the term module [MTerm V V'].

   Every field of [IsCongruence] is a [Prop], so the record is a [Prop] and
   the sigma over it lands at the carrier universe -- item 1 of the SIZE
   NOTE, read forwards rather than as an obstruction.  Measured, [About]
   under [Set Printing Universes]:

     CongIdx@{u u0 u1 u2 u3 u4} :
       ∀ {R : RingObject@{u u0 u1}},
       obj[RMod@{u2 u3 u u1 u0} R] → obj[RMod@{u2 u3 u u1 u0} R] → Type@{u4}
     (* … Set < u2 / Set < u4 / u0 < u2 / u0 < u3 / u <= u2 / u0 <= u4 /
          u1 <= u *)

   [u0] is the ring's carrier universe and [RMod]'s hom universe; the ONLY
   bound on the index [u4] is [u0 <= u4], so [u4 := u0] is expressible and
   the theorem accepts the family.  Contrast [tensor_esols_direct], measured
   in the same run: its index gives [ElementSolutionSet@{u12 u0 u16 u12}]
   with [u0 < u12] -- strictly above.  That single inequality is the whole
   wall and the whole repair.  The wall is not LIFTED; it is ROUTED AROUND.

   THE ONE NEW SIDE CONDITION, stated here and not smoothed over:
   [Set < carrier].  [Set+1] is the sort of [Prop], and identifying the
   index universe with the ring's carrier universe therefore forces the
   carrier strictly above [Set].  The conditional [tensor_via_AFT_of_esols]
   below carries [Set < u0] and [Set < u11]; it does NOT carry [Set < u2],
   the ring's carrier slot, and the unconditional form does.  In practice
   it costs nothing -- Lib.v:17's [Unset Universe Minimization ToSet] keeps
   carrier universes off [Set] -- but it is a real side condition, and it is
   pinned as a probe in Test/ProbeModTensorAFT449.v beside the positive
   control of its [Section SetPin].

   [obj[RMod R]], NOT [RModObject R], in the section context: the quotient
   must land at the SAME [RMod] universe instance as the ambient modules or
   the two elaborations of [QMod] in [esol_obj] and [esol_elem] disagree. *)

Section CongruenceIndex.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

(* A [Prop]-valued congruence on the term module.  [cg_gen] says the
   congruence contains the term model's own relation, so a quotient by it
   is a quotient OF the term model; the remaining four clauses say the
   module operations descend. *)
Record IsCongruence (Rq : MTerm V V' → MTerm V V' → Prop) : Prop := {
  cg_refl  : ∀ s, Rq s s;
  cg_sym   : ∀ s t, Rq s t → Rq t s;
  cg_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  cg_gen   : ∀ s t, mt_eq s t → Rq s t;
  cg_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (mt_plus s t) (mt_plus s' t');
  cg_neg   : ∀ s s', Rq s s' → Rq (mt_neg s) (mt_neg s');
  cg_smul  : ∀ (r : carrier (rig_setoid (ring_rig R))) s s',
               Rq s s' → Rq (mt_smul r s) (mt_smul r s')
}.

Definition CongIdx : Type :=
  { Rq : MTerm V V' → MTerm V V' → Prop & IsCongruence Rq }.

End CongruenceIndex.

Arguments IsCongruence {R} V V' Rq.
Arguments CongIdx {R} V V'.

Section QuotientModule.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).

Lemma QMod_smul_respects (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) :
  Proper (equiv ==> Rq ==> Rq) (@mt_smul R V V').
Proof.
  intros r r' Hr s s' Hs.
  refine (cg_trans _ _ Rq HRq _ (@mt_smul R V V' r s') _ _ _).
  - exact (cg_smul _ _ Rq HRq r _ _ Hs).
  - exact (cg_gen _ _ Rq HRq _ _ (mte_smul Hr (mt_refl s'))).
Qed.

(* THE QUOTIENT SETOID IS NAMED, and that is load-bearing.  Written inline,
   [PropEquiv_of_relation]'s setoid argument is found by resolution, which
   picks the AMBIENT [mt_Setoid] rather than the quotient's, and both
   implications are then refused ("The term "h" has type "Rq f f0" while it
   is expected to have type "f ≈ f0"").  Instance/Mod/Tensor.v:502 gives
   [mt_Setoid] by name for the same reason. *)
Definition QMod_Setoid (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : Setoid (MTerm V V') :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := cg_refl  _ _ Rq HRq
        ; Equivalence_Symmetric  := cg_sym   _ _ Rq HRq
        ; Equivalence_Transitive := cg_trans _ _ Rq HRq |} |}.

(* The quotient module: the term module's carrier and operations with the
   congruence as its `≈`.  Every law is the term model's own law passed
   through [cg_gen], and [cmon_prop] is the congruence being its own [Prop]
   mirror -- the quotient's `≈` IS a [Prop] relation by construction. *)
Definition QMod (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : obj[RMod R] :=
  {| rm_ab := {|
       ab_cmon := {|
         cmon_setoid :=
           {| carrier := MTerm V V'
            ; is_setoid := QMod_Setoid Rq HRq |};
         cmon_zero := @mt_zero R V V';
         cmon_plus := @mt_plus R V V';
         cmon_plus_respects := fun _ _ Hs _ _ Ht => cg_plus _ _ Rq HRq _ _ _ _ Hs Ht;
         cmon_plus_assoc := fun s t u => cg_gen _ _ Rq HRq _ _ (mte_assoc s t u);
         cmon_plus_comm  := fun s t => cg_gen _ _ Rq HRq _ _ (mte_comm s t);
         cmon_plus_zero_l := fun s => cg_gen _ _ Rq HRq _ _ (mte_zero_l s);
         cmon_prop := @PropEquiv_of_relation _ (QMod_Setoid Rq HRq) Rq
                        (fun _ _ h => h) (fun _ _ h => h)
       |};
       ab_neg := @mt_neg R V V';
       ab_neg_respects := fun _ _ Hs => cg_neg _ _ Rq HRq _ _ Hs;
       ab_neg_left := fun s => cg_gen _ _ Rq HRq _ _ (mte_neg_l s)
     |};
     rm_smul := @mt_smul R V V';
     rm_smul_respects := QMod_smul_respects Rq HRq;
     rm_smul_distr_l := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_distr_l r s t);
     rm_smul_distr_r := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_distr_r r s t);
     rm_smul_assoc := fun r s t => cg_gen _ _ Rq HRq _ _ (mte_smul_assoc r s t);
     rm_smul_one := fun s => cg_gen _ _ Rq HRq _ _ (mte_smul_one s)
  |}.

(* The canonical bilinear map into the quotient is the generator former. *)
Definition QMod_gen (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : RBilinear V V' (QMod Rq HRq) :=
  @Build_RBilinear R V V' (QMod Rq HRq) (@mt_gen R V V')
    (fun _ _ Hv _ _ Hw => cg_gen _ _ Rq HRq _ _ (mte_gen Hv Hw))
    (fun v v' w => cg_gen _ _ Rq HRq _ _ (mte_add_l v v' w))
    (fun v w w' => cg_gen _ _ Rq HRq _ _ (mte_add_r v w w'))
    (fun r v w => cg_gen _ _ Rq HRq _ _ (mte_sym (mte_act_l r v w)))
    (fun r v w => cg_gen _ _ Rq HRq _ _ (mte_sym (mte_act_r r v w))).

(* THE ELEMENTARY TENSORS SPAN EVERY QUOTIENT.  This is Instance/Mod/
   Spanning.v:775's [tensor_gen_spanning] verbatim, five cases with
   [mt_neg] discharged by [smod_neg]: the carrier is the same [MTerm] and
   [rbl_map (QMod_gen …)] is [mt_gen], so nothing about the congruence
   enters the induction.  Section 10 consumes it. *)
Theorem QMod_gen_spanning (Rq : MTerm V V' → MTerm V V' → Prop)
  (HRq : IsCongruence V V' Rq) : RBilinearSpanning (QMod_gen Rq HRq).
Proof.
  intro t; induction t.
  - refine (mgen_base (rbl_image (QMod_gen Rq HRq)) _ _).
    exists c, c0; reflexivity.
  - exact (mgen_zero (rbl_image (QMod_gen Rq HRq))).
  - exact (mgen_plus (rbl_image (QMod_gen Rq HRq)) _ _ IHt1 IHt2).
  - exact (smod_neg (SubGenMod (rbl_image (QMod_gen Rq HRq))) _ IHt).
  - exact (mgen_smul (rbl_image (QMod_gen Rq HRq)) _ _ IHt).
Defined.

End QuotientModule.

Arguments QMod {R V V'} Rq HRq.
Arguments QMod_gen {R V V'} Rq HRq.
Arguments QMod_gen_spanning {R V V'} Rq HRq.

(* THE KERNEL CONGRUENCE OF A BILINEAR MAP, AND THE COVERING.

   There is NO [PropEquiv] hypothesis anywhere below, and that single fact
   is what turns the conditional of section 4 into a theorem: since the PR
   "algebraic carriers are sets" (2026-09-17) [cmon_prop] is a FIELD of
   [CMonObject] with [#[export] Existing Instance], so every [RModObject]
   carries the [Prop] mirror of its own `≈`. *)

Section KernelCongruence.

Context {R : RingObject}.
Context (V V' : obj[RMod R]).
Context {W : obj[RMod R]}.
Context (beta : RBilinear V V' W).

Definition ker_cong : MTerm V V' → MTerm V V' → Prop :=
  fun x y => @pequiv _ _ (cmon_prop W)
               (tensor_med_fun beta x) (tensor_med_fun beta y).

Lemma ker_cong_is_cong : IsCongruence V V' ker_cong.
Proof.
  unfold ker_cong.
  constructor.
  - intro s; apply (@pequiv_from _ _ (cmon_prop W)); reflexivity.
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop W)); symmetry;
      exact (@pequiv_to _ _ (cmon_prop W) _ _ H).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (cmon_prop W)).
    transitivity (tensor_med_fun beta t);
      [ exact (@pequiv_to _ _ (cmon_prop W) _ _ H1)
      | exact (@pequiv_to _ _ (cmon_prop W) _ _ H2) ].
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop W));
      exact (tensor_med_respects beta s t H).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (cmon_plus_respects W _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H1)
                                _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H2)).
  - intros s s' H; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (ab_neg_respects W _ _ (@pequiv_to _ _ (cmon_prop W) _ _ H)).
  - intros r s s' H; apply (@pequiv_from _ _ (cmon_prop W)); simpl.
    exact (rm_smul_respects W _ _ (reflexivity r) _ _
             (@pequiv_to _ _ (cmon_prop W) _ _ H)).
Qed.

Definition ker_idx : CongIdx V V' := existT _ ker_cong ker_cong_is_cong.

(* The mediator out of the quotient.  Respectfulness IS [pequiv_to]; the
   other four obligations are [reflexivity], the mediator being the term
   model's own fold. *)
Program Definition ker_med : QMod ker_cong ker_cong_is_cong ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := tensor_med_fun beta |} |}
|}.
Solve All Obligations with
  (first [ (intros s t H; exact (@pequiv_to _ _ (cmon_prop W) _ _ H))
         | (intros; simpl; reflexivity) ]).

(* The covering equation, on the nose. *)
Example ker_factors (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom ker_med)
    (rbl_map (QMod_gen ker_cong ker_cong_is_cong) v w)
  = rbl_map beta v w
  := eq_refl.

(* THE MEDIATOR IS INJECTIVE BY CONSTRUCTION: the congruence IS the kernel
   pair of the evaluation, so injectivity is [pequiv_from] and nothing
   else. *)
Lemma ker_med_injective : RModInjective ker_med.
Proof.
  intros x y H; exact (@pequiv_from _ _ (cmon_prop W) _ _ H).
Qed.

(* AND SURJECTIVE WHEN [beta] SPANS: the generation derivation is READ as a
   term of the term module, one case per constructor of [MGen]. *)
Definition mgen_preimage (a : carrier (cmon_setoid W))
  (D : MGen (rbl_image beta) a)
  : { t : MTerm V V' & tensor_med_fun beta t ≈ a }.
Proof.
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|r a D IH].
  - exact (existT _ (@mt_gen R V V' (`1 Ha) (`1 (`2 Ha))) (`2 (`2 Ha))).
  - exact (existT _ (`1 IH) (transitivity (`2 IH) Hab)).
  - refine (existT _ (@mt_zero R V V') _); simpl; reflexivity.
  - exact (existT _ (@mt_plus R V V' (`1 IH1) (`1 IH2))
             (cmon_plus_respects W _ _ (`2 IH1) _ _ (`2 IH2))).
  - exact (existT _ (@mt_smul R V V' r (`1 IH))
             (rm_smul_respects W _ _ (reflexivity r) _ _ (`2 IH))).
Defined.

Lemma ker_med_surjective (Hsp : RBilinearSpanning beta) :
  RModSurjective ker_med.
Proof.
  intro b; exact (mgen_preimage b (Hsp b)).
Defined.

(* ...and therefore an ISOMORPHISM of [RMod R], through
   Instance/Mod/Spanning.v:650's [rmod_split].  This is the content of Mac
   Lane's Lemma 2 at [RMod R]: every spanning codomain is (isomorphic to) a
   quotient of ONE fixed object, the term module. *)
Definition ker_iso (Hsp : RBilinearSpanning beta) :
  QMod ker_cong ker_cong_is_cong ≅ W.
Proof.
  unshelve refine {| to := ker_med
                   ; from := rmod_split ker_med ker_med_injective
                               (ker_med_surjective Hsp) |}.
  - exact (rmod_split_commutes ker_med ker_med_injective
             (ker_med_surjective Hsp)).
  - intro t; simpl.
    apply ker_med_injective.
    exact (`2 (ker_med_surjective Hsp (tensor_med_fun beta t))).
Defined.

End KernelCongruence.

Arguments ker_cong {R V V' W} beta.
Arguments ker_cong_is_cong {R V V' W} beta.
Arguments ker_idx {R V V' W} beta.
Arguments ker_med {R V V' W} beta.
Arguments ker_iso {R V V' W} beta Hsp.

(* THE OBJECT AND ELEMENT PARTS ARE NAMED, and that too is load-bearing.
   Written inline, [esol_obj] and [esol_elem] each mint their OWN universe
   instance of [QMod] and the record is refused, "RBilinear … (QMod@{a…} …)"
   against "carrier (fobj[?K] (QMod@{b…} …))".  Naming them forces one. *)
Definition QModOf {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : obj[RMod R] := QMod (`1 i) (`2 i).

Definition QModGenOf {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : RBilinear V V' (QModOf i) := QMod_gen (`1 i) (`2 i).

(* THE SOLUTION SET, AT THE CARRIER UNIVERSE.  The [{| … |}] form leaves the
   functor [?K] open and is refused even with the two parts named; the
   explicit [@Build_ElementSolutionSet (RMod R) (Bilin V V')] is required. *)
Definition tensor_esols_prop {R : RingObject} (V V' : obj[RMod R]) :
  ElementSolutionSet (Bilin V V').
Proof.
  unshelve refine (@Build_ElementSolutionSet (RMod R) (Bilin V V')
                     (CongIdx V V') QModOf QModGenOf _).
  intros c beta.
  exists (ker_idx beta), (ker_med beta).
  intros v w; simpl; reflexivity.
Defined.

(** ** 4. Mac Lane's Construction 1: the tensor product from the AFT *)

(* Stated at TOP LEVEL, outside any [Section], for the reason
   Adjunction/Representability/Sets.v:301-305 gives: the comma-initial step
   pins the hom AND proof universes of both categories to [Set], and inside
   a section that has already elaborated a category with those levels apart
   the ascription is refused.  The pin is measured in the header.

   ALL THREE of Mac Lane's premises are now discharged here outright --
   [RMod_Complete] ("K-Mod is small-complete"), [Bilin_PreservesImageLimit]
   ("Bilin(A,B;-) is continuous") and [tensor_esols_prop] of section 3A (the
   solution set).  CORRECTION, PR "algebraic carriers are sets"
   (2026-09-17): until this commit the third stayed a hypothesis and this
   comment said so.  [tensor_esols_direct] -- Mac Lane's OWN family, indexed
   by a sigma over the objects of [RMod R] -- is still refused by the
   theorem, and that refusal is NEGATIVE 1 of the probe and is unchanged;
   what changed is that a DIFFERENT solution set for the same functor, at
   the carrier universe, is now in tree.  Section 10 closes the circle by
   proving Mac Lane's own family small up to isomorphism and feeding the
   resizing.

   THE CONDITIONAL IS NOT LOST.  [tensor_via_AFT_of_esols] is the old
   [tensor_via_AFT], statement for statement; the unconditional
   [tensor_via_AFT] is that constant at [tensor_esols_prop]. *)

Definition tensor_via_AFT_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) : Representable (Bilin V V') :=
  representability_theorem (Bilin V V') (RMod_Complete R)
    (Bilin_PreservesImageLimit V V') E.

(* THE HEADLINE, at an ARBITRARY ring, with no hypothesis and no [Set]. *)
Definition tensor_via_AFT {R : RingObject} (V V' : obj[RMod R]) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_prop V V').

(* THE CIRCULAR DISCHARGE, KEPT FOR COMPARISON; A REMOVAL CANDIDATE FOR
   JOHN.  A solution set at the universe the theorem demands, obtained from
   the tensor product the theorem is meant to construct.  CIRCULAR, and
   named so that the circularity is visible at every use site -- exactly
   Instance/Grp/FreeAFT.v's [Grp_Forget_solution_set_from_adjunction], which
   existed for the same reason and is disclosed the same way.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): its stated
   role was "to show the conditional above is not vacuous", and that role is
   GONE -- [tensor_esols_prop] discharges the hypothesis non-circularly.  It
   is kept, not deleted, because NEGATIVE 6 of
   Test/ProbeModTensorAFT449.v and [tensor_via_AFT_from_tensor] are
   statements ABOUT it, and because removing working code is John's call and
   not this commit's.  What it now is, is the comparison: the two solution
   sets are different terms for the same functor, and the probe pins that. *)
Definition tensor_esols_from_tensor {R : RingObject} (V V' : RModObject R) :
  ElementSolutionSet (Bilin V V').
Proof.
  unshelve refine (@Build_ElementSolutionSet (RMod R) (Bilin V V')
                     unit (fun _ => TensorMod V V')
                     (fun _ => @tensor_gen R V V') _).
  intros c β.
  refine (existT _ tt _).
  refine (existT _ (tensor_factor β) _).
  intros v w; exact (tensor_factor_commutes β v w).
Defined.

Definition tensor_via_AFT_from_tensor {R : RingObject} (V V' : RModObject R) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_from_tensor V V').

(** ** 5. The comparison with [TensorMod] *)

Definition tensor_repr_of_UE {R : RingObject} (V V' : RModObject R) :
  Representable (Bilin V V') :=
  Representable_of_UniversalElement (tensor_UniversalElement V V').

Example tensor_repr_of_UE_obj {R : RingObject} (V V' : RModObject R) :
  @repr_obj (RMod R) (Bilin V V') (tensor_repr_of_UE V V') = TensorMod V V'
  := eq_refl.

(* The object comparison is `≅`, NOT [eq_refl]: the AFT builds its object
   as a limit inside the comma category, [TensorMod] is a quotient of
   formal terms.  The statement holds for EVERY solution set, so nothing
   here depends on which one is supplied -- which is why the conditional
   form is kept beside the unconditional one rather than replaced by it. *)
Definition tensor_AFT_iso_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT_of_esols V V' E)
    ≅ TensorMod V V' :=
  repr_unique_iso (tensor_repr_of_UE V V')
    (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_iso {R : RingObject} (V V' : obj[RMod R]) :
  @repr_obj (RMod R) (Bilin V V') (tensor_via_AFT V V')
    ≅ TensorMod V V' :=
  tensor_AFT_iso_of_esols V V' (tensor_esols_prop V V').

Definition tensor_AFT_iso_universal_of_esols {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :=
  repr_unique_iso_universal (tensor_repr_of_UE V V')
    (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_iso_universal {R : RingObject} (V V' : obj[RMod R]) :=
  tensor_AFT_iso_universal_of_esols V V' (tensor_esols_prop V V').

Definition tensor_AFT_ue_of_esols {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) : UniversalElement (Bilin V V') :=
  UniversalElement_of_Representable (tensor_via_AFT_of_esols V V' E).

Definition tensor_AFT_ue {R : RingObject} (V V' : obj[RMod R]) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue_of_esols V V' (tensor_esols_prop V V').

(* The issue's verification name.  [module_tensor_universal V V'] is the
   universal element the adjoint functor theorem produces -- an alias of
   [tensor_AFT_ue], so that the name the issue asks to audit resolves to
   the delivered constant.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): this comment
   read "it inherits the conditional shape and the [Set] pin of
   [tensor_via_AFT]".  Both clauses are now false of the name as it stands.
   The conditional shape is [module_tensor_universal_of_esols], which is the
   old constant statement for statement; the [Set] pin went with the
   annotation of [DiscreteCat_Functor] in the same PR.  What the
   unconditional form DOES carry is the new [Set < carrier] side condition
   of section 3A. *)
Definition module_tensor_universal_of_esols {R : RingObject}
  (V V' : RModObject R) (E : ElementSolutionSet (Bilin V V')) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue_of_esols V V' E.

Definition module_tensor_universal {R : RingObject} (V V' : obj[RMod R]) :
  UniversalElement (Bilin V V') :=
  tensor_AFT_ue V V'.

Definition tensor_AFT_elem_iso {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  @ue_obj (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E) ≅ TensorMod V V' :=
  universal_element_iso
    (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
    (tensor_universal_element V V').

Theorem tensor_AFT_elem_commutes {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  fmap[Bilin V V'] (to (tensor_AFT_elem_iso V V' E))
    (@ue_elem (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E))
    ≈ @tensor_gen R V V'.
Proof.
  exact (ue_med_commutes
           (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
           (tensor_universal_element V V')).
Qed.

Definition tensor_AFT_elem_unique {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :=
  universal_element_unique
    (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
    (tensor_universal_element V V').

(* The two comparisons agree, and the AFT's universal bilinear map carried
   along the REPRESENTATION-level isomorphism is [tensor_gen] itself.  The
   argument is naturality of the representation followed by
   [repr_induced_compatible] at the identity; nothing about the solution set
   enters. *)
Theorem tensor_AFT_iso_carries_elem {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  fmap[Bilin V V'] (to (tensor_AFT_iso_of_esols V V' E))
    (@ue_elem (RMod R) (Bilin V V') (tensor_AFT_ue_of_esols V V' E))
    ≈ @tensor_gen R V V'.
Proof.
  pose proof (repr_compatible_at
    (repr_induced_compatible (tensor_repr_of_UE V V')
       (tensor_via_AFT_of_esols V V' E) nat_id) (TensorMod V V') id) as HC.
  pose proof (@naturality _ _ _ _
      (to (@represented _ _ (tensor_via_AFT_of_esols V V' E)))
      (@repr_obj _ _ (tensor_via_AFT_of_esols V V' E)) (TensorMod V V')
      (to (tensor_AFT_iso_of_esols V V' E)) (@id (RMod R) _)) as HN.
  transitivity (transform[to (@represented _ _ (tensor_via_AFT_of_esols V V' E))]
                  (TensorMod V V')
                  (@compose (RMod R) _ _ _ (to (tensor_AFT_iso_of_esols V V' E))
                     (@id (RMod R) _))).
  - exact HN.
  - transitivity (transform[to (@represented _ _ (tensor_via_AFT_of_esols V V' E))]
                    (TensorMod V V')
                    (@compose (RMod R) _ _ _ (@id (RMod R) _)
                       (to (tensor_AFT_iso_of_esols V V' E)))).
    + apply proper_morphism.
      rewrite id_left, id_right; reflexivity.
    + rewrite HC.
      exact (@fmap_id _ _ (Bilin V V') (TensorMod V V') (@tensor_gen R V V')).
Qed.

Theorem tensor_AFT_isos_agree {R : RingObject} (V V' : RModObject R)
  (E : ElementSolutionSet (Bilin V V')) :
  tensor_AFT_elem_iso V V' E ≈ tensor_AFT_iso_of_esols V V' E.
Proof.
  exact (universal_element_iso_unique
           (AUniversalElement_of_UniversalElement (tensor_AFT_ue_of_esols V V' E))
           (tensor_universal_element V V')
           (tensor_AFT_iso_of_esols V V' E)
           (tensor_AFT_iso_carries_elem V V' E)).
Qed.

(** ** 6. Exercise 3: the balanced-biadditive functor [Ab ⟶ Sets] *)

Section BalBiaddFunctor.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Program Definition BalBiadditive_Setoid (A : AbObject) :
  Setoid (BalBiadditive N M A) := {|
  equiv := fun β γ => ∀ n m, bal_map β n m ≈ bal_map γ n m
|}.
Next Obligation.
  intros A.
  constructor.
  - intros β n m; reflexivity.
  - intros β γ Hβγ n m; symmetry; apply Hβγ.
  - intros β γ δ H1 H2 n m.
    transitivity (bal_map γ n m); [ apply H1 | apply H2 ].
Qed.

Definition BalBiadd_obj (A : AbObject) : SetoidObject := {|
  carrier   := BalBiadditive N M A;
  is_setoid := BalBiadditive_Setoid A
|}.

Program Definition BalBiadd_post {A B : AbObject} (f : A ~{Ab}~> B)
  (β : BalBiadditive N M A) : BalBiadditive N M B := {|
  bal_map := fun n m => cmon_map f (bal_map β n m)
|}.
Next Obligation.
  intros A B f β n n' Hn m m' Hm; simpl.
  exact (proper_morphism (cmon_map f) _ _ (bal_respects β _ _ Hn _ _ Hm)).
Qed.
Next Obligation.
  intros A B f β n n' m; simpl.
  rewrite (bal_add_l β n n' m).
  apply (cmon_map_plus f).
Qed.
Next Obligation.
  intros A B f β n m m'; simpl.
  rewrite (bal_add_r β n m m').
  apply (cmon_map_plus f).
Qed.
Next Obligation.
  intros A B f β x n m; simpl.
  now rewrite (bal_balance β x n m).
Qed.

Program Definition BalBiadd : Ab ⟶ Sets := {|
  fobj := BalBiadd_obj;
  fmap := fun A B f => {| morphism := BalBiadd_post f |}
|}.
Next Obligation.
  intros A B f β γ Hβγ n m; simpl.
  exact (proper_morphism (cmon_map f) _ _ (Hβγ n m)).
Qed.
Next Obligation.
  intros A B f g Hfg β n m; simpl.
  exact (Hfg (bal_map β n m)).
Qed.
Next Obligation. intros A β n m; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g β n m; simpl; reflexivity. Qed.

(* The universal element the explicit construction already supplies, in the
   form the comparison below consumes. *)
Program Definition bal_universal_element :
  AUniversalElement BalBiadd (BalTensor N M) := {|
  aue_elem      := @bal_gen X N M;
  aue_universal := fun A β => {| unique_obj := bal_med β |}
|}.
Next Obligation. intros A β n m; simpl; reflexivity. Qed.
Next Obligation.
  intros A β k Hk.
  symmetry.
  exact (bal_med_unique β k Hk).
Qed.

Definition bal_UniversalElement : UniversalElement BalBiadd :=
  UniversalElement_of_AUniversalElement bal_universal_element.

Example bal_UniversalElement_obj :
  @ue_obj Ab BalBiadd bal_UniversalElement = BalTensor N M := eq_refl.

Example bal_UniversalElement_elem :
  @ue_elem Ab BalBiadd bal_UniversalElement = @bal_gen X N M := eq_refl.

End BalBiaddFunctor.

Arguments BalBiadditive_Setoid {X} N M A.
Arguments BalBiadd_obj {X} N M A.
Arguments BalBiadd_post {X} N M {A B} f β.
Arguments BalBiadd {X} N M.
Arguments bal_universal_element {X} N M.
Arguments bal_UniversalElement {X} N M.

(** ** 7. Exercise 3: [BalBiadd N M] is continuous *)

Section BalContinuity.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Section AtALimitingCone.

Context {J : Category}.
Context {K : J ⟶ Ab}.
Context {L : Cone K}.
Context (HL : IsLimitCone L).

Definition bal_sets_limit : IsLimitCone (FCone Ab_Forget L) :=
  Ab_Forget_creates_continuous J K L HL.

Lemma bal_lim_ext (u v : carrier (cmon_setoid vertex_obj[L]))
  (H : ∀ x : J, cmon_map (cone_leg L x) u ≈ cmon_map (cone_leg L x) v) :
  u ≈ v.
Proof using All. exact (slim_ext bal_sets_limit u v H). Qed.

Section AtACone.

Context (Q : Cone (BalBiadd N M ◯ K)).

Lemma bal_family_compat (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N))) (m : carrier (cmon_setoid (rm_ab M)))
  (x y : J) (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f (bal_map (cone_leg Q x q) n m)
    ≈ bal_map (cone_leg Q y q) n m.
Proof using All.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ Q) x y f q n m).
Qed.

Definition bal_med_elem (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  carrier (cmon_setoid vertex_obj[L]) :=
  slim_elem bal_sets_limit (fun x => bal_map (cone_leg Q x q) n m)
    (fun x y f => bal_family_compat q n m x y f).

Lemma bal_med_elem_leg (q : carrier (vertex_obj[Q]))
  (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) (x : J) :
  cmon_map (cone_leg L x) (bal_med_elem q n m)
    ≈ bal_map (cone_leg Q x q) n m.
Proof using All.
  exact (slim_elem_leg bal_sets_limit
           (fun x => bal_map (cone_leg Q x q) n m)
           (fun x y f => bal_family_compat q n m x y f) x).
Qed.

Program Definition BalBiadd_med (q : carrier (vertex_obj[Q])) :
  BalBiadditive N M vertex_obj[L] := {|
  bal_map := bal_med_elem q
|}.
Next Obligation.
  intros q n n' Hn m m' Hm.
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  exact (bal_respects (cone_leg Q x q) _ _ Hn _ _ Hm).
Qed.
Next Obligation.
  intros q n n' m.
  apply bal_lim_ext; intro x.
  rewrite bal_med_elem_leg.
  rewrite (cmon_map_plus (cone_leg L x)).
  rewrite !bal_med_elem_leg.
  apply bal_add_l.
Qed.
Next Obligation.
  intros q n m m'.
  apply bal_lim_ext; intro x.
  rewrite bal_med_elem_leg.
  rewrite (cmon_map_plus (cone_leg L x)).
  rewrite !bal_med_elem_leg.
  apply bal_add_r.
Qed.
Next Obligation.
  intros q r n m.
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  apply bal_balance.
Qed.

Program Definition BalBiadd_cone_med :
  vertex_obj[Q] ~{Sets}~> vertex_obj[FCone (BalBiadd N M) L] :=
  {| morphism := BalBiadd_med |}.
Next Obligation.
  intros q q' Hq n m.
  change (bal_med_elem q n m ≈ bal_med_elem q' n m).
  apply bal_lim_ext; intro x.
  rewrite !bal_med_elem_leg.
  exact (proper_morphism (cone_leg Q x) q q' Hq n m).
Qed.

End AtACone.

Theorem BalBiadd_preserves_cone : IsLimitCone (FCone (BalBiadd N M) L).
Proof using All.
  intro Q.
  unshelve refine {| unique_obj := BalBiadd_cone_med Q |}.
  - intros x q n m.
    exact (bal_med_elem_leg Q q n m x).
  - intros u Hu q n m.
    apply bal_lim_ext; intro x.
    rewrite (bal_med_elem_leg Q q n m x).
    symmetry; exact (Hu x q n m).
Qed.

End AtALimitingCone.

Definition BalBiadd_continuous : ContinuousFunctor (BalBiadd N M) :=
  fun J K L HL => BalBiadd_preserves_cone HL.

Definition BalBiadd_PreservesImageLimit :
  @PreservesImageLimit Ab Sets (BalBiadd N M) :=
  Continuous_PreservesImageLimit BalBiadd_continuous.

End BalContinuity.

(** ** 7A. Exercise 3's congruence index: [Prop] congruences on [bsum] *)

(* Section 3A over [Ab], one clause shorter: the balanced tensor is an
   abelian group, not a module, so there is no scalar congruence clause.
   Everything else transposes: the term type is Instance/Mod/Bimodule.v's
   [bsum] (whose relation [bs_eq] is already a [Prop] inductive), the
   quotient is an [AbObject] with the congruence as its `≈` and its own
   [Prop] mirror as [cmon_prop], and the covering is the kernel congruence
   of [bal_med_fun].

   WHAT DOES NOT TRANSPOSE, and is stated here rather than discovered
   later: section 10's Lemma-2 theorem is about [RMod R] only.  The [Ab]
   spanning vocabulary of section 9 ([ABGenSub], [AbImageSub], [ab_split],
   [abg_subobj]) has no counterpart of [mgen_preimage], so nothing below
   claims [bal_esols_direct] is small up to isomorphism.  Exercise 3 gets
   the unconditional representation and NOT the book-faithful second
   route. *)

Section BalCongruenceIndex.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Record IsBalCongruence (Rq : bsum N M → bsum N M → Prop) : Prop := {
  bc_refl  : ∀ s, Rq s s;
  bc_sym   : ∀ s t, Rq s t → Rq t s;
  bc_trans : ∀ s t u, Rq s t → Rq t u → Rq s u;
  bc_gen   : ∀ s t, bs_eq s t → Rq s t;
  bc_plus  : ∀ s s' t t', Rq s s' → Rq t t' →
               Rq (bs_plus s t) (bs_plus s' t');
  bc_neg   : ∀ s s', Rq s s' → Rq (bs_neg s) (bs_neg s')
}.

Definition BalCongIdx : Type :=
  { Rq : bsum N M → bsum N M → Prop & IsBalCongruence Rq }.

End BalCongruenceIndex.

Arguments IsBalCongruence {X} N M Rq.
Arguments BalCongIdx {X} N M.

Section BalQuotient.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

(* NAMED, for the reason section 3A's [QMod_Setoid] is named. *)
Definition QBal_Setoid (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : Setoid (bsum N M) :=
  {| equiv := Rq
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := bc_refl  _ _ Rq H
        ; Equivalence_Symmetric  := bc_sym   _ _ Rq H
        ; Equivalence_Transitive := bc_trans _ _ Rq H |} |}.

Definition QBal (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : obj[Ab] :=
  {| ab_cmon := {|
       cmon_setoid :=
         {| carrier := bsum N M ; is_setoid := QBal_Setoid Rq H |};
       cmon_zero := @bs_zero X N M;
       cmon_plus := @bs_plus X N M;
       cmon_plus_respects := fun _ _ Hs _ _ Ht => bc_plus _ _ Rq H _ _ _ _ Hs Ht;
       cmon_plus_assoc := fun s t u => bc_gen _ _ Rq H _ _ (be_assoc s t u);
       cmon_plus_comm  := fun s t => bc_gen _ _ Rq H _ _ (be_comm s t);
       cmon_plus_zero_l := fun s => bc_gen _ _ Rq H _ _ (be_zero_l s);
       cmon_prop := @PropEquiv_of_relation _ (QBal_Setoid Rq H) Rq
                      (fun _ _ h => h) (fun _ _ h => h)
     |};
     ab_neg := @bs_neg X N M;
     ab_neg_respects := fun _ _ Hs => bc_neg _ _ Rq H _ _ Hs;
     ab_neg_left := fun s => bc_gen _ _ Rq H _ _ (be_neg_l s)
  |}.

(* The canonical balanced map into the quotient is the generator former. *)
Definition QBal_gen (Rq : bsum N M → bsum N M → Prop)
  (H : IsBalCongruence N M Rq) : BalBiadditive N M (QBal Rq H) :=
  @Build_BalBiadditive X N M (QBal Rq H) (@bs_gen X N M)
    (fun _ _ Hn _ _ Hm => bc_gen _ _ Rq H _ _ (be_gen Hn Hm))
    (fun n n' m => bc_gen _ _ Rq H _ _ (be_add_l n n' m))
    (fun n m m' => bc_gen _ _ Rq H _ _ (be_add_r n m m'))
    (fun x n m => bc_gen _ _ Rq H _ _ (be_balance x n m)).

End BalQuotient.

Arguments QBal_Setoid {X N M} Rq H.
Arguments QBal {X N M} Rq H.
Arguments QBal_gen {X N M} Rq H.

Section BalKernelCongruence.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).
Context {A : AbObject}.
Context (beta : BalBiadditive N M A).

(* NO [PropEquiv] hypothesis: [cmon_prop] is a field of [CMonObject] and
   [AbObject] is a record over one. *)
Definition bal_ker_cong : bsum N M → bsum N M → Prop :=
  fun s t => @pequiv _ _ (cmon_prop A)
               (bal_med_fun beta s) (bal_med_fun beta t).

Lemma bal_ker_is_cong : IsBalCongruence N M bal_ker_cong.
Proof.
  unfold bal_ker_cong.
  constructor.
  - intro s; apply (@pequiv_from _ _ (cmon_prop A)); reflexivity.
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop A)); symmetry;
      exact (@pequiv_to _ _ (cmon_prop A) _ _ H).
  - intros s t u H1 H2; apply (@pequiv_from _ _ (cmon_prop A)).
    transitivity (bal_med_fun beta t);
      [ exact (@pequiv_to _ _ (cmon_prop A) _ _ H1)
      | exact (@pequiv_to _ _ (cmon_prop A) _ _ H2) ].
  - intros s t H; apply (@pequiv_from _ _ (cmon_prop A));
      exact (bal_med_respects N M beta s t H).
  - intros s s' t t' H1 H2; apply (@pequiv_from _ _ (cmon_prop A)); simpl.
    exact (cmon_plus_respects A _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H1)
                                _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H2)).
  - intros s s' H; apply (@pequiv_from _ _ (cmon_prop A)); simpl.
    exact (ab_neg_respects A _ _ (@pequiv_to _ _ (cmon_prop A) _ _ H)).
Qed.

Definition bal_ker_idx : BalCongIdx N M :=
  existT _ bal_ker_cong bal_ker_is_cong.

(* The mediator out of the quotient.  Respectfulness IS [pequiv_to]; the
   two monoid laws are [reflexivity], the mediator being [bal_med_fun]. *)
Program Definition bal_ker_med :
  QBal bal_ker_cong bal_ker_is_cong ~{Ab}~> A := {|
  cmon_map := {| morphism := bal_med_fun beta |}
|}.
Solve All Obligations with
  (first [ (intros s t H; exact (@pequiv_to _ _ (cmon_prop A) _ _ H))
         | (intros; simpl; reflexivity) ]).

(* The covering equation, on the nose. *)
Example bal_ker_factors (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map bal_ker_med (bal_map (QBal_gen bal_ker_cong bal_ker_is_cong) n m)
  = bal_map beta n m
  := eq_refl.

End BalKernelCongruence.

Arguments bal_ker_cong {X N M A} beta.
Arguments bal_ker_is_cong {X N M A} beta.
Arguments bal_ker_idx {X N M A} beta.
Arguments bal_ker_med {X N M A} beta.

(* NAMED, so that the two record fields elaborate [QBal] at ONE universe
   instance -- section 3A's [QModOf] trap, at [Ab]. *)
Definition QBalOf {X : RingObject} {N : RModObject (Ring_op X)}
  {M : RModObject X} (i : BalCongIdx N M) : obj[Ab] := QBal (`1 i) (`2 i).

Definition QBalGenOf {X : RingObject} {N : RModObject (Ring_op X)}
  {M : RModObject X} (i : BalCongIdx N M) : BalBiadditive N M (QBalOf i) :=
  QBal_gen (`1 i) (`2 i).

Definition bal_esols_prop {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     (BalCongIdx N M) QBalOf QBalGenOf _).
  intros A beta.
  exists (bal_ker_idx beta), (bal_ker_med beta).
  intros n m; simpl; reflexivity.
Defined.

(** ** 8. Exercise 3: the balanced tensor from the AFT, and the comparison *)

(* Top level again, for the same [Set] pin.

   CORRECTION, PR "algebraic carriers are sets" (2026-09-17): the
   conditional is now named [bal_tensor_via_AFT_of_esols] and
   [bal_tensor_via_AFT] is unconditional, at [bal_esols_prop] of section
   7A.  No statement was weakened: the conditional is the old constant
   statement for statement. *)

Definition bal_tensor_via_AFT_of_esols {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X)
  (E : ElementSolutionSet (BalBiadd N M)) :
  Representable (BalBiadd N M) :=
  representability_theorem (BalBiadd N M) Ab_Complete
    (BalBiadd_PreservesImageLimit N M) E.

Definition bal_tensor_via_AFT {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_prop N M).

(* THE CIRCULAR DISCHARGE, KEPT FOR COMPARISON; A REMOVAL CANDIDATE FOR
   JOHN.  Circular as at [RMod R]: a solution set at the universe the
   theorem demands, read off the balanced tensor the theorem is meant to
   build.  CORRECTION, PR "algebraic carriers are sets" (2026-09-17): its
   stated role, "to show the conditional above is not vacuous", is gone --
   [bal_esols_prop] discharges the hypothesis non-circularly.  Kept, not
   deleted, on the same footing as [tensor_esols_from_tensor]. *)
Definition bal_esols_from_tensor {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     unit (fun _ => BalTensor N M)
                     (fun _ => @bal_gen X N M) _).
  intros A β.
  refine (existT _ tt _).
  refine (existT _ (bal_med β) _).
  intros n m; reflexivity.
Defined.

Definition bal_tensor_via_AFT_from_tensor {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :
  Representable (BalBiadd N M) :=
  bal_tensor_via_AFT_of_esols N M (bal_esols_from_tensor N M).

Definition bal_repr_of_UE {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : Representable (BalBiadd N M) :=
  Representable_of_UniversalElement (bal_UniversalElement N M).

Example bal_repr_of_UE_obj {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  @repr_obj Ab (BalBiadd N M) (bal_repr_of_UE N M) = BalTensor N M := eq_refl.

Definition bal_AFT_iso_of_esols {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  @repr_obj Ab (BalBiadd N M) (bal_tensor_via_AFT_of_esols N M E)
    ≅ BalTensor N M :=
  repr_unique_iso (bal_repr_of_UE N M)
    (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_iso {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  @repr_obj Ab (BalBiadd N M) (bal_tensor_via_AFT N M) ≅ BalTensor N M :=
  bal_AFT_iso_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_iso_universal_of_esols {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X)
  (E : ElementSolutionSet (BalBiadd N M)) :=
  repr_unique_iso_universal (bal_repr_of_UE N M)
    (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_iso_universal {X : RingObject}
  (N : RModObject (Ring_op X)) (M : RModObject X) :=
  bal_AFT_iso_universal_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_ue_of_esols {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  UniversalElement (BalBiadd N M) :=
  UniversalElement_of_Representable (bal_tensor_via_AFT_of_esols N M E).

Definition bal_AFT_ue {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : UniversalElement (BalBiadd N M) :=
  bal_AFT_ue_of_esols N M (bal_esols_prop N M).

Definition bal_AFT_elem_iso {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  @ue_obj Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E) ≅ BalTensor N M :=
  universal_element_iso
    (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
    (bal_universal_element N M).

Theorem bal_AFT_elem_commutes {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  fmap[BalBiadd N M] (to (bal_AFT_elem_iso N M E))
    (@ue_elem Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E))
    ≈ @bal_gen X N M.
Proof.
  exact (ue_med_commutes
           (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
           (bal_universal_element N M)).
Qed.

Theorem bal_AFT_iso_carries_elem {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  fmap[BalBiadd N M] (to (bal_AFT_iso_of_esols N M E))
    (@ue_elem Ab (BalBiadd N M) (bal_AFT_ue_of_esols N M E))
    ≈ @bal_gen X N M.
Proof.
  pose proof (repr_compatible_at
    (repr_induced_compatible (bal_repr_of_UE N M)
       (bal_tensor_via_AFT_of_esols N M E) nat_id) (BalTensor N M) id) as HC.
  pose proof (@naturality _ _ _ _
      (to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E)))
      (@repr_obj _ _ (bal_tensor_via_AFT_of_esols N M E)) (BalTensor N M)
      (to (bal_AFT_iso_of_esols N M E)) (@id Ab _)) as HN.
  transitivity (transform[to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E))]
                  (BalTensor N M)
                  (@compose Ab _ _ _ (to (bal_AFT_iso_of_esols N M E)) (@id Ab _))).
  - exact HN.
  - transitivity (transform[to (@represented _ _ (bal_tensor_via_AFT_of_esols N M E))]
                    (BalTensor N M)
                    (@compose Ab _ _ _ (@id Ab _) (to (bal_AFT_iso_of_esols N M E)))).
    + apply proper_morphism.
      rewrite id_left, id_right; reflexivity.
    + rewrite HC.
      exact (@fmap_id _ _ (BalBiadd N M) (BalTensor N M) (@bal_gen X N M)).
Qed.

Theorem bal_AFT_isos_agree {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :
  bal_AFT_elem_iso N M E ≈ bal_AFT_iso_of_esols N M E.
Proof.
  exact (universal_element_iso_unique
           (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
           (bal_universal_element N M)
           (bal_AFT_iso_of_esols N M E)
           (bal_AFT_iso_carries_elem N M E)).
Qed.

Definition bal_AFT_elem_unique {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (E : ElementSolutionSet (BalBiadd N M)) :=
  universal_element_unique
    (AUniversalElement_of_UniversalElement (bal_AFT_ue_of_esols N M E))
    (bal_universal_element N M).

(** ** 9. Exercise 3: Mac Lane's direct solution set over [Ab] *)

Section AbGeneratedSub.

Context {A : AbObject}.
Context (P : carrier (cmon_setoid A) → Type).

(* Instance/Mod/Spanning.v's [ABGen] has exactly the five fields of
   Instance/Ab/DirectedColimit.v:273's [AbSubgroup]; this is the
   repackaging, with no proof obligation. *)
Definition ABGenSub : AbSubgroup A :=
  @Build_AbSubgroup A (ABGen P) (abgen_resp P) (abgen_zero P)
    (abgen_plus P) (abgen_neg P).

End AbGeneratedSub.

(* The image of a homomorphism of abelian groups, as a subgroup -- the [Ab]
   counterpart of Instance/Mod/Quotient.v:761's [ImageSubmod]. *)
Program Definition AbImageSub {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSubgroup B := {|
  absub_mem := fun b => { a : carrier (cmon_setoid A) & cmon_map f a ≈ b }
|}.
Next Obligation.
  intros A B f a b Hab [x Hx].
  exists x; rewrite Hx; exact Hab.
Qed.
Next Obligation.
  intros A B f.
  exists (cmon_zero A); apply cmon_map_zero.
Qed.
Next Obligation.
  intros A B f a b [x Hx] [y Hy].
  exists (cmon_plus A x y).
  rewrite (cmon_map_plus f); now rewrite Hx, Hy.
Qed.
Next Obligation.
  intros A B f a [x Hx].
  exists (ab_neg A x).
  rewrite (ab_map_neg f); now rewrite Hx.
Qed.

(* A bijective homomorphism of abelian groups splits.  The section is not
   canonical -- it picks the preimage the surjectivity datum carries -- and
   each law is injectivity applied to the witness equation. *)
Program Definition ab_split {A B : AbObject} (f : A ~{Ab}~> B)
  (Hi : AbInjective f) (Hs : AbSurjective f) : B ~{Ab}~> A := {|
  cmon_map := {| morphism := fun b => `1 (Hs b) |}
|}.
Next Obligation.
  intros A B f Hi Hs a b Hab.
  apply Hi; rewrite (`2 (Hs a)), (`2 (Hs b)); exact Hab.
Qed.
Next Obligation.
  intros A B f Hi Hs; simpl.
  apply Hi; rewrite (`2 (Hs (cmon_zero B))).
  symmetry; exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros A B f Hi Hs a b; simpl.
  apply Hi.
  rewrite (cmon_map_plus f).
  rewrite (`2 (Hs (cmon_plus B a b))), (`2 (Hs a)), (`2 (Hs b)).
  reflexivity.
Qed.

Lemma ab_split_commutes {A B : AbObject} (f : A ~{Ab}~> B)
  (Hi : AbInjective f) (Hs : AbSurjective f) :
  @compose Ab _ _ _ f (ab_split f Hi Hs) ≈ @id Ab B.
Proof. intro b; exact (`2 (Hs b)). Qed.

(* A subgroup as a subobject of [Ab]: the inclusion is injective on the
   nose, hence monic. *)
Definition abg_subobj {A : AbObject} (S : AbSubgroup A) : @SubObj Ab A :=
  @Build_SubObj Ab A (AbSubgroupAb S) (absub_incl S)
    (ab_injective_monic (absub_incl S) (fun _ _ H => H)).

Section BalSpanningBridge.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).
Context {A : AbObject}.
Context (β : BalBiadditive N M A).

Definition bal_restrict_image (m : @SubObj Ab A)
  (β' : BalBiadditive N M (sub_dom m))
  (Hβ : ∀ n mm, cmon_map (sub_mono m) (bal_map β' n mm) ≈ bal_map β n mm)
  (a : carrier (cmon_setoid A)) (Ha : bal_image N M β a) :
  absub_mem (AbImageSub (sub_mono m)) a.
Proof using All.
  destruct Ha as [n [mm Hnm]].
  exists (bal_map β' n mm).
  rewrite (Hβ n mm); exact Hnm.
Defined.

(* Elementwise spanning implies Mac Lane's categorical form, over [Ab].
   Same argument as Instance/Mod/Spanning.v's
   [rbilinear_spanning_to_spanning], with [ABGen] for [MGen] and
   [AbImageSub] for [ImageSubmod]. *)
Theorem bal_spanning_to_spanning (H : BalSpanning N M β) :
  Spanning (BalBiadd N M) (global_element (X := BalBiadd N M A) β).
Proof using All.
  intros m [k Hk].
  pose (β' := k ttt).
  assert (Hβ : ∀ n mm, cmon_map (sub_mono m) (bal_map β' n mm)
                         ≈ bal_map β n mm) by exact (Hk ttt).
  assert (Hs : AbSurjective (sub_mono m)).
  { intro x.
    exact (abgen_least (bal_image N M β)
             (absub_mem (AbImageSub (sub_mono m)))
             (absub_resp (AbImageSub (sub_mono m)))
             (absub_zero (AbImageSub (sub_mono m)))
             (absub_plus (AbImageSub (sub_mono m)))
             (absub_neg (AbImageSub (sub_mono m)))
             (bal_restrict_image m β' Hβ) x (H x)). }
  assert (Hi : AbInjective (sub_mono m)) by
    exact (ab_monic_injective (sub_mono m) (sub_is_monic m)).
  exists (ab_split (sub_mono m) Hi Hs).
  exact (ab_split_commutes (sub_mono m) Hi Hs).
Defined.

(* The corestriction of β to the subgroup generated by its image. *)
Program Definition bal_gen_corestrict :
  BalBiadditive N M (AbSubgroupAb (ABGenSub (bal_image N M β))) := {|
  bal_map := fun n mm =>
    existT _ (bal_map β n mm)
      (abgen_base (bal_image N M β) (bal_map β n mm)
         (existT _ n (existT _ mm (reflexivity _))))
|}.
Next Obligation.
  intros n n' Hn m m' Hm; simpl.
  exact (bal_respects β _ _ Hn _ _ Hm).
Qed.
Next Obligation. intros n n' m; simpl; apply bal_add_l. Qed.
Next Obligation. intros n m m'; simpl; apply bal_add_r. Qed.
Next Obligation. intros x n m; simpl; apply bal_balance. Qed.

Lemma bal_corestrict_spanning : BalSpanning N M bal_gen_corestrict.
Proof using All.
  intros [a D].
  induction D as [a Ha|a b Hab D IH| |a b D1 IH1 D2 IH2|a D IH].
  - refine (abgen_base (bal_image N M bal_gen_corestrict) _ _).
    destruct Ha as [n [mm Hnm]].
    exists n, mm; exact Hnm.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _ IH).
    exact Hab.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_zero (bal_image N M bal_gen_corestrict))).
    reflexivity.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_plus (bal_image N M bal_gen_corestrict) _ _ IH1 IH2)).
    reflexivity.
  - refine (abgen_resp (bal_image N M bal_gen_corestrict) _ _ _
              (abgen_neg (bal_image N M bal_gen_corestrict) _ IH)).
    reflexivity.
Defined.

End BalSpanningBridge.

Definition bal_esols_direct {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) : ElementSolutionSet (BalBiadd N M).
Proof.
  unshelve refine (@Build_ElementSolutionSet Ab (BalBiadd N M)
                     (SpanningArrowsOutOf (BalBiadd N M) SetsOne)
                     (fun i => `1 i) (fun i => `1 (`2 i) ttt) _).
  intros A β.
  unshelve eexists.
  - refine (existT _ (AbSubgroupAb (ABGenSub (bal_image N M β))) _).
    refine (existT _ (global_element
                        (X := BalBiadd N M
                                (AbSubgroupAb (ABGenSub (bal_image N M β))))
                        (bal_gen_corestrict N M β)) _).
    exact (bal_spanning_to_spanning N M (bal_gen_corestrict N M β)
             (bal_corestrict_spanning N M β)).
  - exists (absub_incl (ABGenSub (bal_image N M β))).
    intros n m; reflexivity.
Defined.

Example bal_esols_direct_index {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) :
  esol_index (bal_esols_direct N M)
    = SpanningArrowsOutOf (BalBiadd N M) SetsOne := eq_refl.

Example bal_esols_direct_obj {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (i : SpanningArrowsOutOf (BalBiadd N M) SetsOne) :
  esol_obj (bal_esols_direct N M) i = `1 i := eq_refl.

Example bal_esols_direct_elem {X : RingObject} (N : RModObject (Ring_op X))
  (M : RModObject X) (i : SpanningArrowsOutOf (BalBiadd N M) SetsOne) :
  esol_elem (bal_esols_direct N M) i = `1 (`2 i) ttt := eq_refl.

(** ** 10. MAC LANE §V.7 LEMMA 2 AS A THEOREM AT [RMod R] *)

(* WHAT THIS SECTION DISCHARGES, AND WHAT IT DOES NOT.

   Mac Lane's Lemma 2 (book p. 128, catalog id `maclane:V.7:lem2`) is the
   step that turns his covering family into a SET: the spanning codomains
   are quotients of one fixed object, so a small family of representatives
   UP TO ISOMORPHISM suffices.  Section 2's [tensor_esols_direct] is the
   covering family and section 3A gives the fixed object -- the term module
   -- together with the quotients.  Putting the two together proves the
   lemma at [RMod R], as [SmallUpToIso] of Adjunction/GAFT/Resize.v, and
   feeding the resizing to [representability_theorem] gives a SECOND,
   book-faithful route to the same representation.

   SCOPE, because "Lemma 2 is discharged" is easy to over-read.  What is
   discharged is the SMALLNESS premise.  It is NOT
   [GAFT_from_spanning]'s hypotheses, which are [HasWidePullbacks A] and
   [PreservesWidePullbacks G]; the first is still universe-refused at
   [RMod R] (Instance/Mod/Spanning.v:149-180), and the widening of
   Adjunction/SpanningArrow.v's [Section GAFTFromSpanning] in this same PR
   does not reach it either (that file's header measures the surviving
   refusal).  [GAFT_from_spanning] is not reachable at [RMod R] by this
   work, and NOT DELIVERED (2) of the header stands.

   THE THREE PIECES.

   (1) [si_to] is [cong_spanning_arrow]: every congruence quotient, with
   its canonical bilinear map, IS a spanning arrow.  The spanning proof is
   [QMod_gen_spanning] of section 3A.

   (2) [si_rep] is the interesting half.  At a spanning arrow [(W; (g; sp))]
   with [β := g ttt], the representative is [ker_idx β], and [ker_med β] is
   an ISOMORPHISM -- injective because the congruence IS the kernel pair,
   surjective because [β] spans.

   (3) The arrow clause is [reflexivity] after destructing the singleton.

   ONE TRAP, worth the line.  [sp : Spanning (Bilin V V') g] is NOT
   [Spanning (Bilin V V') (global_element (g ttt))]: eta on the singleton
   is not definitional.  The transport is Adjunction/SpanningArrow.v's
   [spanning_respects], with [g ≈ global_element (g ttt)] proved by
   destructing the singleton. *)

Definition cong_spanning_arrow {R : RingObject} {V V' : obj[RMod R]}
  (i : CongIdx V V') : SpanningArrowsOutOf (Bilin V V') SetsOne :=
  existT _ (QModOf i)
    (existT _ (global_element (X := Bilin V V' (QModOf i)) (QModGenOf i))
       (rbilinear_spanning_to_spanning (QModGenOf i)
          (QMod_gen_spanning (`1 i) (`2 i)))).

Theorem tensor_spanning_SmallUpToIso {R : RingObject} (V V' : obj[RMod R]) :
  SmallUpToIso (sols_of_esols (Bilin V V') (tensor_esols_direct V V')).
Proof.
  unshelve refine (@Build_SmallUpToIso (RMod R) Sets (Bilin V V') SetsOne
                     (sols_of_esols (Bilin V V') (tensor_esols_direct V V'))
                     (CongIdx V V') cong_spanning_arrow _).
  intro i.
  destruct i as [W [g sp]].
  pose (beta := g ttt).
  assert (Hg : g ≈ global_element (X := Bilin V V' W) beta).
  { intro u; destruct u; intros v w; reflexivity. }
  assert (Hsp : RBilinearSpanning beta).
  { exact (spanning_to_rbilinear_spanning beta
             (spanning_respects (Bilin V V') g
                (global_element (X := Bilin V V' W) beta) Hg sp)). }
  exists (ker_idx beta).
  unshelve eexists.
  - exact (ker_iso beta Hsp).
  - intro u; destruct u; simpl; intros v w; reflexivity.
Defined.

(* Mac Lane's OWN family, resized by his own Lemma 2. *)
Definition tensor_esols_resized {R : RingObject} (V V' : obj[RMod R]) :
  ElementSolutionSet (Bilin V V') :=
  esols_of_sols (Bilin V V')
    (resize_up_to_iso (sols_of_esols (Bilin V V') (tensor_esols_direct V V'))
       (tensor_spanning_SmallUpToIso V V')).

(* ...and fed to the theorem.  Same signature as [tensor_via_AFT], reached
   by a different argument: p. 128's covering family plus Lemma 2, rather
   than the kernel congruence of an arbitrary bilinear map directly. *)
Definition tensor_via_AFT_maclane {R : RingObject} (V V' : obj[RMod R]) :
  Representable (Bilin V V') :=
  tensor_via_AFT_of_esols V V' (tensor_esols_resized V V').
