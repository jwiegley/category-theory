Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Construction.Elements.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SpanningArrow.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Product.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Quotient.Isomorphism.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Spanning bilinear maps, and the solution set for the tensor product

    nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
    nLab:      https://ncatlab.org/nlab/show/solution+set+condition
    nLab:      https://ncatlab.org/nlab/show/subobject
    Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules

    Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
    §V.7, book p. 128 (PDF p. 137), is the source of everything below: the
    unnumbered construction of the tensor product from the adjoint functor
    theorem (catalog id `maclane:V.7:construction1`) and Exercise 3 (catalog
    id `maclane:V.7:ex3`).  CITED BY LOCATION AND BY THE IN-TREE CATALOG:
    the printed text was not consulted and no sentence of it is reproduced
    here.  The catalog summaries this file works from live in
    doc/plan/books/maclane/inventory/V.json, and they read:

      construction1 -- "For modules A and B over a commutative ring K, a
      tensor product is a universal element of the set Bilin(A,B;C) of
      bilinear functions beta : A x B -> C into a third K-module C;
      Bilin(A,B;-) is (the object part of) a functor of C.  To get a
      solution set it suffices to consider only the bilinear beta which
      span C, i.e. do not factor through a proper submodule of C; such a C
      consists of all finite sums of the form sum beta(a_i,b_i), which
      bounds its cardinality and gives the solution set condition.  Since
      K-Mod is small-complete and Bilin(A,B;-) : K-Mod -> Set is
      continuous, the adjoint functor theorem yields a universal bilinear
      map A x B -> A tensor B."

      ex3 -- "For R a ring, A a right R-module and B a left R-module, use
      the adjoint functor theorem to construct A tensor_R B ... Prove that
      A tensor_R B is spanned, as an abelian group, by the elements a
      tensor b.  If S -> R is a morphism of rings, examine the relation
      between A tensor_S B and A tensor_R B."

    THIS FILE IS THE SPANNING HALF of that programme.  It delivers Mac
    Lane's solution set -- the bilinear maps that span their target -- and
    his "spanned by the elementary tensors", together with the module-side
    vocabulary they need.  It does NOT build the tensor product from the
    adjoint functor theorem: the two remaining premises of
    `representability_theorem` (Adjunction/Representability/Sets.v:391),
    namely `Complete (RMod R)` and `PreservesImageLimit (Bilin V V')`, are
    not inhabited here, and the comparison of an AFT-produced object with
    Instance/Mod/Tensor.v's [TensorMod] is not attempted.  See NOT
    DELIVERED.

    WHAT IS DELIVERED, IN NINE STEPS, AND AT WHAT STRENGTH.

    (1) THE SUBMODULE/SUBOBJECT BRIDGE.  Mac Lane's §V.7 Definition 1
    records that "these categorical subobjects agree with the
    element-defined ones in Rng, Grp, Ab and R-Mod"; before this PR
    nothing in tree connected the two at [RMod R] -- `git grep -l 'SubObj'
    5f681ba4 -- Instance/Mod.v Instance/Mod/` returns nothing, and that
    command still reproduces from the merged tree.  [smod_subobj] carries
    a [Submodule] (Instance/Mod/Quotient.v:229) to a [SubObj]
    (Theory/Subobject.v:15) and [subobj_smod] carries a subobject back, as
    the image submodule of its mono (`ImageSubmod`, Quotient.v:761).  The
    subobject round trip is at `≈` on [SubObj W] ([smod_subobj_image_equiv],
    through the two [sub_le]s [smod_subobj_image_le] and
    [smod_subobj_image_ge]) and NOT at [eq_refl]; the submodule round trip
    is only inter-derivable, [smod_round_to] and [smod_round_from], because
    the membership of [subobj_smod (smod_subobj S)] is a sigma over the
    submodule's own carrier and so is a different [Type] from [smod_mem S];
    NEGATIVE 1 of Test/ProbeModSpanning449.v pins that the [eq_refl]
    reading is refused, with [smod_round_iff] beside it as the control.
    What IS [eq_refl] is [smod_subobj_dom], [smod_subobj_mono] and
    [subobj_smod_mem].  [smod_subobj] is built with `@Build_SubObj`
    explicitly: a record literal picks the record's category parameter from
    the first field it elaborates, and that trap is on record in the
    project memory.  The one new module fact is [rmod_image_retract] -- a
    monic map retracts its own image submodule -- whose four laws are one
    and the same argument, [rmod_monic_injective] (Instance/Mod.v:521)
    applied to [rmod_image_witness].

    (2) THE GENERATED SUBMODULE.  [MGen P] is the submodule generated by a
    [Type]-valued predicate, as an inductive family with FIVE constructors,
    packaged as [SubGenMod P : Submodule M].  Negation is NOT a
    constructor: [smod_neg] (Quotient.v:242) derives it from (−1)·a, which
    is why [MGen] closes under scalar multiplication where [ABGen] of step
    (8) closes under negation; both are five-constructor inductives, with
    four closure constructors each.
    Leastness comes in both orders: [mgen_least], the [Fixpoint] one case
    per constructor in the idiom of Instance/Variety/Spanning.v:464, and
    [mgen_sub_le_least], the same fact read as [sub_le] in [SubObj M] --
    the statement #448 left unstated for varieties.

    (3) SPANNING, ELEMENTWISE AND CATEGORICALLY, AND THEIR EQUIVALENCE.
    [RBilinearSpanning β] says every element of the target lies in
    [MGen (rbl_image β)]; [Spanning (Bilin V V') (global_element β)] is
    #448's categorical form (Adjunction/SpanningArrow.v:276) at the functor
    [Bilin V V'] (Instance/Mod/Tensor.v:814) and the global element
    (Theory/Universal/Element.v:271) of a bilinear map.  The two are
    equivalent, as two named functions [rbilinear_spanning_to_spanning] and
    [spanning_to_rbilinear_spanning] packaged by [rbilinear_spanning_iff].
    The forward direction is the substantial one: a subobject through which
    β factors bilinearly has an image submodule containing the image of β,
    hence containing everything [MGen] generates, so its mono is surjective
    as well as injective and therefore splits ([rmod_split]).  The backward
    direction corestricts β to [SubGenMod (rbl_image β)]
    ([rbl_gen_corestrict]) and reads the splitting off the conclusion.
    Neither direction goes through [sub_le_top_iso] or
    [spanning_forces_top] (Adjunction/SpanningArrow.v:367, :381): the
    positive form of [Spanning] hands back the splitting directly, so those
    two are available to a reader but are not consumed here.

    (4) THE ELEMENTARY TENSORS SPAN.  [tensor_gen_spanning] is Mac Lane's
    "spanned by the elements a ⊗ b" for [TensorMod], by induction on
    [MTerm] in five cases -- the same five [tensor_hom_ext]
    (Instance/Mod/Tensor.v:730) runs one level up -- and
    [tensor_gen_spanning_categorical] is the same fact in the [Spanning]
    form, obtained from (3) rather than re-proved.

    (5) WIDE PULLBACKS IN [RMod R].  [RMod_HasWidePullbacks] is the tree's
    SECOND [HasWidePullbacks] instance (Instance/Sets/SubobjectLattice.v's
    [Sets_HasWidePullbacks] was the only one) and its first at an algebraic
    category.  The apex is the submodule of Instance/Mod/Product.v's
    [ProdMod] on which all the maps of the family agree; the projections
    are [prod_proj] after the inclusion and the mediator is a tuple.

    IT DOES NOT DISCHARGE THE HYPOTHESIS OF [spanning_solution_set], AND
    THE REASON IS A UNIVERSE, MEASURED.  With Set Printing Universes,

      About RMod_HasWidePullbacks.

    reports, RE-MEASURED 2026-09-17 in the PR "algebraic carriers are
    sets" (an earlier revision of this comment printed the ring's three
    universe slots in the wrong order, as [RingObject@{u u2 u3}], and did
    not carry the [Set < u0] line; nothing else in the readback changed,
    and neither correction touches the argument below),

      RMod_HasWidePullbacks@{u u0 u1 u2 u3} :
        ∀ R : RingObject@{u3 u u2},
        HasWidePullbacks@{u u u0 u} (RMod@{u0 u1 u3 u2 u} R)
      (* ... Set < u0, u < u0, u < u1, u3 <= u0, ... *)

    -- the class's INDEX universe is instantiated at [u], the universe of
    the module CARRIERS, which the block pins strictly BELOW [u0], the
    universe where [RModObject R] itself lives.  [SubObj W] lives at [u0],
    so [FactoringFamily] (Adjunction/SpanningArrow.v:408) does too, and

      Check (@spanning_solution_set (RMod R) Sets (Bilin V V')
               (RMod_HasWidePullbacks R) GP SetsOne).

    is refused with

      The term "RMod_HasWidePullbacks R" has type
       "HasWidePullbacks@{u_car u_car u_obj u_car} (RMod@{u_obj ...} R)"
      while it is expected to have type
       "HasWidePullbacks@{u_idx u_idx' u_obj' u_car} (RMod@{u_obj' ...} R)"
      (universe inconsistency: Cannot enforce u_car = u_idx because
       u_car < u1 <= u2 <= u_idx)

    (the generated universe names are replaced by readable ones,
    positionally; everything else is verbatim, and NEGATIVE 2 of
    Test/ProbeModSpanning449.v re-runs it).  The pin
    is ATTRIBUTED, not guessed: it is not [Submodule]'s and not the class's
    but [ProdMod]'s, whose carrier is the dependent function space
    [∀ i : I, carrier (cmon_setoid (V i))], so the index universe is at or
    below the carrier universe, while an object of [RMod R] has its carrier
    strictly below the object universe.  A control makes this exact:

      Check (fun (W : obj[RMod R]) (A : @SubObj (RMod R) W -> obj[RMod R])
               => (@ProdMod R (@SubObj (RMod R) W) A : obj[RMod R])).

    is refused with "The term \"ProdMod A\" has type \"RModObject R\"
    while it is expected to have type \"obj[RMod R]\" (universe
    inconsistency: Cannot enforce u_prod = u_car because u_car < u1 <= u2
    <= u3 <= u_prod)" -- a four-step chain from the module carrier level
    up to the product's, re-run as NEGATIVE 3 of the probe with a
    [ProdMod] over a bare [Type] beside it.  ANNOTATION WAS TRIED AND
    CANNOT HELP: the two constraints are [index ≤ carrier] (from the
    product) and [carrier < object] (from [RModObject] being a record over
    a [SetoidObject]), and [SubObj W] is at the object universe, so no
    annotation of the instance can satisfy both.  This is the same
    obstruction Adjunction/SpanningArrow.v:236-245 records for
    [Sets_HasWidePullbacks], reproduced on the module side and now with the
    donor named.  BOTH REFUSALS ARE PINNED: they are NEGATIVES 2 and 3 of
    Test/ProbeModSpanning449.v, each stripped and re-run alone in a copy of
    the whole probe so the refusal kind could be read rather than guessed,
    with the abstract-[HWP] application and a [ProdMod] over a bare [Type]
    as the paired positive controls.  The instance is landed anyway, as a
    wide pullback in [RMod R] worth having; what it does not do is stated
    here rather than left to a reader.

    (6) [Bilin V V'] PRESERVES WIDE PULLBACKS, UNCONDITIONALLY.
    [Bilin_PreservesWidePullbacks] is the first witness of
    [PreservesWidePullbacks] (Adjunction/SpanningArrow.v:291) for ANY
    functor in the tree.  It is proved against an ARBITRARY
    [IsWidePullback] rather than against the apex of (5) -- which is what
    keeps its index universe free, and therefore what lets it be applied at
    [FactoringFamily] -- by a small element calculus: [wpull_elem_unique]
    (elements of the apex are separated by the projections),
    [wpull_elem] (the element determined by a compatible family) and
    [wpull_elem_proj].  All three go through [rmod_by_element]
    (Instance/Mod/Representable.v:113), r ↦ r·m, evaluated at the unit of
    R, and through [wide_pullback_jointly_monic] (Structure/Pullback/
    Wide.v:271).  Monicity of the family is not spent: the hypothesis [Hm]
    of [PreservesWidePullbacks] is accepted and ignored, so the statement
    proved is stronger than the interface asks for.

    (7) THE SOLUTION SET.  Inside a section over
    `Context \`{HWP : @HasWidePullbacks (RMod R)}` -- the ONE premise this
    file leaves open, for the measured reason in (5) --
    [tensor_solution_set] is Mac Lane's covering family for [Bilin V V']
    -- a solution set in the sense of the record, with no smallness -- and
    [tensor_esols] its element-wise form.  Three [eq_refl] readbacks pin
    what survives the two repackagings: [esol_index tensor_esols] IS
    [SpanningArrowsOutOf (Bilin V V') SetsOne], [esol_obj] is the first
    projection and [esol_elem] is the spanning bilinear map evaluated at
    [ttt].  NO SMALLNESS: [sol_index] and [esol_index] are bare [Type]s, so
    Mac Lane's cardinality bound ("all finite sums") is not part of what
    the records ask for and nothing below supplies it.

    THE OTHER ROUTE TO THE SAME INDEX.  Instance/Mod/TensorAFT.v carries
    [tensor_esols_direct], Mac Lane's p. 128 argument written out
    UNCONDITIONALLY: it corestricts an arbitrary bilinear map to the
    submodule generated by its image ([rbl_gen_corestrict] of step (3)
    below), proves the corestriction spans, and covers by the inclusion --
    no wide pullbacks anywhere, so the hypothesis this section leaves open
    is not needed there.  The two solution sets are indexed by the SAME
    type ON THE NOSE: [tensor_esols_same_index] in that file is
    [esol_index (@tensor_esols R V V' HWP)
       = esol_index (tensor_esols_direct V V') := eq_refl],
    with [HWP] passed EXPLICITLY, since [RMod_HasWidePullbacks] would be
    found by resolution and then refused at the application for the reason
    in (5).  Mac Lane's Lemma 2 route (here) and his p. 128 route (there)
    therefore agree about WHAT the solution set is indexed by and differ
    only in what they assume.

    (8) EXERCISE 3, THE SPANNING CLAUSE.  [ABGen P] is the subgroup of an
    abelian group generated by a predicate and [bal_gen_spanning] says
    Instance/Mod/Bimodule.v:710's [BalTensor] -- the genuinely balanced
    tensor of a right and a left module over a possibly non-commutative
    ring, which lands in [Ab] -- is spanned as an abelian group by the
    elements [bs_gen n m], by induction on [bsum] in four cases.  [ABGen]
    has an [abgen_neg] constructor where [MGen] has [mgen_smul], there
    being no scalar in [Ab] to derive negation from; the two inductives
    have five constructors each.  Instance/Ab/DirectedColimit.v
    has an [AbSubgroup] record (:273) but its generated notion [InGen]
    (:381) is generated by a finite LIST rather than by a predicate, so
    nothing there is reused and that file is deliberately not required
    here; [abgen_least] is stated against a bare closed predicate instead.

    (9) EXERCISE 3, THE BASE-CHANGE CLAUSE.  For `phi : T ~{Rng}~> R` --
    Mac Lane's "morphism of rings S → R", with T for his S -- restriction
    of scalars (Instance/Rng/Mod.v:212, :277) gives [bal_right_T] and
    [bal_left_T], and [bal_change] is the comparison group homomorphism
    A ⊗_T B → A ⊗_R B.  It carries generators to generators at [eq_refl]
    ([bal_change_gen]); it is SURJECTIVE ([bal_change_surjective], by
    induction on the formal sums of the target), so A ⊗_R B is a quotient
    of A ⊗_T B; and it is characterised as [bal_med] of the R-balanced
    generator read as a T-balanced map ([bal_change_is_med], through
    [bal_med_unique], Bimodule.v:784).  ITS KERNEL IS NOT DESCRIBED --
    see NOT DELIVERED.

    NOT DELIVERED, and the scope of each statement is this file rather than
    the tree.  (1) NO TENSOR PRODUCT FROM THE ADJOINT FUNCTOR THEOREM IS
    BUILT HERE.  [representability_theorem] needs `Complete (RMod R)` and
    `PreservesImageLimit (Bilin V V')`; neither is built here and no
    constant below mentions either.  Both are landed by the siblings of
    this PR -- [RMod_Complete] at Instance/Mod/Limit.v:804 and
    [Bilin_PreservesImageLimit] in Instance/Mod/TensorAFT.v -- and so is
    the headline of `maclane:V.7:construction1`, the universal bilinear
    map produced by the AFT: [tensor_via_AFT] in that file is
    [representability_theorem] at those two, CONDITIONALLY on an
    [ElementSolutionSet] whose index the theorem pins at the ring's
    CARRIER universe, which neither this file's [tensor_esols] nor that
    file's [tensor_esols_direct] can supply, both being indexed by a sigma
    over the OBJECTS of [RMod R] (the refusal is NEGATIVE 1 of that
    file's probe, Test/ProbeModTensorAFT449.v).  What is landed HERE is
    the solution-set
    half, itself conditional for the different reason of (4).  (2) NO
    COMPARISON WITH [TensorMod].  Nothing below
    relates an AFT-produced representing object to Instance/Mod/Tensor.v's
    [TensorMod], at [eq_refl] or at `≅`; [tensor_gen_spanning] says only
    that the EXISTING tensor's canonical bilinear map is one of the
    spanning arrows the solution set is indexed by.  (3) NO SMALLNESS and
    so no cardinality bound, for the reason in (7); this is inherited from
    the records of Adjunction/GAFT.v:179 and Adjunction/Representability/
    Sets.v:233, and Adjunction/SpanningArrow.v:218-222 says the same of
    itself.  (4) NO [HasWidePullbacks] AT THE UNIVERSE THE SOLUTION SET
    WANTS, for the measured reason in (5); [tensor_solution_set] and
    [tensor_esols] are therefore axiom-free CONDITIONALS over that one
    hypothesis, in the sense docs/INHABITATION.md uses.  (5) THE KERNEL OF
    [bal_change] IS NOT DESCRIBED.  Surjectivity is proved; nothing below
    identifies the kernel, exhibits it as generated by the elements
    (a·r) ⊗ b − a ⊗ (r·b) for r outside the image of phi, or shows the
    comparison is an isomorphism in any case.  Mac Lane's "examine the
    relation" is answered with a surjection and its universal
    characterisation, and no more.  (6) NO NON-DEGENERACY WITNESS.  No
    concrete ring map is instantiated, so nothing below shows [bal_change]
    is ever NOT injective; the tree has no non-commutative ring at all
    (Instance/Mod/Tensor.v:120-176 records that gap), so the
    non-commutative reading of ex3 is uninstantiated here as elsewhere.
    (7) ONLY THREE OF THE BOUNDARIES ARE PINNED IN Test/.
    Test/ProbeModSpanning449.v carries this file's full 25-`Require` list
    plus the file, and pins three: NEGATIVE 1, the submodule round trip
    being inter-derivable and not [eq_refl] (CONVERSION, with
    [smod_round_iff] as the control); NEGATIVE 2, the exported
    [RMod_HasWidePullbacks] not discharging [spanning_solution_set]'s
    hypothesis (UNIVERSE, with the abstract-[HWP] application beside it as
    the positive control); and NEGATIVE 3, the donor one level down at
    [ProdMod] indexed by [SubObj] (UNIVERSE, with a [ProdMod] over a bare
    [Type] as the control).  Each was re-run alone with its guard stripped
    in a copy of the whole probe, and the refusal kinds are read off the
    messages rather than guessed.  Two more facts of this file are pinned
    in Test/ProbeModTensorAFT449.v: the shared index ([c_same_index]) and
    [MGen]'s positional predicate (its NEGATIVE 7).
    Everything else claimed here -- the eq_refl readbacks of section 7, the
    two load-bearing [Defined]s, the equivalence of the two spanning
    forms, the ex3 clauses -- rests on being compiled here and is not
    guarded by a probe.  (8) NO [Complete]-free route: nothing below
    weakens [representability_theorem] or offers a spanning-only
    representability statement.  (9) NO PROPER-RESTRICTION WITNESS.
    Nothing below exhibits a bilinear map that is NOT spanning, so the
    restriction Mac Lane's argument turns on is not shown to cut anything
    down; non-vacuity is witnessed only positively, by
    [tensor_gen_spanning_categorical].  Combined with (3), the solution set
    is Mac Lane's in SHAPE and in nothing that bounds it.

    MEASURED. 80 `.glob` heads -- 40 `def`, 19 `prf`, 10 `constr`, 8
    `scheme`, 2 `ind`, 1 `inst` -- plus 26 [Program] obligations, which
    appear in NEITHER the `.glob` heads NOR `Search inside`, enumerated with
    `strings Instance/Mod/Spanning.vo | grep -o
    '[A-Za-z0-9_]*_obligation_[0-9]*' | sed 's/^[0-9]*//' | sort -u` (the
    junk digit prefix stripped, not dropped) and cross-checked against
    `Print Module Category.Instance.Mod.Spanning`, which lists the same 26
    and no others: four each for [rmod_image_retract], [mgen_sub_include],
    [rmod_split] and [wpull_mod_tuple], five each for [rbl_gen_corestrict]
    and [wpull_bilin_med]. (The census also reports three
    [ImageSubmod_obligation_*]; those are Instance/Mod/Quotient.v:833's and
    are not counted here.) All 106 are "Closed under the global context",
    zero `Axioms:` lines, run through a scratch file of `Print Assumptions
    Category.Instance.Mod.Spanning.<name>.` -- the obligations need the
    QUALIFIED name, the short one is not in scope after `Require Import` --
    and all 106 are registered in the `make print-assumptions` gate.
    Counted BY TOKEN with `grep -ow` over the file BELOW this header
    comment: 37 `Qed` and 16 `Defined` as proof terminators. (A `grep -ow`
    over the WHOLE file reports more, because it also counts the occurrences
    of both words in this comment; no whole-file figure is quoted here,
    since quoting one would change it.) EXACTLY TWO of the sixteen are
    LOAD-BEARING, measured by flipping each to `Qed` in a copy of the whole
    file: [WPullSub] (then [wpull_mod_commutes] stops, its `\`2 p i j` no
    longer applying), and [bal_change_bil] (then the [eq_refl] of
    [bal_change_gen] stops). The other fourteen were flipped to `Qed`
    TOGETHER and the file still compiles, so their transparency is a choice.
    Universes ([About] under `Set Printing Universes`, all 106): no [Set]
    in the universe block or printed type of any declared head or
    obligation, the only [Set] in the module being the auto-generated
    [MGen_rec] and [ABGen_rec] motives, which target [Set] by
    construction -- `grep -cw Set` over the 106 [About] blocks returns 2
    and both are those.  Nothing here is pinned, and
    [GAFT_from_spanning]'s [Set] pin was never reached because no constant
    below feeds [GAFT].  (CORRECTION, PR "algebraic carriers are sets",
    2026-09-17: that pin no longer exists -- [Section GAFTFromSpanning] was
    widened off [Set] and the theorem now reads
    [Category@{u u0 u0}] / [Category@{u1 u2 u2}] with [u <= u0].  The
    sentence is kept in the past tense because the reason it gave for this
    file's independence is unchanged: no constant below feeds [GAFT], and
    the widening does not make [GAFT_from_spanning] reach [RMod R] either
    -- see that file's header for the surviving refusal.) [smod_subobj], [subobj_smod], [mgen_sub_le_least]
    and [RMod_HasWidePullbacks] carry no equation and the same two strict
    constraints of [RMod R] itself -- the module carrier universe strictly
    below two others -- [smod_subobj] printing them as `u1 < u`, `u1 < u0`
    and the other three as `u < u0`, `u < u1`;
    [WPullSub] and [RMod_WidePullback] carry [ProdMod]'s ten
    equations (`u = u3 = u5 = u6 = u7 = u8 = u10 = u11 = u12`, `u1 = u4 =
    u9`); [Bilin_PreservesWidePullbacks] carries `u = u0 = u1`, ATTRIBUTED
    by [About] to [rmod_by_element] (Instance/Mod/Representable.v:113),
    which reports exactly those two equations while [Bilin],
    [wide_pullback_jointly_monic] and [IsWidePullback] each report none;
    [bal_change] and [bal_change_surjective] carry `u = u0 = u1 = u2 = u3 =
    u4`, identifying the THREE universes of BOTH rings, and those five
    equations are the SECTION BINDER's rather than any constant's, isolated
    with a trivial `Example : T = T := eq_refl` closed in four nested
    Sections: with only `Context {T R : RingObject}` it reports NO
    equation; adding `Context (phi : T ~{Rng}~> R)` alone already reports
    all five; adding the two [RModObject] binders adds none, and the file's
    own [bal_left_T], [bal_right_T], [bal_change] and
    [bal_change_surjective] report exactly the same five and no more.
    [RestrictObj], [RigHom_op], [Ring_op] and [Rig_op] each report none,
    and the control `Definition ctl_hom (T R : RingObject) : Type :=
    T ~{Rng}~> R` prints `RingObject@{u1 u1 u1}` for BOTH rings, so the
    whole identification is already [Rng]'s hom and the [RModObject]
    instances over [Ring_op R] and [Ring_op T] add nothing to it.
    Closure 162 files excluding this one, from
    25 `Require`s, by iterated `coqdep`; at the margin
    Adjunction/Representability/Sets.v costs 28, Instance/Mod/Bimodule.v 17,
    Instance/Rng/Mod.v 6, Instance/Mod/Representable.v 2, and four more cost
    1 each, the rest 0. Every `Require` was tested by deletion:
    Category.Theory.Isomorphism and Category.Instance.Ab.Subtract were
    droppable (marginal closure 0 both) and were removed; the remaining 25
    are each needed. Zero DECLARATION-HEAD COLLISIONS: none of the 106
    names is declared anywhere else, measured by scanning every one of the
    1017 other `.glob` files in the tree for a `def`/`prf`/`ind`/`constr`/
    `scheme`/`inst` head equal to one of them (file list from `find`, fed
    through `xargs`, so no `.gitignore` traversal rule can apply), with
    [tensor_gen] as the positive control (declared in
    Instance/Mod/Tensor.glob and Instance/Ab/Tensor.glob, two files) and a
    nonexistent name as the negative. MENTIONS are a different count and
    are not zero: over the 1021 other `.v` files, exactly three mention any
    of the 106 names, all as USES -- Instance/Mod/TensorAFT.v 25 of them,
    Test/ProbeModSpanning449.v 13 and Test/ProbeModTensorAFT449.v 6.
    `make todo` gains FOUR hits, all of them the four guarded commands of
    Test/ProbeModSpanning449.v (the instrument check and the three
    negatives); this file contributes none, in any letter case. *)

(** ** 1. Submodules and subobjects of [RMod R] *)

Definition smod_subobj {R : RingObject} {W : RModObject R} (S : Submodule W) :
  @SubObj (RMod R) W :=
  @Build_SubObj (RMod R) W (SubmoduleMod S) (smod_incl S) (smod_incl_monic S).

Example smod_subobj_dom {R : RingObject} {W : RModObject R} (S : Submodule W) :
  sub_dom (smod_subobj S) = SubmoduleMod S := eq_refl.

Example smod_subobj_mono {R : RingObject} {W : RModObject R} (S : Submodule W) :
  sub_mono (smod_subobj S) = smod_incl S := eq_refl.

Definition subobj_smod {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : Submodule W := ImageSubmod (sub_mono m).

Example subobj_smod_mem {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) (b : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod m) b
    = { a : carrier (cmon_setoid (sub_dom m))
      & cmon_map (rm_hom (sub_mono m)) a ≈ b } := eq_refl.

(* The witness carried by a member of an image submodule. *)
Lemma rmod_image_witness {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (p : smod_carrier (ImageSubmod f)) :
  cmon_map (rm_hom f) (`1 (`2 p)) ≈ `1 p.
Proof. exact (`2 (`2 p)). Qed.

(* When f is monic its image submodule retracts onto the source: the
   preimage carried by a member is unique, by injectivity, so the second
   projection is a homomorphism.  All four laws are the SAME argument --
   apply injectivity, then [rmod_image_witness] on both sides. *)
Program Definition rmod_image_retract {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hm : Monic f) :
  SubmoduleMod (ImageSubmod f) ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun p : smod_carrier (ImageSubmod f) => `1 (`2 p) |} |}
|}.
Next Obligation.
  intros R M N f Hm p q Hpq.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f p), (rmod_image_witness f q); exact Hpq.
Qed.
Next Obligation.
  intros R M N f Hm; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f (cmon_zero (SubmoduleMod (ImageSubmod f)))).
  simpl; symmetry; exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f Hm p q; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f
             (cmon_plus (SubmoduleMod (ImageSubmod f)) p q)).
  rewrite (cmon_map_plus (rm_hom f)).
  rewrite (rmod_image_witness f p), (rmod_image_witness f q).
  simpl; reflexivity.
Qed.
Next Obligation.
  intros R M N f Hm r p; simpl.
  apply (rmod_monic_injective f Hm).
  rewrite (rmod_image_witness f
             (rm_smul (SubmoduleMod (ImageSubmod f)) r p)).
  rewrite (rm_map_smul f).
  rewrite (rmod_image_witness f p).
  simpl; reflexivity.
Qed.

Lemma rmod_image_retract_commutes {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hm : Monic f) :
  @compose (RMod R) _ _ _ f (rmod_image_retract f Hm)
    ≈ smod_incl (ImageSubmod f).
Proof. intro p; exact (rmod_image_witness f p). Qed.

(* The two halves of the round trip on the SUBOBJECT side. *)
Definition smod_subobj_image_le {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : sub_le (smod_subobj (subobj_smod m)) m.
Proof.
  exact (existT _ (rmod_image_retract (sub_mono m) (sub_is_monic m))
                  (rmod_image_retract_commutes (sub_mono m)
                     (sub_is_monic m))).
Defined.

Definition smod_subobj_image_ge {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : sub_le m (smod_subobj (subobj_smod m)).
Proof.
  exact (existT _ (mod_image_cores (sub_mono m))
                  (mod_image_factors (sub_mono m))).
Defined.

(* Mac Lane V.7 Definition 1's "these categorical subobjects agree with
   the element-defined ones in R-Mod", one half: every subobject of a
   module IS its image submodule, at `≈` on [SubObj W]. *)
Theorem smod_subobj_image_equiv {R : RingObject} {W : RModObject R}
  (m : @SubObj (RMod R) W) : smod_subobj (subobj_smod m) ≈ m.
Proof.
  apply sub_le_antisym.
  - exact (smod_subobj_image_le m).
  - exact (smod_subobj_image_ge m).
Defined.

(* The other half, on the SUBMODULE side.  It is NOT [eq_refl]: the
   membership of [subobj_smod (smod_subobj S)] is a sigma over the
   submodule's own carrier, so the two Types differ even though the two
   memberships are inter-derivable. *)
Definition smod_round_to {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod (smod_subobj S)) a → smod_mem S a.
Proof.
  intros [p Hp]; exact (smod_at S Hp (`2 p)).
Defined.

Definition smod_round_from {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem S a → smod_mem (subobj_smod (smod_subobj S)) a.
Proof.
  intro Ha.
  unshelve eexists.
  - exact (existT _ a Ha).
  - simpl; reflexivity.
Defined.

Theorem smod_round_iff {R : RingObject} {W : RModObject R}
  (S : Submodule W) (a : carrier (cmon_setoid W)) :
  smod_mem (subobj_smod (smod_subobj S)) a ↔ smod_mem S a.
Proof.
  split; [ exact (smod_round_to S a) | exact (smod_round_from S a) ].
Defined.

(** ** 2. The submodule generated by a predicate *)

Section Generated.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (P : carrier (cmon_setoid M) → Type).

(* FIVE constructors, not four: [mgen_zero] cannot be dropped (P may be
   empty) and [mgen_resp] is required because [smod_resp] is a FIELD of
   [Submodule].  Closure under negation is DERIVED -- [smod_neg]
   (Instance/Mod/Quotient.v:260) gets it from (−1)·a -- so there is no
   [mgen_neg]. *)
Inductive MGen : carrier (cmon_setoid M) → Type :=
  | mgen_base : ∀ a, P a → MGen a
  | mgen_resp : ∀ a b, a ≈ b → MGen a → MGen b
  | mgen_zero : MGen (cmon_zero M)
  | mgen_plus : ∀ a b, MGen a → MGen b → MGen (cmon_plus M a b)
  | mgen_smul : ∀ (r : carrier (rig_setoid (ring_rig R))) a,
      MGen a → MGen (rm_smul M r a).

Definition SubGenMod : Submodule M :=
  @Build_Submodule R M MGen mgen_resp mgen_zero mgen_plus mgen_smul.

Definition mgen_incl (a : carrier (cmon_setoid M)) (Ha : P a) :
  smod_mem SubGenMod a := mgen_base a Ha.

(* Leastness, in the [Fixpoint] idiom of Instance/Variety/Spanning.v:464:
   one case per constructor, no tactic. *)
Fixpoint mgen_least (S : Submodule M) (HS : ∀ a, P a → smod_mem S a)
  (a : carrier (cmon_setoid M)) (D : MGen a) {struct D} : smod_mem S a :=
  match D in MGen a' return smod_mem S a' with
  | mgen_base a Ha      => HS a Ha
  | mgen_resp a b H D'  => smod_resp S a b H (mgen_least S HS a D')
  | mgen_zero           => smod_zero S
  | mgen_plus a b D1 D2 =>
      smod_plus S a b (mgen_least S HS a D1) (mgen_least S HS b D2)
  | mgen_smul r a D'    => smod_smul S r a (mgen_least S HS a D')
  end.

End Generated.

(* Leastness read in the SUBOBJECT order of [RMod R] -- the statement
   #448 left unstated for varieties. *)
Program Definition mgen_sub_include {R : RingObject} {M : RModObject R}
  (P : carrier (cmon_setoid M) → Type) (S : Submodule M)
  (HS : ∀ a, P a → smod_mem S a) :
  SubmoduleMod (SubGenMod P) ~{RMod R}~> SubmoduleMod S := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun p : smod_carrier (SubGenMod P) =>
      existT _ (`1 p) (mgen_least P S HS (`1 p) (`2 p)) |} |}
|}.
Next Obligation. intros R M P S HS p q Hpq; exact Hpq. Qed.
Next Obligation. intros R M P S HS; simpl; reflexivity. Qed.
Next Obligation. intros R M P S HS p q; simpl; reflexivity. Qed.
Next Obligation. intros R M P S HS r p; simpl; reflexivity. Qed.

Theorem mgen_sub_le_least {R : RingObject} {M : RModObject R}
  (P : carrier (cmon_setoid M) → Type) (S : Submodule M)
  (HS : ∀ a, P a → smod_mem S a) :
  sub_le (smod_subobj (SubGenMod P)) (smod_subobj S).
Proof.
  exists (mgen_sub_include P S HS).
  intro p; simpl; reflexivity.
Defined.

(** ** 3. Spanning bilinear maps, elementwise and categorically *)

(* The image of a bilinear map, as a bare [Type]-valued predicate -- the
   membership shape of [ImageSubmod] (Instance/Mod/Quotient.v:833) with
   two preimages instead of one. *)
Definition rbl_image {R : RingObject} {V V' W : RModObject R}
  (β : RBilinear V V' W) (x : carrier (cmon_setoid W)) : Type :=
  { v : carrier (cmon_setoid V) &
    { w : carrier (cmon_setoid V') & rbl_map β v w ≈ x } }.

(* Mac Lane's "β spans C", elementwise: the submodule generated by the
   image of β is all of W. *)
Definition RBilinearSpanning {R : RingObject} {V V' W : RModObject R}
  (β : RBilinear V V' W) : Type :=
  ∀ x : carrier (cmon_setoid W), MGen (rbl_image β) x.

(* A bijective module map splits.  The section is not canonical -- it
   picks the preimage the surjectivity datum carries -- and every one of
   its four laws is injectivity applied to the witness equation. *)
Program Definition rmod_split {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hi : RModInjective f) (Hs : RModSurjective f) :
  N ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun b : carrier (cmon_setoid N) => `1 (Hs b) |} |}
|}.
Next Obligation.
  intros R M N f Hi Hs a b Hab.
  apply Hi; rewrite (`2 (Hs a)), (`2 (Hs b)); exact Hab.
Qed.
Next Obligation.
  intros R M N f Hi Hs; simpl.
  apply Hi; rewrite (`2 (Hs (cmon_zero N))).
  symmetry; exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f Hi Hs a b; simpl.
  apply Hi.
  rewrite (cmon_map_plus (rm_hom f)).
  rewrite (`2 (Hs (cmon_plus N a b))), (`2 (Hs a)), (`2 (Hs b)).
  reflexivity.
Qed.
Next Obligation.
  intros R M N f Hi Hs r a; simpl.
  apply Hi.
  rewrite (rm_map_smul f).
  rewrite (`2 (Hs (rm_smul N r a))), (`2 (Hs a)).
  reflexivity.
Qed.

Lemma rmod_split_commutes {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) (Hi : RModInjective f) (Hs : RModSurjective f) :
  @compose (RMod R) _ _ _ f (rmod_split f Hi Hs) ≈ @id (RMod R) N.
Proof. intro b; exact (`2 (Hs b)). Qed.

Section SpanningEquivalence.

Context {R : RingObject}.
Context {V V' W : RModObject R}.
Context (β : RBilinear V V' W).

(* The restriction of β to a submodule it factors through, as a datum. *)
Definition rbl_restrict_image (m : @SubObj (RMod R) W)
  (β' : RBilinear V V' (sub_dom m))
  (Hβ : ∀ v w, cmon_map (rm_hom (sub_mono m)) (rbl_map β' v w)
                 ≈ rbl_map β v w)
  (a : carrier (cmon_setoid W)) (Ha : rbl_image β a) :
  smod_mem (subobj_smod m) a.
Proof.
  destruct Ha as [v [w Hvw]].
  exists (rbl_map β' v w).
  rewrite (Hβ v w); exact Hvw.
Defined.

(* → : elementwise spanning implies Mac Lane's categorical form. *)
Theorem rbilinear_spanning_to_spanning (H : RBilinearSpanning β) :
  Spanning (Bilin V V') (global_element (X := Bilin V V' W) β).
Proof.
  intros m [k Hk].
  (* the lifted bilinear map, and its commutation *)
  pose (β' := k ttt).
  assert (Hβ : ∀ v w, cmon_map (rm_hom (sub_mono m)) (rbl_map β' v w)
                        ≈ rbl_map β v w) by exact (Hk ttt).
  (* the mono is surjective, because its image submodule contains the
     image of β and therefore everything [MGen] generates *)
  assert (Hs : RModSurjective (sub_mono m)).
  { intro x.
    exact (mgen_least (rbl_image β) (subobj_smod m)
             (rbl_restrict_image m β' Hβ) x (H x)). }
  assert (Hi : RModInjective (sub_mono m)) by
    exact (rmod_monic_injective (sub_mono m) (sub_is_monic m)).
  exists (rmod_split (sub_mono m) Hi Hs).
  exact (rmod_split_commutes (sub_mono m) Hi Hs).
Defined.

(* The corestriction of β to the submodule generated by its image. *)
Program Definition rbl_gen_corestrict :
  RBilinear V V' (SubmoduleMod (SubGenMod (rbl_image β))) := {|
  rbl_map := fun v w =>
    existT _ (rbl_map β v w)
      (mgen_base (rbl_image β) (rbl_map β v w)
         (existT _ v (existT _ w (reflexivity _))))
|}.
Next Obligation. intros v v' Hv w w' Hw; simpl; now rewrite Hv, Hw. Qed.
Next Obligation. intros v v' w; simpl; apply rbl_add_l. Qed.
Next Obligation. intros v w w'; simpl; apply rbl_add_r. Qed.
Next Obligation. intros r v w; simpl; apply rbl_smul_l. Qed.
Next Obligation. intros r v w; simpl; apply rbl_smul_r. Qed.

(* ← : Mac Lane's categorical form implies elementwise spanning. *)
Theorem spanning_to_rbilinear_spanning
  (H : Spanning (Bilin V V') (global_element (X := Bilin V V' W) β)) :
  RBilinearSpanning β.
Proof.
  assert (Hfac : SubFactorsThrough (Bilin V V')
                   (global_element (X := Bilin V V' W) β)
                   (smod_subobj (SubGenMod (rbl_image β)))).
  { exists (global_element (X := Bilin V V' (SubmoduleMod
                                   (SubGenMod (rbl_image β))))
              rbl_gen_corestrict).
    intros u v w; simpl; reflexivity. }
  destruct (H _ Hfac) as [j Hj].
  intro x.
  exact (mgen_resp (rbl_image β) _ _ (Hj x)
           (`2 (cmon_map (rm_hom j) x))).
Defined.

Theorem rbilinear_spanning_iff :
  RBilinearSpanning β
    ↔ Spanning (Bilin V V') (global_element (X := Bilin V V' W) β).
Proof.
  split.
  - exact rbilinear_spanning_to_spanning.
  - exact spanning_to_rbilinear_spanning.
Defined.

End SpanningEquivalence.

(** ** 4. The elementary tensors span *)

(* Mac Lane's "A ⊗ B is spanned by the elements a ⊗ b", by induction on
   [MTerm] in five cases -- the same five [tensor_hom_ext]
   (Instance/Mod/Tensor.v:730) runs one level up.  The [mt_neg] case
   costs nothing new: [smod_neg] already derives closure under negation
   from the four [Submodule] fields. *)
Theorem tensor_gen_spanning {R : RingObject} (V V' : RModObject R) :
  RBilinearSpanning (@tensor_gen R V V').
Proof.
  intro t; induction t.
  - refine (mgen_base (rbl_image (@tensor_gen R V V')) _ _).
    exists c, c0; reflexivity.
  - exact (mgen_zero (rbl_image (@tensor_gen R V V'))).
  - exact (mgen_plus (rbl_image (@tensor_gen R V V')) _ _ IHt1 IHt2).
  - exact (smod_neg (SubGenMod (rbl_image (@tensor_gen R V V'))) _ IHt).
  - exact (mgen_smul (rbl_image (@tensor_gen R V V')) _ _ IHt).
Defined.

Theorem tensor_gen_spanning_categorical {R : RingObject}
  (V V' : RModObject R) :
  Spanning (Bilin V V')
    (global_element (X := Bilin V V' (TensorMod V V')) (@tensor_gen R V V')).
Proof.
  exact (rbilinear_spanning_to_spanning (@tensor_gen R V V')
           (tensor_gen_spanning V V')).
Defined.

(** ** 5. Wide pullbacks in [RMod R] *)

Section WidePullbackMod.

Context {R : RingObject}.
Context {I : Type}.
Context {A : I → RModObject R}.
Context {z : RModObject R}.
Context (g : ∀ i : I, A i ~{RMod R}~> z).

(* The apex is the submodule of the product on which all the [g i] agree
   -- Mac Lane's intersection, computed elementwise. *)
Definition wpull_mem (f : carrier (cmon_setoid (ProdMod A))) : Type :=
  ∀ i j : I,
    cmon_map (rm_hom (g i)) (f i) ≈ cmon_map (rm_hom (g j)) (f j).

Definition WPullSub : Submodule (ProdMod A).
Proof using A I R g z.
  unshelve refine (@Build_Submodule R (ProdMod A) wpull_mem _ _ _ _).
  - intros a b Hab Ha i j.
    rewrite <- (Hab i), <- (Hab j); exact (Ha i j).
  - intros i j.
    rewrite (cmon_map_zero (rm_hom (g i))).
    rewrite (cmon_map_zero (rm_hom (g j))).
    reflexivity.
  - intros a b Ha Hb i j.
    rewrite (cmon_map_plus (rm_hom (g i)) (a i) (b i)).
    rewrite (cmon_map_plus (rm_hom (g j)) (a j) (b j)).
    rewrite (Ha i j), (Hb i j); reflexivity.
  - intros r a Ha i j.
    rewrite (rm_map_smul (g i) r (a i)), (rm_map_smul (g j) r (a j)).
    rewrite (Ha i j); reflexivity.
Defined.

Definition WPullMod : RModObject R := SubmoduleMod WPullSub.

Definition wpull_mod_proj (i : I) : WPullMod ~{RMod R}~> A i :=
  @compose (RMod R) _ _ _ (prod_proj A i) (smod_incl WPullSub).

Lemma wpull_mod_commutes (i j : I) :
  @compose (RMod R) _ _ _ (g i) (wpull_mod_proj i)
    ≈ @compose (RMod R) _ _ _ (g j) (wpull_mod_proj j).
Proof. intro p; exact (`2 p i j). Qed.

Program Definition wpull_mod_tuple {Q : RModObject R}
  (q : ∀ i : I, Q ~{RMod R}~> A i)
  (Hq : ∀ i j : I, @compose (RMod R) _ _ _ (g i) (q i)
                     ≈ @compose (RMod R) _ _ _ (g j) (q j)) :
  Q ~{RMod R}~> WPullMod := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun x : carrier (cmon_setoid Q) =>
      existT _ (fun i => cmon_map (rm_hom (q i)) x)
               (fun i j => Hq i j x) |} |}
|}.
Next Obligation.
  intros Q q Hq x y Hxy i; simpl.
  exact (proper_morphism (cmon_map (rm_hom (q i))) x y Hxy).
Qed.
Next Obligation.
  intros Q q Hq i; exact (cmon_map_zero (rm_hom (q i))).
Qed.
Next Obligation.
  intros Q q Hq x y i; exact (cmon_map_plus (rm_hom (q i)) x y).
Qed.
Next Obligation.
  intros Q q Hq r x i; exact (rm_map_smul (q i) r x).
Qed.

Definition RMod_WidePullback : WidePullback g.
Proof using A I R g z.
  unshelve refine (@Build_WidePullback (RMod R) I A z g
                     WPullMod wpull_mod_proj _ _).
  - exact wpull_mod_commutes.
  - intros Q q Hq.
    unshelve refine {| unique_obj := wpull_mod_tuple q Hq |}.
    + intros i x; reflexivity.
    + intros v Hv x i; symmetry; exact (Hv i x).
Defined.

End WidePullbackMod.

#[export] Instance RMod_HasWidePullbacks (R : RingObject) :
  HasWidePullbacks (RMod R) :=
  @Build_HasWidePullbacks (RMod R) (@RMod_WidePullback R).

(** ** 6. [Bilin V V'] preserves wide pullbacks *)

Section BilinWidePullbacks.

Context {R : RingObject}.
Context (V V' : RModObject R).

Section AtAFamily.

Context {I : Type}.
Context {B : I → RModObject R}.
Context {zz : RModObject R}.
Context (g : ∀ i : I, B i ~{RMod R}~> zz).
Context {P : RModObject R}.
Context {p : ∀ i : I, P ~{RMod R}~> B i}.
Context (HP : IsWidePullback g P p).

(* Elements of the apex are separated by the projections.  The bridge
   from elements to arrows is [rmod_by_element]
   (Instance/Mod/Representable.v:113): r ↦ r·x. *)
Lemma wpull_elem_unique (x y : carrier (cmon_setoid P))
  (H : ∀ i, cmon_map (rm_hom (p i)) x ≈ cmon_map (rm_hom (p i)) y) : x ≈ y.
Proof using B HP I P R g p zz.
  assert (Hd : ∀ i, @compose (RMod R) _ _ _ (p i) (rmod_by_element R P x)
                      ≈ @compose (RMod R) _ _ _ (p i) (rmod_by_element R P y)).
  { intros i r; simpl.
    rewrite (rm_map_smul (p i) r x), (rm_map_smul (p i) r y).
    now rewrite (H i). }
  pose proof (wide_pullback_jointly_monic HP
                (rmod_by_element R P x) (rmod_by_element R P y) Hd
                (rig_one (ring_rig R))) as Hone.
  simpl in Hone.
  rewrite (rm_smul_one P x), (rm_smul_one P y) in Hone.
  exact Hone.
Qed.

Lemma wpull_elem_maps_agree (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) :
  ∀ i j : I,
    @compose (RMod R) _ _ _ (g i) (rmod_by_element R (B i) (b i))
      ≈ @compose (RMod R) _ _ _ (g j) (rmod_by_element R (B j) (b j)).
Proof using B I R g zz.
  intros i j r; simpl.
  rewrite (rm_map_smul (g i) r (b i)), (rm_map_smul (g j) r (b j)).
  now rewrite (Hb i j).
Qed.

(* The element of the apex determined by a compatible family of
   elements: the mediator applied to the unit of R. *)
Definition wpull_elem (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) :
  carrier (cmon_setoid P) :=
  cmon_map (rm_hom (unique_obj
     (wpull_ump HP (fun i => rmod_by_element R (B i) (b i))
        (wpull_elem_maps_agree b Hb))))
    (rig_one (ring_rig R)).

Lemma wpull_elem_proj (b : ∀ i : I, carrier (cmon_setoid (B i)))
  (Hb : ∀ i j : I, cmon_map (rm_hom (g i)) (b i)
                     ≈ cmon_map (rm_hom (g j)) (b j)) (i : I) :
  cmon_map (rm_hom (p i)) (wpull_elem b Hb) ≈ b i.
Proof using B HP I P R g p zz.
  unfold wpull_elem.
  transitivity (cmon_map (rm_hom (rmod_by_element R (B i) (b i)))
                  (rig_one (ring_rig R))).
  - exact (unique_property
             (wpull_ump HP (fun k => rmod_by_element R (B k) (b k))
                (wpull_elem_maps_agree b Hb)) i (rig_one (ring_rig R))).
  - simpl; apply rm_smul_one.
Qed.

(* A compatible family of bilinear maps into the [B i] IS a bilinear map
   into the apex -- the elementwise content of preservation. *)
Program Definition wpull_bilin_med
  (β : ∀ i : I, RBilinear V V' (B i))
  (Hβ : ∀ (i j : I) (v : carrier (cmon_setoid V))
          (w : carrier (cmon_setoid V')),
          cmon_map (rm_hom (g i)) (rbl_map (β i) v w)
            ≈ cmon_map (rm_hom (g j)) (rbl_map (β j) v w)) :
  RBilinear V V' P := {|
  rbl_map := fun v w =>
    wpull_elem (fun i => rbl_map (β i) v w) (fun i j => Hβ i j v w)
|}.
Next Obligation.
  intros β Hβ v v' Hv w w' Hw.
  apply wpull_elem_unique; intro i.
  rewrite !wpull_elem_proj.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros β Hβ v v' w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (cmon_map_plus (rm_hom (p i))).
  rewrite !wpull_elem_proj.
  apply rbl_add_l.
Qed.
Next Obligation.
  intros β Hβ v w w'.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (cmon_map_plus (rm_hom (p i))).
  rewrite !wpull_elem_proj.
  apply rbl_add_r.
Qed.
Next Obligation.
  intros β Hβ r v w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (rm_map_smul (p i)).
  rewrite !wpull_elem_proj.
  apply rbl_smul_l.
Qed.
Next Obligation.
  intros β Hβ r v w.
  apply wpull_elem_unique; intro i.
  rewrite wpull_elem_proj.
  rewrite (rm_map_smul (p i)).
  rewrite !wpull_elem_proj.
  apply rbl_smul_r.
Qed.

End AtAFamily.

Theorem Bilin_PreservesWidePullbacks : PreservesWidePullbacks (Bilin V V').
Proof using R V V'.
  intros I B zz g Hm P p HP.
  unshelve refine (@Build_IsWidePullback Sets I _ _ _ _ _ _ _).
  - (* the legs agree after the common codomain *)
    intros i j β v w.
    exact (wpull_commutes HP i j (rbl_map β v w)).
  - (* the universal property *)
    intros Q q Hq.
    unshelve refine {| unique_obj := {| morphism := fun x : carrier Q =>
      wpull_bilin_med g HP (fun i => q i x)
        (fun i j v w => Hq i j x v w) |} |}.
    + (* the mediator respects [≈] on Q *)
      intros x y Hxy v w.
      apply (wpull_elem_unique g HP); intro i; simpl.
      rewrite !(wpull_elem_proj g HP).
      exact (proper_morphism (q i) x y Hxy v w).
    + (* it lifts every leg *)
      intros i x v w.
      exact (wpull_elem_proj g HP (fun k => rbl_map (q k x) v w)
               (fun k l => Hq k l x v w) i).
    + (* and is the only one *)
      intros u Hu x v w.
      apply (wpull_elem_unique g HP); intro i; simpl.
      rewrite (wpull_elem_proj g HP).
      symmetry; exact (Hu i x v w).
Qed.

End BilinWidePullbacks.

(** ** 7. The spanning solution set for [Bilin V V'] *)

Section TensorSolutionSet.

Context {R : RingObject}.
Context (V V' : RModObject R).
Context `{HWP : @HasWidePullbacks (RMod R)}.

(* Mac Lane's "it suffices to consider the bilinear β which span C":
   the solution set indexed by the spanning bilinear maps out of V × V'.
   The second hypothesis is discharged by [Bilin_PreservesWidePullbacks]
   above; the first is the open one -- see the header. *)
Definition tensor_solution_set (X : Sets) : SolutionSet (Bilin V V') X :=
  @spanning_solution_set (RMod R) Sets (Bilin V V') HWP
    (Bilin_PreservesWidePullbacks V V') X.

Definition tensor_esols : ElementSolutionSet (Bilin V V') :=
  esols_of_sols (Bilin V V') (tensor_solution_set SetsOne).

(* The index, the objects and the elements survive both repackagings on
   the nose. *)
Example tensor_esol_index :
  esol_index tensor_esols = SpanningArrowsOutOf (Bilin V V') SetsOne
  := eq_refl.

Example tensor_esol_obj (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_obj tensor_esols i = `1 i := eq_refl.

Example tensor_esol_elem (i : SpanningArrowsOutOf (Bilin V V') SetsOne) :
  esol_elem tensor_esols i = `1 (`2 i) ttt := eq_refl.

End TensorSolutionSet.

(** ** 8. Exercise 3: the balanced tensor is spanned by its generators *)

Section AbGenerated.

Context {A : AbObject}.
Context (P : carrier (cmon_setoid A) → Type).

(* The subgroup of an abelian group generated by a [Type]-valued
   predicate.  The same four closure constructors as [MGen], with
   [abgen_neg] in place of [mgen_smul]: there is no scalar here, so
   negation cannot be derived from (−1)· and must be a constructor of
   its own. *)
Inductive ABGen : carrier (cmon_setoid A) → Type :=
  | abgen_base : ∀ a, P a → ABGen a
  | abgen_resp : ∀ a b, a ≈ b → ABGen a → ABGen b
  | abgen_zero : ABGen (cmon_zero A)
  | abgen_plus : ∀ a b, ABGen a → ABGen b → ABGen (cmon_plus A a b)
  | abgen_neg  : ∀ a, ABGen a → ABGen (ab_neg A a).

(* Leastness, against a bare closed predicate rather than against a
   record: Instance/Ab/DirectedColimit.v:273's [AbSubgroup] is the
   in-tree record, but its own generated notion [InGen] (:381) is
   generated by a finite LIST, so nothing there is reused and that file
   is deliberately not [Require]d here. *)
Fixpoint abgen_least (Q : carrier (cmon_setoid A) → Type)
  (Hresp : ∀ a b, a ≈ b → Q a → Q b)
  (Hzero : Q (cmon_zero A))
  (Hplus : ∀ a b, Q a → Q b → Q (cmon_plus A a b))
  (Hneg : ∀ a, Q a → Q (ab_neg A a))
  (HP : ∀ a, P a → Q a)
  (a : carrier (cmon_setoid A)) (D : ABGen a) {struct D} : Q a :=
  match D in ABGen a' return Q a' with
  | abgen_base a Ha     => HP a Ha
  | abgen_resp a b H D' =>
      Hresp a b H (abgen_least Q Hresp Hzero Hplus Hneg HP a D')
  | abgen_zero          => Hzero
  | abgen_plus a b D1 D2 =>
      Hplus a b (abgen_least Q Hresp Hzero Hplus Hneg HP a D1)
                (abgen_least Q Hresp Hzero Hplus Hneg HP b D2)
  | abgen_neg a D'      =>
      Hneg a (abgen_least Q Hresp Hzero Hplus Hneg HP a D')
  end.

End AbGenerated.

Section BalancedSpanning.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Definition bal_image {A : AbObject} (β : BalBiadditive N M A)
  (x : carrier (cmon_setoid A)) : Type :=
  { n : carrier (cmon_setoid (rm_ab N)) &
    { m : carrier (cmon_setoid (rm_ab M)) & bal_map β n m ≈ x } }.

Definition BalSpanning {A : AbObject} (β : BalBiadditive N M A) : Type :=
  ∀ x : carrier (cmon_setoid A), ABGen (bal_image β) x.

(* Mac Lane's Exercise 3, second clause: "A ⊗_R B is spanned, as an
   abelian group, by the elements a ⊗ b."  Four cases, by induction on
   [bsum]; the [bs_neg] case needs [abgen_neg] because an abelian group
   carries no scalar to derive it from. *)
Theorem bal_gen_spanning : BalSpanning (@bal_gen X N M).
Proof using M N X.
  intro s; induction s as [n m| |s1 IH1 s2 IH2|s IH].
  - refine (abgen_base (bal_image (@bal_gen X N M)) _ _).
    exists n, m; reflexivity.
  - exact (abgen_zero (bal_image (@bal_gen X N M))).
  - exact (abgen_plus (bal_image (@bal_gen X N M)) _ _ IH1 IH2).
  - exact (abgen_neg (bal_image (@bal_gen X N M)) _ IH).
Qed.

End BalancedSpanning.

(** ** 9. Exercise 3: base change along a ring homomorphism *)

Section BalBaseChange.

Context {T R : RingObject}.
Context (phi : T ~{Rng}~> R).
Context (N : RModObject (Ring_op R)).
Context (M : RModObject R).

(* The two modules, read over T by restriction of scalars.  Neither
   changes the underlying abelian group, so the generators of the two
   balanced tensors are indexed by the SAME pair of carriers and the
   comparison below needs no transport. *)
Definition bal_right_T : RModObject (Ring_op T) :=
  RestrictObj (RigHom_op phi) N.

Definition bal_left_T : RModObject T := RestrictObj phi M.

(* The R-balanced generator, read as a T-balanced map: the only clause
   that changes is the balance rule, which is the R-rule at the scalar
   [phi t]. *)
Definition bal_change_bil :
  BalBiadditive bal_right_T bal_left_T (@BalTensor R N M).
Proof using M N R T phi.
  unshelve refine (@Build_BalBiadditive T bal_right_T bal_left_T
                     (@BalTensor R N M) (@bs_gen R N M) _ _ _ _).
  - intros n n' Hn m m' Hm; exact (@be_gen R N M n n' m m' Hn Hm).
  - intros n n' m; exact (@be_add_l R N M n n' m).
  - intros n m m'; exact (@be_add_r R N M n m m').
  - intros t n m; exact (@be_balance R N M (rig_map phi t) n m).
Defined.

(* The comparison homomorphism A ⊗_T B → A ⊗_R B. *)
Definition bal_change :
  @BalTensor T bal_right_T bal_left_T ~{Ab}~> @BalTensor R N M :=
  bal_med bal_change_bil.

(* Generators go to generators, on the nose. *)
Example bal_change_gen (n : carrier (cmon_setoid (rm_ab N)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map bal_change (@bs_gen T bal_right_T bal_left_T n m)
    = @bs_gen R N M n m := eq_refl.

(* Mac Lane's "examine the relation": the comparison is SURJECTIVE --
   A ⊗_R B is a quotient of A ⊗_T B -- by induction on the formal sums
   of the target. *)
Theorem bal_change_surjective : AbSurjective bal_change.
Proof using M N R T phi.
  intro t; induction t as [n m| |t1 IH1 t2 IH2|t IH].
  - exists (@bs_gen T bal_right_T bal_left_T n m); reflexivity.
  - exists (@bs_zero T bal_right_T bal_left_T); reflexivity.
  - destruct IH1 as [s1 H1]; destruct IH2 as [s2 H2].
    exists (@bs_plus T bal_right_T bal_left_T s1 s2).
    exact (be_plus H1 H2).
  - destruct IH as [s H].
    exists (@bs_neg T bal_right_T bal_left_T s).
    exact (be_neg H).
Qed.

(* And it IS [bal_med] of the R-balanced generator read over T: any
   homomorphism carrying generators to generators equals it. *)
Theorem bal_change_is_med
  (f : @BalTensor T bal_right_T bal_left_T ~{Ab}~> @BalTensor R N M)
  (Hf : ∀ (n : carrier (cmon_setoid (rm_ab N)))
          (m : carrier (cmon_setoid (rm_ab M))),
          cmon_map f (@bs_gen T bal_right_T bal_left_T n m)
            ≈ @bs_gen R N M n m) :
  f ≈ bal_change.
Proof using M N R T phi. exact (bal_med_unique bal_change_bil f Hf). Qed.

End BalBaseChange.
