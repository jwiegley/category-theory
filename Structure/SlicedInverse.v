Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Determination.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.One.

(** * Sliced adjoint inverses: Mac Lane's Proposition V.9.1, abstractly

    nLab: https://ncatlab.org/nlab/show/topological+concrete+category
    nLab: https://ncatlab.org/nlab/show/subspace+topology
    nLab: https://ncatlab.org/nlab/show/quotient+space
    nLab: https://ncatlab.org/nlab/show/over+category

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, SS V.9, read from the page images: the
          subspace construction (book pp. 132-133, PDF pp. 141-142;
          catalog id maclane:V.9:construction2), Proposition 1 (book
          p. 133, PDF p. 142; maclane:V.9:prop1), the quotient
          construction (book pp. 133-134, PDF pp. 142-143;
          maclane:V.9:construction3), and the one sentence stating the
          dual of Proposition 1 (book p. 134, PDF p. 143), which is the
          first clause of maclane:V.9:remark2, #458's catalog item.  The
          book numbers Proposition 1 and none of the constructions or
          remarks; the catalog ids are names, not book numbering.
    Book: Fong and Spivak, "Seven Sketches in Compositionality", CUP 2019,
          SS 7.3.2, Exercise 7.32 (printed p. 236, PDF p. 248) --
          7sketches:7.3.2:ex7.32.
    Book: Adamek, Herrlich and Strecker, "Abstract and Concrete
          Categories: The Joy of Cats", Wiley 1990, SS 21 (topological
          categories), cited through nLab.

    ** Background

    Mac Lane's SS V.9 recasts two constructions of point-set topology as
    adjunctions over the underlying-set functor [G : Top ⟶ Set], sliced
    at a space.  Over a fixed space [x], the induced functor
    [G↓x : (Top↓x) ⟶ (Set↓Gx)] has a right adjoint [L] that topologizes
    a function [t : S ⟶ Gx] by declaring open exactly the preimages
    [t⁻¹U] of the open sets [U] of [x] (the subspace construction).  When
    [S] is a subset of [Gx] that is the subspace topology, and the book
    observes: "(G↓X)∘L = Id; L is a 'right-adjoint-right-inverse' to
    (G↓X)".  By the naming of SS IV.4, where an adjunction with counit
    the identity makes the left adjoint a left-adjoint-left-inverse, that
    is the adjunction [G↓x ⊣ L] with counit the identity, read from [L];
    the record below states it so.  Mac Lane stresses that the universal
    property concerns arbitrary spaces mapping in, not only other
    subspaces.  Under a space the dual holds: [x↓G] has a left adjoint
    that gives [S] the sets with open preimage -- the quotient, or
    identification, topology when [t] is surjective -- "with unit the
    identity map, so M is left-adjoint-right-inverse to X↓G" (the
    quotient construction).  Between the two the book states, verbatim
    from the page:

      "Proposition 1.  If G: C→D is a faithful functor, if D has
       equalizers, and if, for each x ∈ C, (G↓x): (C↓x)→(D↓Gx) has a
       right-adjoint-right-inverse L, then C has equalizers."

    Its proof builds the equalizer as the lift [L] of the downstairs one,
    which explains the classical equalizer of two maps of spaces -- the
    points where they agree, with the subspace topology -- without
    mentioning points.  The dual is one sentence of the book, "Now
    Proposition 1 was proved just from the axioms for a category, so its
    dual is also true" (book p. 134): coequalizers from sliced
    left-adjoint-right-inverses.  nLab's "subspace topology" records the
    same equalizer computation and identifies the subspace inclusions
    with the regular monomorphisms of Top; its "quotient space" calls the
    dual construction the final, or strong, topology.  Seven Sketches'
    Exercise 7.32 is the elementary side of the subspace construction:
    the open sets of [Y ⊆ X] are the traces [B ∩ Y] of the open sets [B]
    of [X], and the inclusion is continuous.

    The shape has a general theory.  A functor [U : C ⟶ D] along which
    every family of maps [f_i : X ⟶ U S_i] out of an object of [D] has an
    initial lift -- informally the "smallest topology rendering the f_i
    continuous" -- is a topological functor, and [C] a topological
    concrete category over [D]; the forgetful functor from Top to Set is
    the paradigm, every topological functor is faithful (Adamek, Herrlich
    and Strecker, Theorem 21.3), and the notion is self-dual, so such a
    [C] carries final structures as well (nLab, "topological concrete
    category").  Read against that definition, Mac Lane's hypothesis is
    the one-arrow case: a sliced right adjoint at [(S; t)] is a universal
    lift of the single map [t], and the right-inverse clause asks that the
    lift sit over [S] on the nose -- the equation [U(T) = X] of nLab's
    definition of an initial lift, an EXISTENCE condition carried by [S]
    itself.  That such lifts are UNIQUE, literally and not up to
    isomorphism, is a separate condition, which nLab attributes to
    Adamek, Herrlich and Strecker and identifies with [U] being amnestic;
    a chosen right-adjoint-right-inverse does not supply it (argued, not
    built: a faithful functor can have one on every slice without being
    amnestic -- spaces carrying an inert bit that the maps ignore, lifted
    with the bit 0).  This file measures how little of that Proposition 1
    consumes.

    ** What is delivered

    - [Sliced G a : (A ̸ a) ⟶ (X ̸ G a)] and
      [Cosliced G a : (a ̸co A) ⟶ (G a ̸co X)], Mac Lane's [G↓a] and
      [a↓G] on Construction/Slice.v's [Slice] and [Coslice]: an object
      [(d; h)] goes to [(G d; fmap[G] h)], an arrow [m] to [fmap[G] m].
    - [RightAdjointRightInverse S]: a right adjoint [rari_right], the
      adjunction [rari_adj : S ⊣ rari_right], the Leibniz object equation
      [rari_obj c : S (rari_right c) = c], and
      [rari_counit c : counit c ≈ id_cast (rari_obj c)].  "Counit the
      identity" is not an equation between arrows of one hom-set until
      the object equation is supplied, so this is Adjunction/LeftInverse.v's
      design crux one parameter over, and the record is
      [LeftAdjointLeftInverse] with the adjoint moved into the parameter:
      the bridges [rari_lali] and [lali_rari], with both round trips at
      [eq_refl], are in Structure/SlicedInverse/Strict.v.
    - The pointwise cores.  [sliced_equalizer]: given one parallel pair
      [f g : x ~> y], one downstairs equalizer [E] of [fmap[G] f] and
      [fmap[G] g] at [(S, s)], ONE couniversal arrow [U] from
      [Sliced G x] to the slice object [(S; s)], and [Faithful G], the
      arrow [sliced_eq_arrow : sliced_eq_obj ~> x] -- Mac Lane's
      [Lt : Ls ⟶ x] -- is an equalizer of [f] and [g].
      [cosliced_coequalizer] is the dual, over a universal arrow from
      [(Q; q)] to [Cosliced G y], proved directly.
    - The book forms.  [equalizers_from_sliced_right_adjoints] (any right
      adjoints [R a] of the [Sliced G a]) and
      [equalizers_from_sliced_RARI], which is Proposition 1 and is the
      former applied to [rari_right] and [rari_adj];
      [coequalizers_from_sliced_left_adjoints], the dual of Proposition 1
      over whole left adjoints.  The dual over left-adjoint-right-inverses,
      Theory/Equivalence/Strict.v's [LeftAdjointRightInverse], is
      Structure/SlicedInverse/Strict.v's [coequalizers_from_sliced_LARI].
    - What the right-inverse clause buys: [rari_preserves], [G] of the
      lifted equalizer is an equalizer of [fmap[G] f] and [fmap[G] g] (its
      object is [S] up to the Leibniz [rari_over], its arrow [s] up to
      that cast, [rari_arrow_over]); [equalizers_from_sliced_RARI_preserved]
      states it for every equalizer that [equalizers_from_sliced_RARI]
      builds.  The dual, [lari_preserves], is in the satellite.
    - [adj_unit_universal_op]: the unit of an adjunction as a universal
      arrow, read off Adjunction/Determination.v's
      [adj_counit_couniversal] at Adjunction/Opposite.v's
      [Opposite_Adjunction]; the coequalizer book form takes its universal
      arrow from it.
    - [prop1_needs_faithfulness], below.

    ** Where each hypothesis is spent, measured

    The right-inverse clause is not used by Proposition 1: the body of
    [equalizers_from_sliced_RARI] names [rari_right] and [rari_adj] and
    neither [rari_obj] nor [rari_counit], and the theorem it applies,
    [equalizers_from_sliced_right_adjoints], has no right-inverse
    hypothesis at all.  Whole adjoints are not used either: the pointwise
    core takes a single couniversal arrow, at the one slice object
    [(S; s)] that the downstairs equalizer supplies, and the book form
    obtains it from the counit by [adj_counit_couniversal] and consults
    the adjunction nowhere else.  The same holds of the two coequalizer
    forms, which name only [lari_left]/[lari_adj] or the given [L] and
    [adjL].

    Faithfulness is spent in exactly one step per variance, the fork
    equation.  It is a section variable ([GF]) of [SlicedEqualizer] and of
    [CoslicedCoequalizer].  [sliced_desc] and [cosliced_desc] -- the
    existence AND the uniqueness of the mediating arrow -- close under
    [Proof using E U], and their About readbacks carry no [Faithful]
    argument.  [sliced_fork] and [cosliced_cofork] need
    [Proof using E U GF]: on a scratch copy with [Proof using E U] each is
    refused with "The following section variable is used but not
    declared: GF."  So the lift's descent comes from the downstairs
    equalizer and the couniversal property alone, and faithfulness is
    what proves that the lifted arrow forks.

    ** Faithfulness cannot be dropped

    [prop1_needs_faithfulness] refutes Proposition 1 with the
    faithfulness hypothesis deleted, quantified over all [A], [X] and [G]
    at one universe instance.  The countermodel is
    [Erase Parallel : Parallel ⟶ _1] (Instance/Parallel.v,
    Instance/One.v).  Every slice of [Parallel] has the terminal object
    [(a; id)], and [erase_slice_RARI] makes the functor constant at it a
    right-adjoint-right-inverse of each [Sliced (Erase Parallel) a] --
    the object equation is one case analysis over the slice of [_1], and
    the counit condition holds because that slice is thin
    ([slice_one_hom_eq]).  [_1] has equalizers ([One_HasEqualizers]).  But
    the pair [par_arrow_one], [par_arrow_two] has no fork at all
    ([parallel_pair_unforked]), so [Parallel] has no equalizers
    ([Parallel_no_equalizers]), and [Erase Parallel] is not faithful
    ([Erase_Parallel_not_faithful]).  [sliced_RARI_without_faithfulness]
    packages the four facts.  The dual is the satellite's
    [prop1_dual_needs_faithfulness].

    ** Strengths

    Holding at [eq_refl], as [Example]s: [Sliced_fobj], [Sliced_fmap],
    [Cosliced_fobj], [Cosliced_fmap]; [adj_unit_universal_op_obj] and
    [adj_unit_universal_op_arrow] (the universal arrow IS the unit, as
    Adjunction/Determination.v's counit readback has it); [rari_eq_obj]
    and [rari_eq_arrow] (the pointwise equalizer built from a
    right-adjoint-right-inverse IS [rari_right L (S; s)]);
    [equalizers_from_sliced_RARI_obj] and
    [equalizers_from_sliced_RARI_arrow] (the same at the [HasEqualizers]
    level), and [coequalizers_from_sliced_left_adjoints_obj] and
    [coequalizers_from_sliced_left_adjoints_arrow].  Twelve in all.  The
    book forms read the downstairs (co)equalizer by projections
    rather than by a [match] so that those readbacks reach [eq_refl]:
    written with [destruct] on the downstairs equalizer instead, the same
    book form has its object readback refused at [eq_refl] ("cannot
    unify", compiled out of tree), the stdlib [sigT] having no
    definitional eta.

    Leibniz but not [eq_refl]: [rari_over : G (`1 (rari_right L (S; s)))
    = S], which is [f_equal projT1] of the field [rari_obj]; at a variable
    [L] the field is its only source.  Also Leibniz, by [destruct] on the
    equation: [slice_id_cast_1], the first component of a slice arrow
    transported by [id_cast] is the transport of first components, a
    Leibniz equation between arrows at a variable equation, of the kind
    Construction/Quotient.v's [id_cast_refl] already states.  Up to [≈]:
    [rari_arrow_over], the fork equations, and the transported arrows.
    [rari_preserves] is data assembled by [IsEqualizer_transport] from
    [rari_over] and [rari_arrow_over], and
    [equalizers_from_sliced_RARI_preserved] reaches it through the
    [eq_refl] readbacks, with no further cast.  Nothing is claimed about
    the mediating arrow beyond its unique existence.

    The file has six [Defined] (counted by token): [sliced_desc],
    [cosliced_desc], [IsEqualizer_transport], the second obligation of
    [One_HasEqualizers], [erase_slice_adj] and [erase_slice_RARI].  Each
    carries data (a mediating arrow, an equalizer, an adjunction, a
    record) and is kept [Defined] by the data convention; none is
    load-bearing, measured by flipping all six, together with the
    satellite's four, to [Qed] in a scratch copy, which compiles both
    files.

    ** Universes, measured by About on every constant

    [Sliced@{oA hA oX hX u u0 u1 u2}] and [Cosliced] keep the categories
    at their own levels, [A : Category@{oA hA hA}] and
    [X : Category@{oX hX hX}].  Their blocks carry no equation: the bound
    [hA <= hX] that [G : A ⟶ X] itself imposes, and one strict bound per
    slice instance ([hA < u], [hX < u0]), which is Construction/Slice.v's
    own [u2 < u1] on [Slice] and on [Coslice] alike.  The four readbacks
    have the same shape.

    Every other constant over two categories binds them at ONE hom level,
    [A : Category@{oA h h}] and [X : Category@{oX h h}], in the BINDER and
    with no equation in any block.  The identification is inherited, and
    which donor forces it was measured by isolation: a section declaring
    [hA] and [hX] apart, one [Context] line varied, and a trivial
    [Example] read back by About.  The couniversal arrow
    [CouniversalArrow ((S; s)) (Sliced G x)] alone prints [hA = hX]
    (Theory/Universal/Arrow/Dual.v's [CouniversalArrow] carries the
    equation [u0 = u2] in its own block), [Faithful G] alone prints it
    (Theory/Functor.v's [Faithful] binds both categories at one hom level),
    and a sliced adjunction [Sliced G x ⊣ R] prints it (two functors in
    opposite directions already do).  [Sliced G x] alone and
    [IsEqualizer] alone print only [hA <= hX], and so does the DUAL
    arrow: [UniversalArrow ((Q; q)) (Cosliced G y)] alone prints no
    equation.  So the equalizer core is tied by two independent donors,
    the coequalizer core by faithfulness only, and the book forms by the
    adjunctions as well; all of them inherited and none introduced here.
    At Instance/Top/Forgetful.v's [Top_Forget] the two hom levels
    coincide anyway ([Top@{h o}] and [Sets@{h so}] both have homs at
    [h]).

    One identification sits in the universe INSTANCES rather than in any
    block, and is disclosed here.  Wherever the two hom levels coincide,
    the two slice-auxiliary universes of [Sliced] and [Cosliced] (the
    [u] and [u0] of [hA < u] and [hX < u0], one per slice) are
    instantiated at one universe: [equalizers_from_sliced_RARI] reads
    [Sliced@{oA h oX h u u u5 u6}], [sliced_equalizer] and
    [cosliced_coequalizer] read [Sliced@{oA h oX h u3 u3 u0 u}] and its
    [Cosliced] twin, and the refutation below reads
    [Sliced@{u4 u5 u2 u5 u3 u3 u u0}].  No donor forces it: a trivial
    [Example] over [Sliced G x] ALONE, in a section binding both
    categories at one hom level [h], already reads back
    [Sliced@{oA h oX h u u u0 u1}] (About, out of tree), and with the hom
    levels apart [UniversalArrow ((Q; q)) (Cosliced G y)] alone keeps
    both universes; so the two, which then carry the same single bound
    [h < _], are merged when this file's constants are elaborated.  It
    costs nothing where it was measured: Instance/Top/Subspace.v's
    [subspace_RARI] and [quotient_LARI] read [Sliced@{so o so o u0 u0 so
    so}] and [Cosliced@{so o so o u0 u0 so so}] and feed both book forms,
    and the instantiation at [Top_Forget] typechecks.

    [RightAdjointRightInverse@{oA oC h u u0}] has one hom level [h] in the
    binder, forced by its first field: with [hA < hC] declared, a record
    holding only [rari_right : C ⟶ A] beside the parameter [S : A ⟶ C] is
    refused ("Cannot enforce hA = ... because hA < hC <= ...").  Its one
    strict bound [h < u] is Theory/Adjunction.v's [Adjunction] class's own
    [h1 < so], measured by adding the fields one at a time: [rari_right]
    alone leaves the block empty, and [rari_adj] brings [h < u].

    Across the 73 constants of this file (Print Module, the record, its
    constructor and projections, and every [Program] obligation) the
    About log has zero word-bounded [Set] and no block carries an
    equation; in every block whose constant binds categories, each strict
    bound relates a hom level to an auxiliary universe that no category
    binder names.  The witness [One_HasEqualizers] is annotated for a
    measured reason (and the satellite's [One_HasCoequalizers] likewise):
    unannotated it minimizes to [HasEqualizers@{u Set} 1] (compiled out of
    tree), which would confine [prop1_needs_faithfulness] to [Set]-homed
    categories; annotated [@{o h}] it is [HasEqualizers@{o h} _1@{o h h}].
    [prop1_needs_faithfulness@{u u0 u1 u2 u3 u4 u5}] quantifies over
    [A : Category@{u4 u5 u5}] and [X : Category@{u2 u5 u5}] with the one
    strict bound [u5 < u3].  [Parallel@{u u0}] carries no [Set] even
    though its object and arrow types are [Set]-sorted inductives.

    ** Route and cost

    Closure: 41 [Category.*] modules excluding this file ([Print
    Libraries] on its [Require] list).  Dropping each [Require] alone,
    Adjunction/Determination.v costs 4 at the margin,
    Construction/Slice.v, Construction/Quotient.v,
    Structure/Equalizer/Fork.v and Structure/Coequalizer.v 1 each, and the
    other eleven 0.  Two constants are rebuilt rather than consumed, each
    on a measurement against that list:

      - [adj_unit_universal_op] has the statement of
        Adjunction/Representability.v's [adj_unit_universal] and the same
        two [eq_refl] readbacks; requiring that module would add 12
        modules (41 to 53).
      - [IsEqualizer_transport] moves an equalizer along a Leibniz
        equation of apexes; Adjunction/CokernelPair.v's
        [IsEqualizer_along_iso] (an isomorphism of apexes, closed [Qed])
        would serve and would add 20 (41 to 61).

    The strict-inverse half -- the bridges to Adjunction/LeftInverse.v
    and the LARI form of the dual -- is the satellite
    Structure/SlicedInverse/Strict.v, because Theory/Equivalence/Strict.v
    would add 14 modules here (41 to 55; Adjunction/LeftInverse.v alone
    12) and those constants are its only consumers.  The coequalizer
    core is proved directly rather than as the op reading of the
    equalizer core: [Slice (A^op) a] and [(Coslice A a)^op] orient the
    triangle equation oppositely ([`2 y ∘ f ≈ `2 x] against
    [`2 y ≈ f ∘ `2 x]), so that route would need a transport functor --
    argued, not measured.

    [#[local] Obligation Tactic := idtac] is set file-wide, as in
    Adjunction/LeftInverse.v and Theory/Equivalence/Strict.v, and every
    obligation is discharged by hand.

    ** Prior art, measured

    No declaration named [RightAdjointRightInverse] existed: a
    whole-word search before this file found only prose in the header of
    Adjunction/Diagonal/Connected.v, which used the name for a different
    notion and is corrected, in place, alongside this file.
    [LeftAdjointLeftInverse] (#376) and
    [LeftAdjointRightInverse] (#377) existed and set the convention
    followed.  No functor between slices is induced by a functor between
    the ambient categories on the [Slice] encoding:
    Construction/Slice/Pullback.v's [Bang_Functor] (post-composition) and
    [Star_Functor] (base change) move along an arrow of ONE category.
    Construction/Comma/Functorial.v's [Comma_reindex] does give the
    sliced functor in comma form, [(Id[A] ↓ =(a)) ⟶ (Id[X] ↓ =(G a))],
    with its object readback at [eq_refl] (compiled out of tree); [Sliced]
    is stated on [Slice] directly because that is the encoding
    [CouniversalArrow] and the equalizer records are used with here.
    Structure/Limit/Creation.v's [CreatesLimit] is a different notion: it
    starts from a limit of [G ◯ K] and asks for its unique lift, whereas
    here the lift is SUPPLIED by the sliced adjoint and its uniqueness is
    not asserted.

    Collisions: none over the 82 names of this file and its satellite
    (every constant Print Module lists, less the [Program] obligations,
    plus the record and its constructor), by [find | xargs grep -lw] over
    every other [.v] file and instrument-checked on names known to be
    present.  The whole-word hits, measured with the probe registered, are
    three files: Instance/Top/Subspace.v (ten of the names) and
    Test/ProbeSubspace457.v (all 82, in its guard block), which use or
    cite these constants and declare none of the names, and the header prose
    of Adjunction/Diagonal/Connected.v named above (one name).  That is
    after three renames: [par_one] and [par_two] are
    Instance/Proset/Transform.v's and
    Theory/Natural/Transformation/Arrows.v's, and [point_adj] is
    Adjunction/LeftInverse.v's, which the satellite requires.

    ** Registration

    Nothing is registered for instance resolution: a
    right-adjoint-right-inverse is a chosen adjoint, passed explicitly, as
    Adjunction/LeftInverse.v and Theory/Equivalence/Strict.v rule for
    their records.  [Faithful] and the (co)equalizer structures are taken
    instance-implicitly, as their classes are.

    ** NOT DELIVERED

    - No concrete instance in this file.  The witnesses are
      Instance/Top/Subspace.v's, over Instance/Top/Prop.v's Prop-valued
      spaces: [subspace_RARI] and [quotient_LARI] (the subspace and
      quotient constructions, at [Sliced PForget X] and
      [Cosliced PForget X]), and [PTop_HasEqualizers] and
      [PTop_HasCoequalizers], built by [equalizers_from_sliced_RARI] and
      the satellite's [coequalizers_from_sliced_LARI]; Seven Sketches'
      Exercise 7.32 is there too.  At Instance/Top/Forgetful.v's
      [Top_Forget] the types line up -- compiled out of tree, with
      [Top_Forget_Faithful] supplied, [equalizers_from_sliced_RARI] there
      has type
      [HasEqualizers Sets@{h so} → (∀ a, RightAdjointRightInverse
      (Sliced Top_Forget a)) → HasEqualizers Top@{h o}] -- but no
      hypothesis is discharged there, and
      Instance/Top/Subspace/TypeValued.v records why the sliced
      adjunctions are not [Adjunction] records over the Type-valued
      [Top].
    - No converse (nothing here derives sliced adjoints from equalizers), no
      multi-arrow initial lifts, no products or general limits (catalog
      maclane:V.9:remark1, #458's), no uniqueness of a
      right-adjoint-right-inverse, no
      characterization of the functors that have one (the analogue of
      Exercise IV.4.4 for left-adjoint-left-inverses), and no readback of
      the mediating arrow against the adjunction's transpose.
    - No op-duality between the two halves; each is proved on its own. *)

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** ** The sliced functors [G/a] and [a/G] *)

(* Mac Lane's G↓a : (A↓a) ⟶ (X↓Ga), on this library's [Slice] encoding:
   an object (d; h : d ~> a) goes to (G d; G h), an arrow m to G m. *)
Program Definition Sliced@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) :
  @Slice A a ⟶ @Slice X (G a) := {|
  fobj := fun h => (G (`1 h); fmap[G] (`2 h));
  fmap := fun h k m => (fmap[G] (`1 m); _)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp.
  apply fmap_respects.
  exact (`2 m).
Qed.
Next Obligation.
  intros ? ? ? ? x y m m' Hm; simpl.
  apply fmap_respects.
  exact Hm.
Qed.
Next Obligation.
  intros ? ? ? ? x; simpl.
  apply fmap_id.
Qed.
Next Obligation.
  intros ? ? ? ? x y z m m'; simpl.
  apply fmap_comp.
Qed.

(* The dual, a↓G : (a↓A) ⟶ (Ga↓X), on the [Coslice] encoding. *)
Program Definition Cosliced@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) :
  @Coslice A a ⟶ @Coslice X (G a) := {|
  fobj := fun h => (G (`1 h); fmap[G] (`2 h));
  fmap := fun h k m => (fmap[G] (`1 m); _)
|}.
Next Obligation.
  intros; simpl.
  rewrite <- fmap_comp.
  apply fmap_respects.
  exact (`2 m).
Qed.
Next Obligation.
  intros ? ? ? ? x y m m' Hm; simpl.
  apply fmap_respects.
  exact Hm.
Qed.
Next Obligation.
  intros ? ? ? ? x; simpl.
  apply fmap_id.
Qed.
Next Obligation.
  intros ? ? ? ? x y z m m'; simpl.
  apply fmap_comp.
Qed.

Example Sliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Slice A a) :
  Sliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

Example Sliced_fmap@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h k : @Slice A a)
  (m : h ~> k) : `1 (fmap[Sliced G a] m) = fmap[G] (`1 m) := eq_refl.

Example Cosliced_fobj@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h : @Coslice A a) :
  Cosliced G a h = (G (`1 h); fmap[G] (`2 h)) := eq_refl.

Example Cosliced_fmap@{oA hA oX hX +} {A : Category@{oA hA hA}}
  {X : Category@{oX hX hX}} (G : A ⟶ X) (a : A) (h k : @Coslice A a)
  (m : h ~> k) : `1 (fmap[Cosliced G a] m) = fmap[G] (`1 m) := eq_refl.

(** ** Right-adjoint-right-inverses *)

(* [R] is a right-adjoint-right-inverse of [S] when [S ⊣ R] with counit the
   identity.  As in Adjunction/LeftInverse.v, "counit the identity" is the
   Leibniz object equation [S (R c) = c] together with the counit being
   [≈] the identity transported along it. *)
Record RightAdjointRightInverse@{oA oC h +} {A : Category@{oA h h}}
  {C : Category@{oC h h}} (S : A ⟶ C) : Type := {
  rari_right : C ⟶ A;
  rari_adj : S ⊣ rari_right;
  rari_obj (c : C) : S (rari_right c) = c;
  rari_counit (c : C) :
    @counit C A S rari_right rari_adj c ≈ id_cast (rari_obj c)
}.

Arguments rari_right {A C S} _.
Arguments rari_adj {A C S} _.
Arguments rari_obj {A C S} _ _.
Arguments rari_counit {A C S} _ _.

(** ** The unit of an adjunction as a universal arrow, by duality *)

(* Adjunction/Determination.v's [adj_counit_couniversal] read at the
   opposite adjunction.  Both readbacks below are [eq_refl]. *)
Definition adj_unit_universal_op@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) (c : D) : UniversalArrow c U :=
  adj_counit_couniversal (Opposite_Adjunction F U A) c.

Example adj_unit_universal_op_obj@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (c : D) :
  @arrow_obj _ _ c U (adj_unit_universal_op A c) = F c := eq_refl.

Example adj_unit_universal_op_arrow@{oC oD h +} {C : Category@{oC h h}}
  {D : Category@{oD h h}} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (c : D) :
  @arrow _ _ c U (adj_unit_universal_op A c) = @unit _ _ F U A c := eq_refl.

(** ** Proposition 1, pointwise *)

(* One parallel pair, its downstairs equalizer (S, s), and ONE couniversal
   arrow from [Sliced G x] to the object (S; s) of the slice over [G x]:
   no adjunction and no right-inverse clause.  Faithfulness is a section
   variable so that [Proof using] records which lemma spends it. *)
Section SlicedEqualizer.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {S : X} (s : S ~> G x).
Context (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s).
Context (U : CouniversalArrow ((S; s) : @Slice X (G x)) (Sliced G x)).
Context `{GF : @Faithful A X G}.

(* Mac Lane's L s and L t : L s ~> x. *)
Definition sliced_eq_obj : A := `1 (coarrow_obj U).

Definition sliced_eq_arrow : sliced_eq_obj ~> x := `2 (coarrow_obj U).

(* The fork equation: the only step that spends faithfulness. *)
Lemma sliced_fork : f ∘ sliced_eq_arrow ≈ g ∘ sliced_eq_arrow.
Proof using E U GF.
  apply (@fmap_inj _ _ G GF).
  rewrite !fmap_comp.
  pose proof (`2 (coarrow U)) as He; simpl in He.
  unfold sliced_eq_arrow.
  rewrite <- He.
  rewrite !comp_assoc.
  rewrite (fork_eq E).
  reflexivity.
Qed.

(* Descent: existence from the downstairs equalizer followed by the
   couniversal property, uniqueness from the couniversal property alone. *)
Definition sliced_desc {z : A} (h : z ~> x) (Hh : f ∘ h ≈ g ∘ h) :
  ∃! u : z ~> sliced_eq_obj, sliced_eq_arrow ∘ u ≈ h.
Proof using E U.
  assert (HGh : fmap[G] f ∘ fmap[G] h ≈ fmap[G] g ∘ fmap[G] h).
  { rewrite <- !fmap_comp. now rewrite Hh. }
  pose (D := eq_desc E (fmap[G] h) HGh).
  pose (k := (unique_obj D; unique_property D)
             : @hom (@Slice X (G x)) (Sliced G x (z; h)) (S; s)).
  pose (D' := ump_couniversal_arrows U (d:=(z; h)) k).
  unshelve eapply Build_Unique.
  - exact (`1 (unique_obj D')).
  - exact (`2 (unique_obj D')).
  - intros v Hv.
    pose (vv := (v; Hv) : @hom (@Slice A x) (z; h) (coarrow_obj U)).
    apply (uniqueness D' vv).
    simpl.
    apply (uniqueness D).
    rewrite comp_assoc.
    rewrite (`2 (coarrow U)).
    simpl.
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact Hv.
Defined.

Definition sliced_equalizer :
  IsEqualizer f g sliced_eq_obj sliced_eq_arrow :=
  {| fork_eq := sliced_fork; eq_desc := @sliced_desc |}.

End SlicedEqualizer.

Section CoslicedCoequalizer.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {Q : X} (q : G y ~> Q).
Context (E : IsCoequalizer (fmap[G] f) (fmap[G] g) Q q).
Context (U : UniversalArrow ((Q; q) : @Coslice X (G y)) (Cosliced G y)).
Context `{GF : @Faithful A X G}.

Definition cosliced_coeq_obj : A := `1 (@arrow_obj _ _ _ _ U).

Definition cosliced_coeq_arrow : y ~> cosliced_coeq_obj :=
  `2 (@arrow_obj _ _ _ _ U).

Lemma cosliced_cofork :
  cosliced_coeq_arrow ∘ f ≈ cosliced_coeq_arrow ∘ g.
Proof using E U GF.
  apply (@fmap_inj _ _ G GF).
  rewrite !fmap_comp.
  pose proof (`2 (@arrow _ _ _ _ U)) as He; simpl in He.
  unfold cosliced_coeq_arrow.
  rewrite He.
  rewrite <- !comp_assoc.
  rewrite (cofork E).
  reflexivity.
Qed.

Definition cosliced_desc {z : A} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : cosliced_coeq_obj ~> z, u ∘ cosliced_coeq_arrow ≈ h.
Proof using E U.
  assert (HGh : fmap[G] h ∘ fmap[G] f ≈ fmap[G] h ∘ fmap[G] g).
  { rewrite <- !fmap_comp. now rewrite Hh. }
  pose (D := coeq_desc E (fmap[G] h) HGh).
  assert (Hk : fmap[G] h ≈ unique_obj D ∘ q)
    by (symmetry; exact (unique_property D)).
  pose (k := (unique_obj D; Hk)
             : @hom (@Coslice X (G y)) (Q; q) (Cosliced G y (z; h))).
  pose (D' := ump_universal_arrows U (d:=(z; h)) k).
  unshelve eapply Build_Unique.
  - exact (`1 (unique_obj D')).
  - symmetry; exact (`2 (unique_obj D')).
  - intros v Hv.
    assert (Hv' : h ≈ v ∘ cosliced_coeq_arrow) by (symmetry; exact Hv).
    pose (vv := (v; Hv')
                : @hom (@Coslice A y) (@arrow_obj _ _ _ _ U) (z; h)).
    apply (uniqueness D' vv).
    simpl.
    apply (uniqueness D).
    rewrite <- comp_assoc.
    rewrite <- (`2 (@arrow _ _ _ _ U)).
    simpl.
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact Hv.
Defined.

Definition cosliced_coequalizer :
  IsCoequalizer f g cosliced_coeq_obj cosliced_coeq_arrow :=
  {| cofork := cosliced_cofork; coeq_desc := @cosliced_desc |}.

End CoslicedCoequalizer.

(** ** Proposition 1 and its dual, as stated *)

(* The downstairs equalizer is read out by projections, not by a [match],
   so that the object and arrow readbacks below hold at [eq_refl]. *)
Definition equalizers_from_sliced_right_adjoints@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (R : ∀ a : A, @Slice X (G a) ⟶ @Slice A a)
  (adjR : ∀ a : A, Sliced G a ⊣ R a) : @HasEqualizers A :=
  {| equalizer := fun x y f g =>
       let S := `1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g)) in
       let s := `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let E := `2 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let U := adj_counit_couniversal (adjR x) ((S; s) : @Slice X (G x)) in
       (sliced_eq_obj G s U;
        (sliced_eq_arrow G s U; sliced_equalizer G f g s E U)) |}.

(* Mac Lane's Proposition 1.  The right-inverse clause is not consulted:
   only [rari_right] and [rari_adj] occur in the body. *)
Definition equalizers_from_sliced_RARI@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) : @HasEqualizers A :=
  equalizers_from_sliced_right_adjoints G
    (fun a => rari_right (L a)) (fun a => rari_adj (L a)).

(* The equalizer built is L applied to the downstairs one, on the nose. *)
Example equalizers_from_sliced_RARI_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g)
    = `1 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example equalizers_from_sliced_RARI_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  `1 (`2 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g))
    = `2 (rari_right (L x)
            (`1 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g));
             `1 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(* The dual of Proposition 1, with whole left adjoints; its LARI form is
   Structure/SlicedInverse/Strict.v's [coequalizers_from_sliced_LARI]. *)
Definition coequalizers_from_sliced_left_adjoints@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) : @HasCoequalizers A :=
  {| coeq := fun x y f g =>
       let Q := `1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g)) in
       let q := `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let E := `2 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))) in
       let U := adj_unit_universal_op (adjL y) ((Q; q) : @Coslice X (G y)) in
       (cosliced_coeq_obj G q U;
        (cosliced_coeq_arrow G q U; cosliced_coequalizer G f g q E U)) |}.

Example coequalizers_from_sliced_left_adjoints_obj@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) {x y : A} (f g : x ~> y) :
  `1 (@coeq A (coequalizers_from_sliced_left_adjoints G L adjL) x y f g)
    = `1 (L y (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
               `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

Example coequalizers_from_sliced_left_adjoints_arrow@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasCoequalizers X}
  (L : ∀ a : A, @Coslice X (G a) ⟶ @Coslice A a)
  (adjL : ∀ a : A, L a ⊣ Cosliced G a) {x y : A} (f g : x ~> y) :
  `1 (`2 (@coeq A (coequalizers_from_sliced_left_adjoints G L adjL) x y f g))
    = `2 (L y (`1 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g));
               `1 (`2 (@coeq X HX _ _ (fmap[G] f) (fmap[G] g))))) :=
  eq_refl.

(** ** What the right-inverse clause adds *)

Lemma slice_id_cast_1@{o h +} {C : Category@{o h h}} {u : C}
  {p q : @Slice C u} (e : p = q) :
  `1 (@id_cast (@Slice C u) p q e)
    = @id_cast C (`1 p) (`1 q) (f_equal (@projT1 _ _) e).
Proof. destruct e; reflexivity. Qed.

(* An equalizer moved along a Leibniz equation of apexes. *)
Definition IsEqualizer_transport@{o h +} {C : Category@{o h h}}
  {a b : C} {f g : a ~> b} {q q' : C} {e : q ~> a} {e' : q' ~> a}
  (p : q' = q) :
  e' ≈ e ∘ id_cast p → IsEqualizer f g q e → IsEqualizer f g q' e'.
Proof.
  destruct p; simpl; intros He E.
  rewrite id_right in He.
  unshelve econstructor.
  - rewrite He; exact (fork_eq E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + exact (unique_obj (eq_desc E h Hh)).
    + rewrite He; exact (unique_property (eq_desc E h Hh)).
    + intros v Hv; apply (uniqueness (eq_desc E h Hh)).
      rewrite <- He; exact Hv.
Defined.

Section RARIPreserves.

Universes oA oX h.
Context {A : Category@{oA h h}} {X : Category@{oX h h}}.
Context (G : A ⟶ X).
Context {x y : A}.
Context (f g : x ~> y).
Context {S : X} (s : S ~> G x).
Context (E : IsEqualizer (fmap[G] f) (fmap[G] g) S s).
Context (L : RightAdjointRightInverse (Sliced G x)).

Definition rari_couniversal :
  CouniversalArrow ((S; s) : @Slice X (G x)) (Sliced G x) :=
  adj_counit_couniversal (rari_adj L) (S; s).

Example rari_eq_obj :
  sliced_eq_obj G s rari_couniversal = `1 (rari_right L (S; s)) := eq_refl.

Example rari_eq_arrow :
  sliced_eq_arrow G s rari_couniversal = `2 (rari_right L (S; s)) := eq_refl.

(* The lifted object sits over S: Leibniz, from the field [rari_obj]. *)
Definition rari_over : G (`1 (rari_right L (S; s))) = S :=
  f_equal (@projT1 _ _) (rari_obj L (S; s)).

Lemma rari_arrow_over :
  fmap[G] (`2 (rari_right L (S; s))) ≈ s ∘ id_cast rari_over.
Proof using Type.
  pose proof (`2 (@counit _ _ _ _ (rari_adj L) (S; s))) as H; simpl in H.
  rewrite <- H.
  apply compose_respects; [reflexivity|].
  transitivity (`1 (@id_cast (@Slice X (G x)) _ _ (rari_obj L (S; s)))).
  - exact (rari_counit L (S; s)).
  - rewrite (slice_id_cast_1 (rari_obj L (S; s))).
    reflexivity.
Qed.

(* G carries the lifted equalizer onto an equalizer of the images. *)
Definition rari_preserves :
  IsEqualizer (fmap[G] f) (fmap[G] g)
    (G (`1 (rari_right L (S; s)))) (fmap[G] (`2 (rari_right L (S; s)))) :=
  IsEqualizer_transport rari_over rari_arrow_over E.

End RARIPreserves.

(* The same at the [HasEqualizers] level: [G] preserves every equalizer
   that [equalizers_from_sliced_RARI] constructs. *)
Definition equalizers_from_sliced_RARI_preserved@{oA oX h +}
  {A : Category@{oA h h}} {X : Category@{oX h h}} (G : A ⟶ X)
  `{GF : @Faithful A X G} `{HX : @HasEqualizers X}
  (L : ∀ a : A, RightAdjointRightInverse (Sliced G a)) {x y : A}
  (f g : x ~> y) :
  IsEqualizer (fmap[G] f) (fmap[G] g)
    (G (`1 (@equalizer A (equalizers_from_sliced_RARI G L) x y f g)))
    (fmap[G] (`1 (`2 (@equalizer A (equalizers_from_sliced_RARI G L)
                         x y f g)))) :=
  rari_preserves G f g _ (`2 (`2 (@equalizer X HX _ _ (fmap[G] f) (fmap[G] g))))
    (L x).

(** ** Faithfulness cannot be dropped *)

(* [Parallel]'s two arrows have no fork at all, so [Parallel] has no
   equalizers; its erasure to [_1] is not faithful; and every other
   hypothesis of Proposition 1 holds there. *)
Definition par_arrow_one : ParX ~{Parallel}~> ParY := (true; ParOne).
Definition par_arrow_two : ParX ~{Parallel}~> ParY := (false; ParTwo).

Lemma parallel_pair_unforked {q : Parallel} (e : q ~> ParX) :
  par_arrow_one ∘ e ≈ par_arrow_two ∘ e → False.
Proof.
  destruct q, e as [b h].
  - inversion h; subst. simpl. discriminate.
  - destruct (ParHom_Y_X_absurd _ h).
Qed.

Definition Parallel_no_equalizers : @HasEqualizers Parallel → False :=
  fun H =>
    parallel_pair_unforked
      (`1 (`2 (@equalizer Parallel H _ _ par_arrow_one par_arrow_two)))
      (fork_eq
         (`2 (`2 (@equalizer Parallel H _ _ par_arrow_one par_arrow_two)))).

Lemma Erase_Parallel_not_faithful : Faithful (Erase Parallel) → False.
Proof.
  intros [inj].
  pose proof (inj _ _ par_arrow_one par_arrow_two eq_refl) as H.
  discriminate H.
Qed.

(* Annotated: unannotated, this witness minimizes its hom level to [Set]. *)
Program Definition One_HasEqualizers@{o h} : @HasEqualizers _1@{o h h} := {|
  equalizer := fun x y f g => (x; (id; {| fork_eq := _; eq_desc := _ |}))
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation.
  intros x y f g z h Hh.
  exists h.
  - destruct h; reflexivity.
  - intros v _; destruct h, v; reflexivity.
Defined.

Lemma slice_one_hom_eq@{o h +} (u : _1@{o h h}) (x y : @Slice _1@{o h h} u)
  (f g : x ~> y) : f ≈ g.
Proof. destruct f as [[] ?], g as [[] ?]; reflexivity. Qed.

Section EraseSlice.

Context (a : Parallel).

#[local] Notation B := (Erase Parallel).

(* The right adjoint of [Sliced B a] is constant at the terminal object
   (a; id) of the slice over [a]. *)
Program Definition erase_slice_right : @Slice _1 (B a) ⟶ @Slice Parallel a := {|
  fobj := fun _ => (a; id);
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros; intros ? ? ?; reflexivity. Qed.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; symmetry; apply id_left. Qed.

Program Definition erase_slice_hom_iso (h : @Slice Parallel a)
  (c : @Slice _1 (B a)) :
  @Isomorphism Sets
    {| carrier := @hom (@Slice _1 (B a)) (Sliced B a h) c;
       is_setoid := @homset (@Slice _1 (B a)) (Sliced B a h) c |}
    {| carrier := @hom (@Slice Parallel a) h (erase_slice_right c);
       is_setoid := @homset (@Slice Parallel a) h (erase_slice_right c) |} := {|
  to := {| morphism := fun _ => (`2 h; _) |};
  from := {| morphism := fun _ => (ttt; _) |}
|}.
Next Obligation. intros; apply id_left. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation. intros; destruct c as [[] []]; reflexivity. Qed.
Next Obligation. intros; intros ? ? ?; simpl; reflexivity. Qed.
Next Obligation.
  intros; intros [v Hv].
  change (`2 h ≈ v).
  rewrite <- Hv; apply id_left.
Qed.
Next Obligation. intros; intros [[] Hv]; reflexivity. Qed.

Definition erase_slice_adj : Sliced B a ⊣ erase_slice_right.
Proof.
  unshelve eapply
    (@Build_Adjunction' _ _ (Sliced B a) erase_slice_right erase_slice_hom_iso).
  - intros x y z f g; simpl.
    symmetry; exact (`2 g).
  - intros x y z f g.
    change (`2 x ≈ id ∘ `2 x).
    symmetry; apply id_left.
Defined.

Definition erase_slice_RARI : RightAdjointRightInverse (Sliced B a).
Proof.
  unshelve refine {| rari_right := erase_slice_right;
                     rari_adj := erase_slice_adj |}.
  - intros [[] []]; reflexivity.
  - intros c; apply slice_one_hom_eq.
Defined.

End EraseSlice.

Definition sliced_RARI_without_faithfulness :
  (∀ a : Parallel, RightAdjointRightInverse (Sliced (Erase Parallel) a))
  * @HasEqualizers _1
  * (Faithful (Erase Parallel) → False)
  * (@HasEqualizers Parallel → False) :=
  (erase_slice_RARI, One_HasEqualizers, Erase_Parallel_not_faithful,
   Parallel_no_equalizers).

(* Proposition 1 with the faithfulness hypothesis deleted is false. *)
Definition prop1_needs_faithfulness :
  (∀ (A X : Category) (G : A ⟶ X), @HasEqualizers X →
     (∀ a : A, RightAdjointRightInverse (Sliced G a)) → @HasEqualizers A)
  → False :=
  fun P => Parallel_no_equalizers
             (P Parallel _1 (Erase Parallel) One_HasEqualizers
                erase_slice_RARI).
