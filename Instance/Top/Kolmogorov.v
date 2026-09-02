(** * T0-spaces are a full reflective subcategory of Top

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd
          ed., Springer GTM 5, §IV.3, printed p. 92, Exercise 4.
          Verbatim from the page image: "4. Show the following
          subcategories to be reflective: (a) The full subcategory of
          all partial orders in the category Preord of all preorders,
          with arrows all monotone functions. (b) The full subcategory
          of T₀-spaces in Top."  Catalog id: maclane:IV.3:ex4.  This
          file is clause (b) ONLY; clause (a) -- posets inside the
          category of all preorders -- is the sibling development in
          Instance/Ord.v and Instance/Ord/Poset.v, whose pinned name is
          [Poset_Reflective_in_Ord].  Nothing here depends on it and
          nothing there depends on this.

    ** What is delivered

    [T0_Reflective_in_Top : Reflective T0_Subcategory] -- the record of
    Construction/Reflective.v:60, whose three fields are exactly the
    three things Mac Lane's phrase names: FULLNESS of the subcategory
    ([T0_Full]), a REFLECTOR ([T0_reflector]), and the ADJUNCTION
    ([T0_adj]) making it left adjoint to the inclusion.  The adjunction
    ALONE is strictly less than the record, and that mismatch is this
    development's typing rejection in Test/ProbeKolmogorov372.v.

    Around it: topological indistinguishability [SameOpens] with its
    three equivalence lemmas and [SameOpens_of_equiv]; the T0 predicate
    [IsT0]; the full subcategory [T0_Subcategory]/[T0Spaces] with the
    inclusion proved Full AND Faithful; the Kolmogorov quotient
    [KolmogorovQuotient] with [KolmogorovQuotient_T0] and the
    projection [kolmogorov_proj]; the universal property
    [kolmogorov_universal] and its packaging
    [kolmogorov_universal_arrow]; the counit corollary
    [t0_reflect_iso] -- a T0 space is its own Kolmogorov quotient up to
    isomorphism -- instantiated at the two-point discrete space as
    [bool_reflect_iso]; and [Hausdorff_T0_nn].

    ** The route

    Universal arrows, exactly the path Instance/Ab/TorsionFree.v takes
    for §IV.3 Exercise 2 and Instance/Grp/Abelianize.v for §III.1
    Exercise 3: state the ∃! ([kolmogorov_universal]), package it with
    Theory/Universal/Arrow.v:158's [universal_arrow_from_UMP]
    ([kolmogorov_universal_arrow]), then read the functor and the
    adjunction off :295's [LeftAdjointFunctorFromUniversalArrows] and
    :324's [AdjunctionFromUniversalArrows] with no further proof.
    Nothing in that chain is re-derived here.

    ** THE UNIVERSE OBSTRUCTION, AND THE DESIGN IT FORCES

    This is the substance of the file, and it is a measurement rather
    than a preference.

    The obvious rendering of indistinguishability is "x and y lie in
    exactly the same opens", quantified over EVERY open of X.  In this
    library that relation does not fit, and the rejection is a genuine
    universe inconsistency rather than a bookkeeping annoyance.
    [TopSpace@{o}] (Instance/Top.v:129) has [top_carrier :>
    SetoidObject@{o o}], so a space's own `≈` is a
    [crelation@{o o}] -- valued in [Type@{o}] -- while [IsOpen]
    quantifies over predicates [X → Type@{o}], so a relation
    quantifying over all of them lands at a level strictly above [o].
    Measured: the
    unrestricted relation elaborates as [∀ X : TopSpace@{o}, X → X →
    Type@{h}] with [o < h], and building a [SetoidObject@{o o}] on it
    is refused with "Cannot enforce ... = o because o < h <= ...".  So
    the "same carrier, coarser `≈`" design that
    Instance/Ab/TorsionFree.v uses, and that the sibling clause (a)
    uses, is NOT available for [Top] at one and the same universe.
    [SameOpensAll] is kept in the file as that unrestricted relation --
    it is a perfectly good [Definition], it simply cannot be a space's
    setoid -- and [SameOpensAll_SameOpens] relates the two.

    What IS available, and is what this file delivers, is
    indistinguishability tested against the opens whose VALUES lie at a
    level [s] strictly below the space's own level [o]:

      [SameOpens@{s o} X x y := ∀ U : X → Type@{s},
                                  IsOpen X U → (U x ↔ U y)]

    which sits at [Type@{o}] exactly because [X → Type@{s} :
    Type@{o}] when [s < o].  Every [Prop]-valued open is such a [U] (by
    cumulativity, at every [s]), so the family being tested against is
    generous; both concrete witnesses below separate their points with
    a [Prop]-valued open.

    The quotient then carries the SAME carrier type, the coarsened `≈`
    [SameOpens X], and as its opens exactly those opens of X that
    RESPECT that relation ([kq_open]).  The two definitions look
    circular and are not, and the lemma that breaks the circle is
    [small_open_is_kq_open]: an open of X valued at level [s] respects
    [SameOpens X] AUTOMATICALLY, since the relation says in so many
    words that x and y agree on it.  Hence every level-[s] open of X is
    still an open of the quotient, [KolmogorovQuotient_T0] is three
    lines, and -- the other half of the same fact -- the mediator out
    of the quotient is continuous because a [Type@{o}]-valued open of
    the T0 target pulls back to an open that respects the relation, by
    [open_proper] of the target.  Classically, where opens are
    [Prop]-valued and small, [kq_open] IS the topology of X and this is
    the ordinary Kolmogorov quotient.

    Read [IsT0] with that in mind: it is "points that agree on all
    level-[s] opens are equal", a STRONGER requirement than agreement
    on all opens would give, since [SameOpensAll] implies [SameOpens]
    and not conversely by anything proved here.  The restriction is
    visible in the statement rather than hidden inside it.

    ** Same carrier, no choice principle

    [KolmogorovQuotient X] forms no new carrier: [kq_carrier_strict]
    records by [eq_refl] that its carrier IS X's, and
    [kq_equiv_strict] that its `≈` IS [SameOpens X].  No equivalence
    class, no quotient axiom, no representative is ever chosen, and
    [kolmogorov_proj] is the identity on points.  Everything in the
    file is [Type]-valued data: [SameOpens] is a Π of products, its
    witnesses are taken apart directly, and nothing anywhere extracts
    a witness from a [Prop]-valued existential -- so no choice
    principle appears.  All 76 constants are closed under the global
    context, with no [Axioms:] line anywhere; in particular this file
    requires none of
    Instance/Top/Interval.v, Instance/Top/Homotopy.v or the metric
    files, so the standard library's real-number axioms are nowhere in
    its closure.

    ** Prior art, measured at d658518e (the issue's "Current state" is
       stale and is corrected rather than repeated)

    Issue #372 says "both ambient categories are missing" and that
    "there is no Instance/Top.v".  Both are false at d658518e:
    [Top : Category] is Instance/Top.v:273, with [TopSpace] (:129),
    [Continuous] (:198), [ContinuousMorphism] (:205), the discrete and
    indiscrete constructors (:319, :380), and the Hausdorff and
    compact-Hausdorff full subcategories (:938, :956) already in place.

    What IS absent, and is what this file supplies: a case-insensitive
    search over the [.v] files for 'kolmogorov', 'specializ' and
    'indistinguish' returns no topological hit at all (the two
    'kolmogorov' hits are Chapman-Kolmogorov in
    Structure/Monoidal/Markov.v:60,:96, the one 'indistinguish' hit is
    Theory/Algebra/Monoid/Product.v:90 about type display, and the
    'specializ' matches are the tactic [specialize] and prose about
    specializing a theorem), and a search for the token 'T0' returns
    three lines --
    Adjunction/Additive.v:47 and Structure/AbCategory.v:50,:182 --
    every one of them Mac Lane's phrase "whence T0 = 0" about an
    additive functor, which is unrelated.  There was no T0 predicate,
    no indistinguishability relation, no Kolmogorov quotient and no
    reflection.

    ** Reused, and what that saves

    - Instance/Top.v: [TopSpace] and its six fields, [Continuous],
      [ContinuousMorphism], [Build_ContinuousMorphism], [Top],
      [IsHausdorff] (:895) for [Hausdorff_T0_nn], and the two witness
      spaces [Bool_Discrete] (:987) and [TwoPoint_Indiscrete] (:792)
      with [bool_setoid_object] (:784).  The [Sub Top] pattern is
      [Hausdorff_Subcategory] (:938) / [HausdorffSpaces] (:945) /
      [Hausdorff_Full] (:947) copied field for field.
    - Construction/Subcategory.v: [Subcategory] (:36), [Sub] (:55),
      [Incl] (:64), [Incl_Faithful] (:89), [Full] (:99),
      [Full_Implies_Full_Functor] (:104).  The trivially-true [shom] is
      the [Hausdorff_Subcategory] and Instance/Rng.v:403 [CRng_Sub]
      pattern, and [Full] is written qualified because
      Construction/Subcategory.v exports its OWN [Full], whose first
      argument is a Category.
    - Construction/Reflective.v: [Reflective] (:60) and
      [reflective_counit_iso] (:92).
    - Theory/Universal/Arrow.v: the three constants named under "The
      route" above.

    The quotient-topology precedents in tree -- Instance/Top.v:635's
    [CP_open], Instance/Top/Wedge.v:145's [wedge_open],
    Instance/Top/Pushout.v:203's [tp_open] -- all glue POINTS by an
    inductive or closed-form relation and re-derive openness from
    scratch.  None of them is required here and none is needed: this
    quotient changes no points.

    NEW here: [SameOpens] and its four lemmas, [SameOpensAll], [IsT0],
    the subcategory, the five [kq_*] topology lemmas and
    [KolmogorovQuotient], [small_open_is_kq_open], the mediator and the
    universal property, [Hausdorff_T0_nn], and the three witnesses.

    ** Strengths, measured strict-first

    Holding at [eq_refl] (eight occurrences outside comments, none of
    them inside a rejection: the SIX [Example]s named in this
    paragraph, which pin a definitional identity, plus two uses inside
    the witness proofs [Bool_Discrete_T0] and [tri_point_apart] -- the
    file's two other [Example]s, [indiscrete_quot_identifies] and
    [tri_quot_merges], are inhabitants rather than [eq_refl]s): the
    quotient's carrier IS the base
    space's and its `≈` IS [SameOpens X] ([kq_carrier_strict],
    [kq_equiv_strict]); the reflector's object part IS the quotient
    ([t0_reflector_obj]); the universal arrow IS [kolmogorov_proj] and
    its object IS [KolmogorovT0 X] ([kolmogorov_arrow_is_proj],
    [kolmogorov_arrow_obj] -- since [universal_arrow_from_UMP] stores
    the supplied morphism as the second projection of the comma object
    it builds); and the adjunction's UNIT is the projection applied to
    any point ([t0_unit_is_proj]).

    Falling back, with the cause diagnosed in each case:

    - The unit as a MORPHISM RECORD is only `≈` the projection
      ([t0_unit_is_proj_hom]).  Cause:
      [AdjunctionFromUniversalArrows] builds ⌊−⌋ as [fun g => fmap[U]
      g ∘ arrow], so the class unit is a COMPOSITE record,
      [fmap[Incl] id ∘ kolmogorov_proj X]; applied to a point that
      composite reduces, as a [ContinuousMorphism] record it does not.
      The same shape is recorded for #371's [torsion_unit_is_proj_hom]
      and for Instance/Mod/Free.v:542's [free_module_unit_is_insert].
    - [KolmogorovQuotient Bool_Discrete] is isomorphic to
      [Bool_Discrete] but not equal to it: [bool_reflect_iso] is a pure
      instantiation of [reflective_counit_iso] with no tactic, while
      [KolmogorovQuotient Bool_Discrete = Bool_Discrete] is refused.
      Cause: [Discrete_Top]'s opens are the `≈`-respecting predicates
      and the quotient's are the pairs of an open with a proof that it
      respects [SameOpens], so the two [IsOpen] fields differ as terms
      -- and so, separately, do the setoid field and every law field.
    - The COUNIT is not read back at all.  It is the other transpose,
      [unique_obj (ump_universal_arrows …)], and
      [ump_universal_arrows] (Theory/Universal/Arrow.v:139) is closed
      with [Qed], so nothing on that side reduces and no [eq_refl] is
      claimed for it in either direction.
    - [Hausdorff_T0_nn] yields only [¬ ¬ (x ≈ y)], and it is stated
      against [SameOpensAll], not against [SameOpens].  TWO independent
      reasons, both measured rather than guessed.  First, logic: from
      "x and y lie in the same opens" and "x is apart from y" one gets
      the separating pair and a contradiction, which refutes the
      apartness and gives a double negation; turning that into [x ≈ y]
      is double-negation elimination for the carrier's own `≈`, which
      this library does not have.  Second, levels: [IsHausdorff]
      produces separating opens valued at [Type@{o}], which are not
      among the level-[s] opens [SameOpens] tests, so the argument does
      not even start from [SameOpens].  Consequently NOTHING here
      derives [IsT0] from [IsHausdorff], and no such implication is
      claimed; [Bool_Discrete_T0] is proved directly instead, from one
      [Prop]-valued open.

    ** Universes

    Measured with [Set Printing Universes] on every constant, reading
    BOTH the binder and the constraint block.

    The file's own content is the strict inequality [s < o] in
    [SameOpens@{s o}] -- the level of the opens tested strictly below
    the level of the space -- declared with the trailing [+] of
    Instance/Top.v:226's idiom, and that [+] is load-bearing across
    versions: without it Coq 8.19 and 8.20 reject the declaration with
    "Universe constraints are not implied by the ones declared" (six
    inferred bounds against [prod] and [sigT]) while Rocq 9.1 accepts
    it, which the three-version nix build found and which is why the
    declaration is not closed.  It propagates: [IsT0@{u u0 u1}]
    carries [u0 < u1] with [u1 <= u], and [KolmogorovQuotient@{u u0} :
    TopSpace@{u} → TopSpace@{u}] carries [u0 < u] (with four inherited
    [Projections] bounds), so the quotient is a genuine ENDOfunction on
    the objects of one and the same [Top] --
    which is what makes [T0_reflector] and hence the [Reflective]
    record formable at all.

    Two identifications sit in BINDERS, where a reader of the blocks
    alone would miss them, and both are the DONORS'.  First,
    [Top@{u u1}] is [Category@{u u u}] (Instance/Top.v's own note: the
    hom-sets live one step above the points), so hom and proof are
    identified there; [T0Spaces] inherits it, printing as
    [Category@{u0 u u}].  Second, [Subcategory] is declared over
    [Category@{u u0 u0}] and [Reflective] over [Category@{u3 u5 u5}],
    the same identification once more; it is guarded by the probe's
    formability rejection, where naming a hom-set and an identity at
    hom-strictly-below-proof levels succeeds while [Subcategory] is
    refused.  Read that rejection at its strength: it fires at
    [Subcategory], and [Reflective] cannot be tested apart from its
    [Subcategory] argument, so whether [Reflective] identifies anything
    OF ITS OWN is not measured here.  Neither identification is
    introduced by this file and neither is claimed unavoidable.

    NO constraint block of any constant in this file carries a universe
    EQUATION -- every entry is [<] or [<=], measured over all 70 blocks
    the 76 constants print.  Read the [Set] measurement exactly: the
    token occurs in the [About] output of this file's constants in
    precisely TWO places, and NEITHER is a universe binder or a
    constraint block -- [Tri@{} : Set], which is the SORT [Inductive
    Tri : Set] declares, and the motive of Coq's generated eliminator
    [Tri_rec : ∀ P : Tri → Set, …].  No universe binder and no
    constraint entry of any constant in the file mentions [Set]; that
    every universe variable satisfies [Set <= _] is Coq's own
    convention and is not printed, so nothing is claimed about it.

    ** Non-vacuity

    Proved in both directions, so the subcategory is neither empty nor
    everything, and the quotient is shown to do something and not to do
    too much.

    [Bool_Discrete] is T0 ([Bool_Discrete_T0], by testing the
    [Prop]-valued open [fun z => z = x]), so [T0Spaces] is inhabited
    and [bool_reflect_iso] applies.  [TwoPoint_Indiscrete] is NOT
    ([TwoPoint_Indiscrete_not_T0]): its opens are the uniform
    predicates, so every pair of points is indistinguishable, while
    [true ≈ false] is [true = false].  The quotient identifies exactly
    that pair, with the witness written out
    ([indiscrete_quot_identifies], whose proof term IS
    [indiscrete_points_same_opens]).

    [Tri_Top] is the mixed three-point space: carrier [Tri] with its
    opens the predicates that cannot tell [Tri_l] from [Tri_r].  It is
    not T0 ([Tri_Top_not_T0]), its quotient merges that pair
    ([tri_quot_merges]) and keeps [Tri_l] apart from the third point
    ([tri_quot_keeps_point_apart]; that [Tri_r] is apart from it too
    follows in one line from [SameOpens_sym]/[SameOpens_trans] and is
    not stated).  Say precisely how the two negatives close, since the
    two mechanisms differ: the first PROVES the relation at every open,
    directly from [tri_open]'s two components, and feeds it to [IsT0];
    the second INSTANTIATES the relation at the single [Prop]-valued
    open [fun z => z = Tri_pt].  Both then close by [discriminate] on
    the discrete carrier.  No map out of the quotient into a second
    space is used anywhere, and no induction over a generated relation
    occurs, there being no generated relation.

    ** NOT delivered

    - No T1/T2 chain beyond [Hausdorff_T0_nn], which as measured above
      does not give [IsT0]; no sober spaces, no T3/T4, no
      specialization ORDER as a preorder, and in particular no bridge
      to the sibling clause (a): the specialization preorder of a space
      would be the natural object of [Ord] connecting the two halves of
      Mac Lane's exercise and it is NOT built here.
    - No Kolmogorov quotient of a pointed space, and no relation to
      Instance/Top/Homotopy.v's [Toph] or [Top_pointed].
    - No functoriality statement for [KolmogorovQuotient] beyond the
      reflector itself, and no naturality of [kolmogorov_proj] stated
      separately from the adjunction's unit.
    - No proof that [KolmogorovQuotient] is a quotient in any
      categorical sense (no coequalizer, no [RegularEpi]); the
      projection is not shown epic.
    - No comparison between [SameOpens] and [SameOpensAll] beyond
      [SameOpensAll_SameOpens]; no space is exhibited separating them,
      so the restriction to level-[s] opens is not shown to be strict.
    - No idempotent monad of the reflection.
      Construction/Reflective/Idempotent.v gives it by instantiation
      from [T0_Reflective_in_Top]; that instantiation is not made.

    ** Corrections to the brief that guided this file

    Each is a measurement, not an opinion.  (1) The brief's plan
    proposed [SameOpens] quantified over ALL opens and the quotient
    with "[IsOpen := IsOpen X] verbatim", noting that "coarsening the
    carrier's `≈` to 'agree on every open' keeps every open predicate
    open on the nose".  That is true of the mathematics and false of
    the universes: the relation is a level too big to be a space's `≈`,
    as measured above and pinned in the probe, so the level-restricted
    relation and the respecting-opens topology are used instead.  (2)
    The brief asked whether [KolmogorovQuotient_T0] is definitional; it
    is not -- it is a three-line proof whose content is
    [small_open_is_kq_open] -- because the quotient's opens are the
    respecting ones rather than X's verbatim.  (3) The brief expected
    [Hausdorff_T0] possibly weakened to a double negation; the double
    negation is indeed all that comes out, and there is a SECOND
    obstruction (the level of the separating opens) that the brief does
    not anticipate, so the lemma is stated against [SameOpensAll].  (4)
    The brief offered [Sum_Top] from Instance/Top/Coproduct.v for the
    mixed witness "if it is cheap"; [Tri_Top] is built directly in
    fifty lines instead, which adds nothing to the closure.  Every
    donor line number the brief gave was re-grepped here and is
    correct. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.

Generalizable All Variables.

(** * Topological indistinguishability

    Two points are indistinguishable when every open tested holds of
    one exactly when it holds of the other.  The opens tested are
    those valued at the level [s], strictly below the space's own
    level [o]; see the header for why the unrestricted relation cannot
    be a space's `≈` in this library. *)

Definition SameOpens@{s o | s < o +} (X : TopSpace@{o}) (x y : X)
  : Type@{o} :=
  ∀ U : X → Type@{s}, IsOpen X U → (U x ↔ U y).

Lemma SameOpens_refl (X : TopSpace) (x : X) : SameOpens X x x.
Proof. intros U HU; split; exact (fun w => w). Defined.

Lemma SameOpens_sym (X : TopSpace) (x y : X) :
  SameOpens X x y → SameOpens X y x.
Proof.
  intros H U HU; destruct (H U HU) as [f g]; split; assumption.
Defined.

Lemma SameOpens_trans (X : TopSpace) (x y z : X) :
  SameOpens X x y → SameOpens X y z → SameOpens X x z.
Proof.
  intros Hxy Hyz U HU.
  destruct (Hxy U HU) as [f1 g1]; destruct (Hyz U HU) as [f2 g2].
  split; auto.
Defined.

(* Equivalent points are indistinguishable: this is [open_proper],
   used in both directions. *)
Lemma SameOpens_of_equiv (X : TopSpace) (x y : X) :
  x ≈ y → SameOpens X x y.
Proof.
  intros Hxy U HU; split.
  - exact (open_proper X U HU x y Hxy).
  - exact (open_proper X U HU y x (symmetry Hxy)).
Defined.

(** * Agreement on ALL opens

    The unrestricted relation.  It is a perfectly good predicate; what
    it cannot be, for the reason measured in the header, is the
    equivalence of a [SetoidObject@{o o}].  It is used only to state
    [Hausdorff_T0_nn]. *)

Definition SameOpensAll (X : TopSpace) (x y : X) : Type :=
  ∀ U : X → Type, IsOpen X U → (U x ↔ U y).

Lemma SameOpensAll_SameOpens (X : TopSpace) (x y : X) :
  SameOpensAll X x y → SameOpens X x y.
Proof. intros H U HU; exact (H U HU). Defined.

(** * T0 spaces

    Kolmogorov's axiom in its setoid reading: indistinguishable points
    are equal -- the same move Instance/Pos.v:90 makes for
    antisymmetry ([pos_antisym : pos_le x y → pos_le y x → x ≈ y]),
    where the conclusion is the carrier's `≈` rather than Leibniz
    equality. *)

Definition IsT0 (X : TopSpace) : Type :=
  ∀ x y : X, SameOpens X x y → x ≈ y.

Definition T0_Subcategory : Subcategory Top :=
  @Build_Subcategory Top
    (fun X : Top => IsT0 X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition T0Spaces : Category := Sub Top T0_Subcategory.

Lemma T0_Full :
  Category.Construction.Subcategory.Full Top T0_Subcategory.
Proof. intros x y ox oy g; exact I. Defined.

Lemma T0_Incl_Full : Functor.Full (Incl Top T0_Subcategory).
Proof.
  exact (Full_Implies_Full_Functor Top T0_Subcategory T0_Full).
Defined.

Lemma T0_Incl_Faithful : Functor.Faithful (Incl Top T0_Subcategory).
Proof. exact (Incl_Faithful Top T0_Subcategory). Defined.

(** * The Kolmogorov quotient

    Same carrier, coarser `≈`, and as opens exactly those opens of X
    that respect the coarser `≈`. *)

Definition kq_setoid (X : TopSpace) : SetoidObject :=
  {| carrier := top_carrier X
   ; is_setoid :=
       {| equiv := SameOpens X
        ; setoid_equiv :=
            Build_Equivalence _ (SameOpens_refl X)
              (SameOpens_sym X) (SameOpens_trans X) |} |}.

Definition kq_open (X : TopSpace) (V : top_carrier X → Type) : Type :=
  (IsOpen X V *
   (∀ x y : top_carrier X, SameOpens X x y → V x → V y))%type.

Lemma kq_respects (X : TopSpace) (U V : top_carrier X → Type) :
  (∀ x, U x ↔ V x) → kq_open X U → kq_open X V.
Proof.
  intros HUV [HU Hr]; split.
  - exact (open_respects X U V HUV HU).
  - intros x y Hxy Vx.
    exact (fst (HUV y) (Hr x y Hxy (snd (HUV x) Vx))).
Defined.

Lemma kq_proper (X : TopSpace) (V : top_carrier X → Type) :
  kq_open X V → ∀ x y : top_carrier X, SameOpens X x y → V x → V y.
Proof. intros [HV Hr]; exact Hr. Defined.

Lemma kq_union (X : TopSpace) (I : Type)
      (U : I → (top_carrier X → Type)) :
  (∀ i, kq_open X (U i)) →
  kq_open X (fun x => { i : I & U i x }).
Proof.
  intro HU; split.
  - exact (open_union X I U (fun i => fst (HU i))).
  - intros x y Hxy w.
    exact (projT1 w; snd (HU (projT1 w)) x y Hxy (projT2 w)).
Defined.

Lemma kq_whole (X : TopSpace) : kq_open X (fun _ => poly_unit).
Proof.
  split; [ exact (open_whole X) | intros x y _ w; exact w ].
Defined.

Lemma kq_inter (X : TopSpace) (U V : top_carrier X → Type) :
  kq_open X U → kq_open X V →
  kq_open X (fun x => U x ∧ V x).
Proof.
  intros [HU HrU] [HV HrV]; split.
  - exact (open_inter X U V HU HV).
  - intros x y Hxy w.
    exact (HrU x y Hxy (fst w), HrV x y Hxy (snd w)).
Defined.

Definition KolmogorovQuotient (X : TopSpace) : TopSpace :=
  {| top_carrier   := kq_setoid X
   ; IsOpen        := kq_open X
   ; open_respects := kq_respects X
   ; open_proper   := kq_proper X
   ; open_union    := kq_union X
   ; open_whole    := kq_whole X
   ; open_inter    := kq_inter X |}.

(* THE CRUX.  An open of [X] whose values lie at the level the
   indistinguishability relation tests respects that relation
   AUTOMATICALLY, because the relation says in so many words that x
   and y agree on it.  So every such open of X is still an open of the
   quotient, with no hypothesis, and that is what makes the definition
   of [SameOpens] and the definition of [kq_open] non-circular. *)
Lemma small_open_is_kq_open (X : TopSpace) (U : X → Type) :
  IsOpen X U → IsOpen (KolmogorovQuotient X) U.
Proof.
  intro HU; split; [ exact HU | ].
  intros a b Hab; exact (fst (Hab U HU)).
Defined.

Lemma KolmogorovQuotient_T0 (X : TopSpace) :
  IsT0 (KolmogorovQuotient X).
Proof.
  intros x y H U HU.
  exact (H U (small_open_is_kq_open X U HU)).
Defined.

Definition kq_proj_setoid (X : TopSpace) :
  SetoidMorphism (top_carrier X) (top_carrier (KolmogorovQuotient X)).
Proof.
  refine {| morphism := fun x : top_carrier X => x |}.
  intros x y Hxy; exact (SameOpens_of_equiv X x y Hxy).
Defined.

Lemma kq_proj_continuous (X : TopSpace) :
  Continuous X (KolmogorovQuotient X) (kq_proj_setoid X).
Proof. intros V HV; exact (fst HV). Defined.

Definition kolmogorov_proj (X : TopSpace)
  : X ~{Top}~> KolmogorovQuotient X :=
  Build_ContinuousMorphism X (KolmogorovQuotient X)
    (kq_proj_setoid X) (kq_proj_continuous X).

(** * The universal property *)

(* A continuous map into a T0 space cannot tell indistinguishable
   points apart: pulling back a level-[s] open of the target along f
   gives a level-[s] open of the source. *)
Definition kq_med_resp {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) (x y : top_carrier X) :
  SameOpens X x y → continuous_map f x ≈ continuous_map f y.
Proof.
  intro Hxy.
  apply HD.
  intros V HV.
  exact (Hxy (fun z => V (continuous_map f z)) (continuity f V HV)).
Defined.

Definition kq_med_setoid {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) :
  SetoidMorphism (top_carrier (KolmogorovQuotient X)) (top_carrier D).
Proof.
  refine {| morphism := fun x => continuous_map f x |}.
  intros x y Hxy; exact (kq_med_resp HD f x y Hxy).
Defined.

Lemma kq_med_continuous {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) :
  Continuous (KolmogorovQuotient X) D (kq_med_setoid HD f).
Proof.
  intros V HV; split.
  - exact (continuity f V HV).
  - intros x y Hxy Vfx.
    exact (open_proper D V HV _ _ (kq_med_resp HD f x y Hxy) Vfx).
Defined.

Definition kolmogorov_med {X D : TopSpace} (HD : IsT0 D)
    (f : X ~{Top}~> D) : KolmogorovQuotient X ~{Top}~> D :=
  Build_ContinuousMorphism (KolmogorovQuotient X) D
    (kq_med_setoid HD f) (kq_med_continuous HD f).

Definition KolmogorovT0 (X : TopSpace) : T0Spaces :=
  (KolmogorovQuotient X; KolmogorovQuotient_T0 X).

Theorem kolmogorov_universal (X : TopSpace) :
  ∀ (d : T0Spaces) (f : X ~{Top}~> Incl Top T0_Subcategory d),
    ∃! g : KolmogorovT0 X ~{T0Spaces}~> d,
      f ≈ fmap[Incl Top T0_Subcategory] g ∘ kolmogorov_proj X.
Proof.
  intros d f.
  unshelve eexists.
  - exact (kolmogorov_med `2 d f; I).
  - intro x; simpl; reflexivity.
  - intros g Hg x; simpl.
    exact (Hg x).
Defined.

Definition kolmogorov_universal_arrow (X : TopSpace)
  : @UniversalArrow Top T0Spaces X (Incl Top T0_Subcategory) :=
  @universal_arrow_from_UMP Top T0Spaces X (Incl Top T0_Subcategory)
    (KolmogorovT0 X) (kolmogorov_proj X) (kolmogorov_universal X).

Definition T0_reflector : Top ⟶ T0Spaces :=
  LeftAdjointFunctorFromUniversalArrows (Incl Top T0_Subcategory)
    kolmogorov_universal_arrow.

Definition T0_adj : T0_reflector ⊣ Incl Top T0_Subcategory :=
  AdjunctionFromUniversalArrows (Incl Top T0_Subcategory)
    kolmogorov_universal_arrow.

Definition T0_Reflective_in_Top : Reflective T0_Subcategory :=
  @Build_Reflective Top T0_Subcategory T0_Full T0_reflector T0_adj.

(** * Strict readbacks *)

Example kq_carrier_strict (X : TopSpace) :
  carrier (top_carrier (KolmogorovQuotient X)) = carrier (top_carrier X)
  := eq_refl.

Example kq_equiv_strict (X : TopSpace) (x y : top_carrier X) :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient X))) x y
    = SameOpens X x y := eq_refl.

Example t0_reflector_obj (X : TopSpace) :
  `1 (fobj[T0_reflector] X) = KolmogorovQuotient X := eq_refl.

Example kolmogorov_arrow_is_proj (X : TopSpace) :
  @arrow Top T0Spaces X (Incl Top T0_Subcategory)
    (kolmogorov_universal_arrow X) = kolmogorov_proj X := eq_refl.

Example kolmogorov_arrow_obj (X : TopSpace) :
  @arrow_obj Top T0Spaces X (Incl Top T0_Subcategory)
    (kolmogorov_universal_arrow X) = KolmogorovT0 X := eq_refl.

Definition t0_unit (X : TopSpace)
  : X ~{Top}~> Incl Top T0_Subcategory (fobj[T0_reflector] X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ T0_adj X.

Example t0_unit_is_proj (X : TopSpace) (x : X) :
  continuous_map (t0_unit X) x = continuous_map (kolmogorov_proj X) x
  := eq_refl.

Lemma t0_unit_is_proj_hom (X : TopSpace) :
  t0_unit X ≈ kolmogorov_proj X.
Proof. intro x; reflexivity. Defined.

(* A T0 space is its own Kolmogorov quotient, up to isomorphism in the
   subcategory: the counit of a full reflective subcategory. *)
Definition t0_reflect_iso (x : T0Spaces) :
  fobj[T0_reflector] (Incl Top T0_Subcategory x) ≅[T0Spaces] x :=
  reflective_counit_iso T0_Reflective_in_Top x.

(** * Hausdorff spaces

    What comes out is a DOUBLE NEGATION, against the unrestricted
    relation; see the header for the two independent reasons this does
    not give [IsT0]. *)

Lemma Hausdorff_T0_nn (X : TopSpace) (H : IsHausdorff X) (x y : X) :
  SameOpensAll X x y → ¬ ¬ (x ≈ y).
Proof.
  intros Hxy Hne.
  destruct (H x y Hne) as [U [V [[HU HV] [[Ux Vy] Hdisj]]]].
  exact (Hdisj y (fst (Hxy U HU) Ux) Vy).
Defined.

(** * Non-vacuity: the two-point discrete space is T0 *)

Lemma bool_point_open (x : bool_setoid_object) :
  IsOpen Bool_Discrete (fun z : bool_setoid_object => z = x).
Proof. intros a b Hab Ha; simpl in Hab; now subst. Defined.

Theorem Bool_Discrete_T0 : IsT0 Bool_Discrete.
Proof.
  intros x y H.
  symmetry.
  exact (fst (H (fun z : bool_setoid_object => z = x)
                (bool_point_open x)) eq_refl).
Defined.

Definition Bool_Discrete_T0Space : T0Spaces :=
  (Bool_Discrete; Bool_Discrete_T0).

Definition bool_reflect_iso :
  fobj[T0_reflector] (Incl Top T0_Subcategory Bool_Discrete_T0Space)
    ≅[T0Spaces] Bool_Discrete_T0Space :=
  t0_reflect_iso Bool_Discrete_T0Space.

(** * Non-vacuity: the two-point indiscrete space is not T0 *)

Lemma indiscrete_points_same_opens :
  SameOpens TwoPoint_Indiscrete true false.
Proof.
  intros U HU; split; intro w.
  - exact (HU true false w).
  - exact (HU false true w).
Defined.

Theorem TwoPoint_Indiscrete_not_T0 : IsT0 TwoPoint_Indiscrete → False.
Proof.
  intro H.
  pose proof (H true false indiscrete_points_same_opens) as Heq.
  simpl in Heq; discriminate.
Defined.

Example indiscrete_quot_identifies :
  @equiv _ (is_setoid (top_carrier
              (KolmogorovQuotient TwoPoint_Indiscrete))) true false
  := indiscrete_points_same_opens.

(** * Non-vacuity: a three-point space merging exactly one pair

    The opens are the predicates that cannot tell [Tri_l] from
    [Tri_r]; [Tri_pt] is separated from both by a [Prop]-valued
    open. *)

Inductive Tri : Set := Tri_l | Tri_r | Tri_pt.

Definition Tri_setoid : SetoidObject :=
  {| carrier := Tri; is_setoid := eq_Setoid Tri |}.

Definition tri_open (U : Tri_setoid → Type) : Type :=
  ((U Tri_l → U Tri_r) * (U Tri_r → U Tri_l))%type.

Lemma tri_respects (U V : Tri_setoid → Type) :
  (∀ x, U x ↔ V x) → tri_open U → tri_open V.
Proof.
  intros HUV [f g]; split; intro w.
  - exact (fst (HUV Tri_r) (f (snd (HUV Tri_l) w))).
  - exact (fst (HUV Tri_l) (g (snd (HUV Tri_r) w))).
Defined.

Lemma tri_proper (U : Tri_setoid → Type) :
  tri_open U → ∀ x y : Tri_setoid, x ≈ y → U x → U y.
Proof. intros _ x y Hxy Ux; simpl in Hxy; now subst. Defined.

Lemma tri_union (I : Type) (U : I → (Tri_setoid → Type)) :
  (∀ i, tri_open (U i)) →
  tri_open (fun x => { i : I & U i x }).
Proof.
  intro HU; split; intro w.
  - exact (projT1 w; fst (HU (projT1 w)) (projT2 w)).
  - exact (projT1 w; snd (HU (projT1 w)) (projT2 w)).
Defined.

Lemma tri_whole : tri_open (fun _ => poly_unit).
Proof. split; intro w; exact w. Defined.

Lemma tri_inter (U V : Tri_setoid → Type) :
  tri_open U → tri_open V → tri_open (fun x => U x ∧ V x).
Proof.
  intros [f1 g1] [f2 g2]; split; intro w.
  - exact (f1 (fst w), f2 (snd w)).
  - exact (g1 (fst w), g2 (snd w)).
Defined.

Definition Tri_Top : TopSpace :=
  {| top_carrier   := Tri_setoid
   ; IsOpen        := tri_open
   ; open_respects := tri_respects
   ; open_proper   := tri_proper
   ; open_union    := tri_union
   ; open_whole    := tri_whole
   ; open_inter    := tri_inter |}.

Lemma tri_pair_same_opens : SameOpens Tri_Top Tri_l Tri_r.
Proof. intros U HU; split; [ exact (fst HU) | exact (snd HU) ]. Defined.

Theorem Tri_Top_not_T0 : IsT0 Tri_Top → False.
Proof.
  intro H.
  pose proof (H Tri_l Tri_r tri_pair_same_opens) as Heq.
  simpl in Heq; discriminate.
Defined.

Lemma tri_point_open :
  IsOpen Tri_Top (fun z : Tri_setoid => z = Tri_pt).
Proof. split; intro w; discriminate w. Defined.

Theorem tri_point_apart : SameOpens Tri_Top Tri_l Tri_pt → False.
Proof.
  intro H.
  pose proof (snd (H (fun z : Tri_setoid => z = Tri_pt) tri_point_open)
                eq_refl) as Heq.
  discriminate Heq.
Defined.

Example tri_quot_merges :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient Tri_Top)))
    Tri_l Tri_r := tri_pair_same_opens.

Theorem tri_quot_keeps_point_apart :
  @equiv _ (is_setoid (top_carrier (KolmogorovQuotient Tri_Top)))
    Tri_l Tri_pt → False.
Proof. exact tri_point_apart. Defined.

Definition Tri_T0 : T0Spaces := KolmogorovT0 Tri_Top.
