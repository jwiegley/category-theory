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

Generalizable All Variables.

(** * The special initial-object theorem *)

(* nLab:      https://ncatlab.org/nlab/show/initial+object
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   Theorem 1, book p. 128 (PDF pp. 137-138; catalogue id
   [maclane:V.8:thm1]): if a category is small-complete, has small
   hom-sets and a small cogenerating set Q, and every set of subobjects
   of each object has an intersection, then it has an initial object.
   Riehl, "Category Theory in Context", Lemma 4.7.11, printed p. 177
   ([riehl:4.7:lem11]), is the same statement for a locally small
   complete category with a small coseparating set.  Both proofs take the
   product q_0 of the cogenerating family and return the intersection r
   of ALL subobjects of q_0.  The theorem is the object-level half of the
   special adjoint functor theorem: nLab's proof of that theorem runs the
   same construction in each comma category d↓R, whose initial object is
   "the intersection = pullback of all subobjects of ∏_s k_s".  It is
   the cogenerator-based alternative to Freyd's construction of an
   initial object from a small weakly initial family (Theory/
   WeaklyInitial.v, Mac Lane §V.6), and the section on Freyd below says
   how the two are related in tree.

   ** What is proved

   [special_initial_object] is the theorem in the form the books give
   it.  From [comp : Complete C], a cogenerating family [G]
   (Adjunction/SAFT.v's [Cogenerator]) and a subobject [w] of
   [cogen_prod comp G] that is the intersection of ALL subobjects of it
   -- [IsIntersection (fun m : SubObj (cogen_prod comp G) => m) w] in
   Theory/Subobject/Lattice.v's vocabulary -- it returns [@Initial C],
   and the initial object IS [Subobject.sub_dom w]:
   [special_initial_object_obj] is [eq_refl].

   UNIQUENESS is [least_sub_arrows_agree].  In any category with
   equalizers, two parallel arrows [f g] out of the domain of a least
   subobject [w] of any object agree: the equalizer [e] of [f] and [g],
   followed by [w]'s mono, is a subobject ([equalizer_sub]); leastness
   gives [s] with [w]'s mono ∘ [e] ∘ [s] ≈ [w]'s mono, cancelling the
   monic gives [e ∘ s ≈ id], so [e] is split epi and [f ≈ g].  The
   book's "two distinct arrows would have an equalizer that is a proper
   mono" becomes a direct argument with no case split on the equality of
   arrows.  The lemma uses neither the cogenerator nor the product, so
   it is stated over a bare [HasEqualizers C] for reuse; the theorem
   supplies Adjunction/GAFT.v's [Complete_HasEqualizers].

   EXISTENCE follows the book.  For [c : C], Mac Lane's j : c → ∏_H q is
   Adjunction/SAFT.v's [cogen_canonical] into the hom-indexed power
   [cogen_power comp G c], monic by [cogenerator_canonical_monic]; that
   makes [c] a subobject of the power ([cogen_canonical_sub]), and it is
   the one place where [cog_separates] is consumed.  Mac Lane's
   k : q_0 → ∏_H q (Riehl's "diagonal map") is [cogen_prod_to_power],
   whose component at [(j, h)] is the [j]-th projection.  Pulling [c]
   back along k ([cogen_pullback_sub], Theory/Subobject/Functor.v's
   [sub_reindex], over the pullbacks of [complete_pullbacks]) gives a
   subobject of the product; the least subobject lies below it, and the
   pullback's second leg [cogen_pullback_to] ends the arrow.  That arrow
   is [special_initial_zero], and [special_initial_object_zero] reads it
   back by [eq_refl].

   Only the lower-bound half of the intersection is consumed.
   [special_initial_object_least] is the theorem over the weakest form
   of the hypothesis, a least subobject [∀ v, sub_le w v];
   [least_of_intersection_all] and [intersection_all_of_least] convert
   between that form and the intersection of all subobjects, both ways
   and by term; [special_initial_object] is [special_initial_object_least]
   composed with the first.  [special_initial_IsInitialObj] states the
   conclusion in the type, [IsInitialObj (Subobject.sub_dom w)], so that
   "the initial object IS the intersection" is a signature and not only
   an [Example].

   ** Mac Lane's hypothesis, read three ways

   THE BOOK'S FORM.  "Every set of subobjects of each object has an
   intersection" is read as [HasClassIntersections]: every ≈-closed class
   of subobjects of every object has an intersection.  The reading
   departs from the book twice.  Sets become CLASSES, which STRENGTHENS
   the hypothesis against a literal set reading, as the book's own proof
   requires (it intersects all subobjects of the product), for the reason
   Structure/WellPowered.v's header gives: a set of subobjects is a set
   of equivalence classes, and the family that carries the proof, ALL
   subobjects of [cogen_prod comp G], is indexed by the large type
   [SubObj (cogen_prod comp G)]; a family indexed at [Complete]'s shape
   universe already has an intersection from completeness alone and
   would make the hypothesis vacuous.  The catalogue's summary of Riehl's
   lemma supports this reading with the word "collection" (catalogue
   summary [riehl:4.7:lem11]: "every collection of subobjects has an
   intersection"; the book's own wording was not checked).  And the
   intersection is a greatest lower bound in the subobject order
   (Theory/Subobject/Lattice.v's [IsIntersection],
   fields [inter_le] and [inter_greatest]), where Mac Lane §V.7 and
   Riehl Definition 4.7.9 define it as the wide pullback, the limit of
   the family of monos.  A wide-pullback intersection is such a greatest
   lower bound (Riehl's prose under 4.7.9; in tree, for families indexed
   at the shape universe, Structure/WellPowered.v's
   [complete_intersection_IsIntersection]), and [IsIntersection] asks for
   no limit cone, so in this second respect alone the book's hypothesis
   implies this one: weaker than the book's, the safe direction.
   [special_initial_object_book] is the theorem over it, taken at the
   class of all subobjects.

   WELL-POWERED CATEGORIES.  Mac Lane's remark under §V.8 Definition 1,
   book p. 130 ([maclane:V.8:def1]): in a well-powered small-complete
   category every set of subobjects of an object has an intersection,
   so the extra hypothesis of Theorems 1 and 2 is automatic.
   [special_initial_object_wellpowered] is the theorem over Structure/
   WellPowered.v's [WellPowered] through #451's
   [wellpowered_complete_intersection_all], and
   [wellpowered_class_intersections] shows that [WellPowered] supplies
   [HasClassIntersections].  [special_initial_object_wellpowered_at] asks
   for well-poweredness at the ONE object [cogen_prod comp G] only,
   through Structure/WellPowered.v's per-object
   [wp_complete_class_intersection], and its index universe is bounded by
   [Complete]'s shape universe rather than pinned at the hom universe
   (the universes paragraph below).

   SMALL OBJECTS.  [special_initial_object_small] needs no intersection
   hypothesis at all: when the objects sit at or below [Complete]'s
   shape universe ([o <= so]), Structure/WellPowered.v's
   [complete_intersection_IsIntersection] intersects the whole family
   [SubObj (cogen_prod comp G)] from completeness alone.  At [so < o],
   the regime of the adjoint functor theorems, that route is refused
   (measured below).  Its own regime, objects and homs at or below the
   shape universe, is that of Structure/Complete/Freyd.v's
   [small_complete_is_thin] ([ArrowIndex C → Complete C → DecHom C →
   Thin C], the arrow index at [Complete]'s shape universe): at this
   corollary's universes, [small_complete_is_thin (canonical_ArrowIndex
   DO) comp D : Thin C] is accepted in a scratch file for [DO : ObjDecEq
   C] and [D : DecHom C], closed under the global context.  So a category
   this corollary reaches that has decidable object equality and
   decidable hom-setoids is thin.  The thin [Subsets X] of
   Adjunction/SAFT/InitialObject/Examples.v sits in the regime:
   [special_initial_object_small] at its completeness witness
   [Subsets_Complete_free X], objects at [o] and homs at [u] with
   [o <= u <= so], is accepted in a scratch file, closed under the
   global context.

   ** Strengths, measured

   Every constant here is a transparent [Definition] except
   [least_sub_arrows_agree], which proves [≈] between two arrows and is
   [Qed]; the [Initial] is built as [@Build_Terminal (C^op)], as
   Theory/WeaklyInitial.v's Freyd construction builds its own.  The
   readbacks, all [eq_refl]:

     - [special_initial_object_obj]: the object of
       [special_initial_object comp G w Hw] is [Subobject.sub_dom w];
     - [special_initial_object_zero]: its arrow to [c] is
       [cogen_pullback_to comp G c ∘ `1 (inter_le _ _ Hw
       (cogen_pullback_sub comp G c))];
     - [special_initial_object_book_obj]: the object is the domain of
       the intersection [HI] returns for the class of all subobjects;
     - [special_initial_object_wellpowered_obj] and
       [special_initial_object_wellpowered_at_obj]: the object is the
       domain of [complete_intersection] of the small reindexed family
       [wp_class_family (…) (fun _ => True)], the wide pullback of
       Structure/WellPowered.v.

   The zero arrow reads back as a composite whose factor [`1 (inter_le
   …)] is whatever the hypothesis supplies; at the well-powered forms it is
   Structure/WellPowered.v's lower-bound half, which its header records
   as computing as far as the witness's own [wp_to_from] does.  The
   normal form of the arrow at a concrete category was not measured.

   ** Universes, measured

   With [Set Printing Universes. About …], stdlib bounds omitted:

     special_initial_object@{o h so q u u0 u1} :
       ∀ {C : Category@{o h h}} (comp : Complete@{so so h o})
         (G : Cogenerator@{so o h} C)
         (w : SubObj@{o h} (cogen_prod@{so u so o h} comp G)),
       IsIntersection@{o h q} (λ m, m) w → @Initial C
       (* h < u, h < u0, so < u0, u < u1, o <= q, o <= u0, h <= so,
          h <= q *)

   Nothing relates [o] to [h] or [so]: in scratch compiles both the
   regime of Adjunction/SAFT.v's [SAFT] ([Complete@{h h h o}],
   [Cogenerator@{h o h}]) and [h < so] are accepted.  Of the rest, one
   constraint is the book's and two are inherited from donors.

   - [h <= so] is the book's "small hom-sets".  [cogen_power]'s index
     [{ j : cog_index G & c ~> cog_obj G j }] ([cogen_power_index], whose
     universe is bounded below by the hom universe) is handed to
     [Complete] as a discrete shape, so the shape universe must reach the
     homs.  Measured in a scratch file carrying this file's full import
     list, this file and Instance/Discrete.v, with [Complete]'s
     limit-datum universe [r] kept apart from [so] so that the binders
     alone do not force the bound: at [so < h <= r], with [comp :
     Complete@{r so h o} C] and [G : Cogenerator@{so o h} C], a statement
     with a trivial body is accepted (the instrument), [cogen_prod comp
     G] is accepted (the control), and [comp _ (DiscreteCat_Functor
     (cogen_power_fam G c))], the body of [cogen_power_limit] with its
     shape argument left to unification, is refused at the functor (<1>
     to <4> stand for universes the scratch compile generated, numbered
     by first appearance, as Test/ProbeSpecialInitial452.v writes them):
       "The term "DiscreteCat_Functor (cogen_power_fam G c)" has type
        "@Functor@{<1> <2> <3> o h h} (DiscreteCat@{<1> <2> <3>}
        (@cogen_power_index@{<4> so o h} C G c)) C" while it is expected
        to have type "@Functor@{so h h o h h} ?D C" (universe
        inconsistency: Cannot enforce <1> = so because so < h <= <4> <=
        <1>)".
     At [h <= so] the same term is accepted.
     Test/ProbeSpecialInitial452.v's N5, labelled P_H_le_so
     ([p452_n5_power_limit_small_shape]), pins this refusal, beside the
     instrument [p452_binder_ok] and the controls [p452_prod_small_shape]
     and [p452_power_limit_ok]; its import list loads Instance/Discrete.v
     without importing it, so there the two names print as
     [Discrete.DiscreteCat_Functor] and [Discrete.DiscreteCat].  In the
     statements here the bound is ALSO implied by the binder:
     [Complete@{r so h o}] declares [so <= r] and [h <= r] ([About
     Complete]), and with [r] collapsed onto [so] (the limit-datum bullet
     below) [h <= r] is [h <= so].  So a statement over [Complete@{so so
     h o}] at [so < h] is refused whatever its body, over the whole
     command, with "Universe inconsistency. Cannot enforce h <= so
     because so < h."; that refusal measures the binder, not the power,
     and the probe's N4 ([p452_n4_binder_collapsed]) pins it as such.
     The bound is the one Structure/Complete.v's size note, item 2(c),
     records for Freyd's route, arriving here through the hom-indexed
     power rather than through the equalizer of all endomorphisms.

   - The cogenerating family's index universe EQUALS [so].  This is a
     donor collapse of Adjunction/SAFT.v's unannotated [cogen_prod_limit]
     and [cogen_prod]: [About cogen_prod] reads [cogen_prod@{u u0 u1 u2
     u3} : Complete@{u1 u u3 u2} → Cogenerator@{u u2 u3} C → obj[C]],
     the same [u] in both.  With [G : Cogenerator@{c o h} C] and
     [c < so], [cogen_prod comp G] is refused: "The term "G" has type
     "Cogenerator@{c o h} C" while it is expected to have type
     "Cogenerator@{so o h} C" (universe inconsistency: Cannot enforce
     c = so because c < so)", while [cogen_power comp G x], whose shape
     is a Σ over the index, is accepted at the same [c < so].  The
     record [Cogenerator] is not cumulative, so a caller whose family
     sits lower must repackage it.

   - The limit-datum universe of [Complete] (its first slot) EQUALS
     [so].  This is a donor collapse of the unannotated
     [cogen_power_limit] and [cogen_power]: [About cogen_power_limit]
     reads [Complete@{u2 u2 u0 u} → … Limit@{u2 u2 u0 u} …].  With
     [comp : Complete@{r so h o}] and [so < r], [cogen_power comp G x]
     is refused: "The term "comp" has type "Complete@{r so h o}" while
     it is expected to have type "Complete@{so so h o}" (universe
     inconsistency: Cannot enforce r = so because so < r)", while
     [cogen_prod comp G] is accepted at the same [so < r].

   Neither collapse is repaired here: annotating [cogen_prod] and
   [cogen_power] would change the signatures Adjunction/SAFT.v's header
   quotes.  The statements therefore take [Complete@{so so h o}] and
   [Cogenerator@{so o h}], which is [SAFT]'s own regime at [so = h].

   The binders are load-bearing.  Unannotated copies minimized [so] onto
   [h]: a bare [special_initial_object_least] read [Complete@{u3 u3 u3
   u2}] and [Cogenerator@{u3 u2 u3}], and a bare [cogen_prod_to_power]
   read [Complete@{u0 u0 u0 u1}].  The intersection's index [q] is bound
   only by [o <= q, h <= q]: the class of all subobjects is large, and it
   is not tied to [so].  [d] names the internal universe of
   [cogen_prod] ([h < d], from Instance/Discrete.v's
   [DiscreteCat_Functor]) wherever a statement mentions [cogen_prod]
   next to [WellPoweredAt] or [HasClassIntersections]; before it was
   named, minimization identified it with [SubObj_Setoid]'s upper
   universe [t], and the readbacks [special_initial_object_book_obj] and
   [special_initial_object_wellpowered_obj] carried the constraint
   [t = d].

     HasClassIntersections@{o h p q s t k} : Category@{o h h} → Type@{k}
       (* h < t, p < k, o <= q, o <= s, o <= k, h <= q, h <= s, h <= k,
          p <= q, q <= k *)
     special_initial_object_wellpowered@{o h w s t so d …} :
       WellPowered@{o h w s t} C → Complete@{so so h o} →
       Cogenerator@{so o h} C → @Initial C
       (* w <= h, w <= so, h <= so, h < t, h < d, o <= s, h <= s, … *)
     special_initial_object_wellpowered_at@{o h w s t so d …} :
       Complete@{so so h o} → Cogenerator@{so o h} C →
       WellPoweredAt@{w o s h t} (cogen_prod@{so d so o h} comp G) →
       @Initial C
       (* w <= so, h <= so, h < t, h < d, o <= s, h <= s, … *)
     special_initial_object_small@{o h so …} :
       Complete@{so so h o} → Cogenerator@{so o h} C → @Initial C
       (* o <= so, h <= so, … *)

   In [HasClassIntersections], [p] is the class's universe, [q] the
   family index, [s] and [t] the two universes of [SubObj_Setoid], [k]
   the sort.  All seven are named so that a consumer can write the
   instance: with only [o h p q] named and a trailing [+], the instance
   [HasClassIntersections@{o h p q}] is refused ("Universe instance
   length for HasClassIntersections is 4 but should be 7").  The
   per-object corollary carries [w <= so] but not [w <= h]: only
   [WellPowered]'s pin puts the index at the hom universe, and a scratch
   control at [h < w <= so] is accepted.  The small route is refused at
   [so < o] with "Found type "SubObj (cogen_prod comp G)" where "?J" was
   expected (unable to find a well-typed instantiation for "?J": cannot
   ensure that "Type@{max(o,h)}" is a subtype of "Type@{…}")", the
   family's index being the large type of subobjects.

   Every refusal quoted in this header was measured by compiling the
   bare statement in a scratch file against this file's import list,
   where it stops with the quoted error, and each has an accepted
   control: the one named beside it or, for the small route and the two
   Freyd comparisons below, the constant of this file stated where it
   holds ([special_initial_object_small] at [o <= so],
   [special_vs_freyd] at [so = h], [freyd_of_cogenerator] with the index
   equal to [h]).  Test/ProbeSpecialInitial452.v pins all of them but
   the instance-length refusal, each beside a control: N2
   ([p452_n2_prod_low_index]) and N3 ([p452_n3_power_high_datum]) the two
   donor collapses; N5, labelled P_H_le_so, the [h <= so] bound, and N4
   the binder's own refusal (both above); N6 ([p452_n6_small_route]) the
   small route, and N7 ([p452_n7_small_index]) the same with the family's
   index given; N8 ([p452_n8_freyd_above]) the comparison with Freyd at
   [h < so]; and N9 ([p452_n9_freyd_wif_low]) Freyd's construction fed
   [wif_of_cogenerator] with its index below the homs.

   ** Relation to Freyd's construction

   Theory/WeaklyInitial.v's [initial_from_weakly_initial] carves the
   initial object out of the product of a small weakly initial family as
   the joint equalizer of all its endomorphisms.  The special route
   takes the least subobject of the cogenerator product instead, and its
   halves line up with Freyd's: the existence half makes the least
   subobject's domain weakly initial ([special_weakly_initial]), and the
   uniqueness half replaces the equalizer of all endomorphisms by the
   equalizer of the one pair of arrows in question.  [special_vs_freyd]
   compares the two objects on that singleton family, by Structure/
   Initial.v's [initial_unique].  Two limits, measured:

   - the in-tree comparison is stated only at [so = h], because
     [initial_from_weakly_initial_complete] pins its universes: [About
     initial_from_weakly_initial_complete] reads [Complete@{u1 u1 u1
     u0} → HasEqualizers C → WeaklyInitialFamily@{u1 u0 u1} C →
     Terminal …], one universe for the shape objects, the limit datum and
     the homs.  With [comp : Complete@{so so h o}] and [h < so] the
     comparison is refused: "The term "comp" has type "Complete@{so so h
     o}" while it is expected to have type "Complete@{…}" (universe
     inconsistency: Cannot enforce h = so because h < so)".  That is a
     limit of the one constant's signature, not of the mathematics: any
     two initial objects are isomorphic, and a comparison through a Freyd
     construction with its universes kept apart is not attempted here;
   - Freyd's object does not read back.  [initial_from_weakly_initial]
     ends in [Qed] ([About]: "initial_from_weakly_initial is opaque"),
     so [special_vs_freyd] relates an object that reads back by
     [eq_refl] to one that does not.

   The solution set at the level of objects -- the object-level
   counterpart of the one Adjunction/SAFT.v's [SAFT] assembles for [GAFT]
   from subobjects of [cogen_prod], and not a step of Mac Lane's §V.8
   proofs, which go through Theorem 1's intersection -- is
   [wif_of_cogenerator]: given well-poweredness at the one object
   [cogen_prod comp G], the subobjects of that product, indexed by
   [wp_index], form a weakly initial family, with no intersection taken.
   [freyd_of_cogenerator] feeds it to Freyd's construction and
   [special_vs_freyd_of_cogenerator] compares the result with
   [special_initial_object_wellpowered_at].  The measured difference is
   the index universe: [wif_of_cogenerator] returns
   [WeaklyInitialFamily@{w o h}] with [w] free, the special route bounds
   [w <= so], and [freyd_of_cogenerator] takes [WellPoweredAt@{h o s h
   t}], its index EQUAL to the hom universe, because the record
   [WeaklyInitialFamily] is not cumulative and
   [initial_from_weakly_initial_complete] takes it at [@{u1 u0 u1}].
   With the index [w < h], feeding [wif_of_cogenerator comp G W] to
   [initial_from_weakly_initial_complete] is refused: "The term
   "wif_of_cogenerator comp G W" has type … while it is expected to have
   type "WeaklyInitialFamily@{h o h} C" (universe inconsistency: Cannot
   enforce w = h because w < h)".

   ** What #453 needs from here

   Mac Lane's proof of the special adjoint functor theorem (§V.8,
   Theorem 2) applies this theorem in the comma category d↓U, whose
   cogenerating family is indexed by the arrows OUT OF d.  That product
   depends on d, and Adjunction/SAFT.v's [cogen_prod] does not, which is
   why [SAFT]'s covering datum is refutable (that file's header).  The
   comma route is #453's, and what it is expected to consume from here
   is a forecast, not a measurement: the theorem over an arbitrary
   category, transparent and with its object readback; both hypothesis
   forms and their conversions; the per-object corollary
   [special_initial_object_wellpowered_at]; and optionally
   [wif_of_cogenerator], which with Adjunction/GAFT.v's [sols_of_wif]
   would keep [GAFT]'s solution-set route at the cost of the index
   identification above, a cost not measured.  One instantiation is
   measured: in a scratch file, [special_initial_object_least
   (@Comma_Complete C D U d HU HC) G w Hw : @Initial (=(d) ↓ U)], with
   [HU : PreservesImageLimit U], [HC : Complete C], [G] a [Cogenerator]
   of the comma category and [w] a least subobject of its [cogen_prod],
   is accepted unannotated and closed under the global context;
   minimization puts [HC] at [Complete@{h h h o}] and [G] at
   [Cogenerator@{h … h}], [SAFT]'s regime [so = h], and the instance at
   [h < so] was not measured.  The lifted cogenerator of the comma
   category is not built here.

   ** Non-vacuity

   Adjunction/SAFT/InitialObject/Examples.v applies the well-powered
   corollary with no hypothesis at two categories: the powerset lattice
   [Subsets X] of any setoid, where the initial object is isomorphic to
   [Subsets_Initial]'s bottom and provably empty, and
   [Indiscrete@{o j j} Type@{j}], objects strictly above homs, where
   every object is initial.  At both the least subobject is computed as
   a wide pullback, not supplied from a known initial object.  Both
   categories are thin, so every family cogenerates them, the empty one
   included, and [cog_separates] does no work there.
   Instance/Sets/SpecialInitial.v applies the theorem at categories that
   are not thin: at [Sets^op] unconditionally, with the genuine
   cogenerator [cog_of_gen Sets_Generator] (its least subobject built
   from the known initial object, as that file's circularity caveat
   says), and at [Sets] under [Untruncate] or [IEM].

   ** Not delivered

   [SAFT] is not re-shaped and no comma cogenerator is built (#453).
   [cogen_prod] and [cogen_power] are not annotated, so the two donor
   collapses above stand.  No [Cogenerator] of a category that is not
   thin is built in this file or its satellite (Instance/Sets/
   Cogenerator.v and Instance/Sets/SpecialInitial.v build them at [Sets]
   and [Sets^op]).  The normal form of the zero arrow at a concrete
   category was not measured.  This file itself pins none of the
   refusals above; Test/ProbeSpecialInitial452.v pins all of them but
   the instance-length refusal of [HasClassIntersections] (the universes
   section names which negative pins which).

   MEASUREMENTS.  Twenty-nine constants ([Print Module]), no [Program]
   obligation; each reports "Closed under the global context" by its
   fully qualified name.  Closure 110 files excluding itself, counted
   over .Makefile.coq.d, the same as Adjunction/SAFT/WellPowered.v's. *)

(** ** Uniqueness: parallel arrows out of a least subobject agree *)

Definition equalizer_sub@{o h +} {C : Category@{o h h}} {x : C} (w : SubObj x)
  {c q : C} {f g : Subobject.sub_dom w ~> c} {e : q ~> Subobject.sub_dom w}
  (E : IsEqualizer f g q e) : SubObj x :=
  @Build_SubObj C x q (Subobject.sub_mono w ∘ e)
    (monic_compose (Subobject.sub_is_monic w) (equalizer_monic f g E)).

Lemma least_sub_arrows_agree@{o h +} {C : Category@{o h h}}
  (HE : HasEqualizers C) {x : C}
  (w : SubObj x) (Hw : ∀ v : SubObj x, sub_le w v)
  {c : C} (f g : Subobject.sub_dom w ~> c) : f ≈ g.
Proof.
  destruct (@equalizer C HE _ _ f g) as [q [e E]].
  destruct (Hw (equalizer_sub w E)) as [s Hs]; simpl in Hs.
  assert (Hes : e ∘ s ≈ id).
  { apply (monic (Monic := Subobject.sub_is_monic w)).
    rewrite comp_assoc, Hs; cat. }
  rewrite <- (id_right f), <- (id_right g), <- Hes, !comp_assoc.
  now rewrite (fork_eq E).
Qed.

(** ** Existence: the pullback of the canonical monic *)

(* Mac Lane's k : q_0 → ∏_H q, whose component at [(j, h)] is the [j]-th
   projection of the cogenerator product. *)
Definition cogen_prod_to_power@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :
  cogen_prod comp G ~> cogen_power comp G c :=
  unique_obj (iprod_ump (cogen_power_fam G c) (cogen_power_limit comp G c)
                (cogen_prod comp G)
                (fun p => iprod_proj (cog_obj G) (cogen_prod_limit comp G)
                            (projT1 p))).

(* [c] as a subobject of its power: the separation content. *)
Definition cogen_canonical_sub@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) : SubObj (cogen_power comp G c) :=
  @Build_SubObj C (cogen_power comp G c) c (cogen_canonical comp G c)
    (cogenerator_canonical_monic comp G c).

Definition complete_pullbacks@{o h r so +| so <= r, h <= r +}
  {C : Category@{o h h}} (comp : @Complete@{r so h o} C) : HasPullbacks C :=
  FinitelyComplete_HasPullbacks (Complete_FinitelyComplete comp).

(* Its pullback along k: a subobject of the cogenerator product. *)
Definition cogen_pullback_sub@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) : SubObj (cogen_prod comp G) :=
  @sub_reindex C (complete_pullbacks comp) _ _
    (cogen_prod_to_power comp G c) (cogen_canonical_sub comp G c).

Definition cogen_pullback_to@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (c : C) :
  Subobject.sub_dom (cogen_pullback_sub comp G c) ~> c :=
  pullback_snd _ _ (@pullback C (complete_pullbacks comp) _ _ _
                      (cogen_prod_to_power comp G c)
                      (cogen_canonical comp G c)).

(* The arrow out of a least subobject: below the pullback, then its leg. *)
Definition special_initial_zero@{o h so +| h <= so +} {C : Category@{o h h}}
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) (c : C) :
  Subobject.sub_dom w ~> c :=
  cogen_pullback_to comp G c ∘ `1 (Hw (cogen_pullback_sub comp G c)).

(** ** The theorem over a least subobject *)

Definition special_initial_object_least@{o h so +| h <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) : @Initial C.
Proof.
  unshelve refine (@Build_Terminal (C^op) (Subobject.sub_dom w) _ _).
  - intro c.
    exact (special_initial_zero comp G w Hw c).
  - intros c f g.
    exact (@least_sub_arrows_agree C (Complete_HasEqualizers comp) _ w Hw
             c f g).
Defined.

(** ** The intersection of all subobjects is the least subobject *)

Definition least_of_intersection_all@{o h q +| o <= q, h <= q +}
  {C : Category@{o h h}} {x : C} (w : SubObj x)
  (Hw : IsIntersection@{o h q} (fun m : SubObj x => m) w) :
  ∀ v : SubObj x, sub_le w v :=
  inter_le _ _ Hw.

Definition intersection_all_of_least@{o h q +| o <= q, h <= q +}
  {C : Category@{o h h}} {x : C} (w : SubObj x)
  (Hw : ∀ v : SubObj x, sub_le w v) :
  IsIntersection@{o h q} (fun m : SubObj x => m) w :=
  @Build_IsIntersection C x (SubObj x) (fun m : SubObj x => m) w
    Hw (fun v Hv => Hv w).

(** ** The theorem: the intersection of all subobjects of the product *)

Definition special_initial_object@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @Initial C :=
  special_initial_object_least comp G w (least_of_intersection_all w Hw).

Example special_initial_object_obj@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  @initial_obj C (special_initial_object comp G w Hw) = Subobject.sub_dom w :=
  eq_refl.

Example special_initial_object_zero@{o h so q +| h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w)
  (c : C) :
  @zero C (special_initial_object comp G w Hw) c
    = cogen_pullback_to comp G c
        ∘ `1 (inter_le _ _ Hw (cogen_pullback_sub comp G c)) :=
  eq_refl.

(* The conclusion read in the type: the intersection's domain IS initial. *)
Definition special_initial_IsInitialObj@{o h so q +|
    h <= so, o <= q, h <= q +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : IsIntersection@{o h q} (fun m : SubObj (cogen_prod comp G) => m) w) :
  IsInitialObj (Subobject.sub_dom w) :=
  IsInitialObj_from_Initial (special_initial_object comp G w Hw).

(** ** Mac Lane's hypothesis: every class of subobjects has an intersection *)

Definition HasClassIntersections@{o h p q s t k |
    o <= s, h <= s, h < t, o <= q, h <= q, p <= q,
    p < k, o <= k, h <= k, q <= k +}
  (C : Category@{o h h}) : Type@{k} :=
  ∀ (x : C) (P : SubObj@{o h} x → Type@{p}),
    (∀ m m' : SubObj x, m ≈ m' → P m → P m') →
    { w : SubObj x &
      IsIntersection@{o h q} (fun k : { m : SubObj x & P m } => `1 k) w }.

(* The book's statement, at the class of all subobjects. *)
Definition special_initial_object_book@{o h so p q s t k d +|
    h <= so, h < d +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (HI : HasClassIntersections@{o h p q s t k} C) :
  @Initial C.
Proof.
  refine (special_initial_object_least comp G
            (`1 (HI (cogen_prod@{so d so o h} comp G) (fun _ => unit)
                   (fun _ _ _ t => t)))
            _).
  intro v.
  exact (inter_le _ _
           (`2 (HI (cogen_prod@{so d so o h} comp G) (fun _ => unit)
                  (fun _ _ _ t => t)))
           (existT _ v tt)).
Defined.

Example special_initial_object_book_obj@{o h so p q s t k d +|
    h <= so, h < d +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (HI : HasClassIntersections@{o h p q s t k} C) :
  @initial_obj C (special_initial_object_book comp G HI)
    = Subobject.sub_dom
        (`1 (HI (cogen_prod@{so d so o h} comp G) (fun _ => unit)
               (fun _ _ _ t => t))) :=
  eq_refl.

(** ** Well-powered categories: the hypothesis discharged *)

Definition wellpowered_class_intersections@{o h w s t so p q k +|
    w <= h, h < t, o <= s, h <= s, w <= so, p <= so,
    o <= q, h <= q, p <= q +}
  {C : Category@{o h h}} (WP : WellPowered@{o h w s t} C)
  (comp : @Complete@{so so h o} C) : HasClassIntersections@{o h p q s t k} C :=
  fun x P HP => wellpowered_complete_has_intersections WP comp x P HP.

(* Mac Lane's remark under §V.8 Definition 1. *)
Definition special_initial_object_wellpowered@{o h w s t so d +|
    w <= h, h < t, h < d, o <= s, h <= s, h <= so, w <= so +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (`2 (wellpowered_complete_intersection_all WP comp
          (cogen_prod@{so d so o h} comp G))).

Example special_initial_object_wellpowered_obj@{o h w s t so d +|
    w <= h, h < t, h < d, o <= s, h <= s, h <= so, w <= so +}
  {C : Category@{o h h}}
  (WP : WellPowered@{o h w s t} C) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) :
  @initial_obj C (special_initial_object_wellpowered WP comp G)
    = Subobject.sub_dom
        (complete_intersection comp
           (wp_class_family (WP (cogen_prod@{so d so o h} comp G))
              (fun _ => True))) :=
  eq_refl.

(* Well-poweredness at the ONE object [cogen_prod comp G] suffices. *)
Definition special_initial_object_wellpowered_at@{o h w s t so d +|
    h < t, h < d, o <= s, h <= s, h <= so, w <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{so d so o h} comp G)) :
  @Initial C.
Proof.
  refine (special_initial_object_least comp G
            (`1 (wp_complete_class_intersection comp W (fun _ => True)
                   (fun _ _ _ t => t))) _).
  intro v.
  exact (inter_le _ _
           (`2 (wp_complete_class_intersection comp W (fun _ => True)
                  (fun _ _ _ t => t)))
           (existT _ v I)).
Defined.

Example special_initial_object_wellpowered_at_obj@{o h w s t so d +|
    h < t, h < d, o <= s, h <= s, h <= so, w <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{so d so o h} comp G)) :
  @initial_obj C (special_initial_object_wellpowered_at comp G W)
    = Subobject.sub_dom
        (complete_intersection comp (wp_class_family W (fun _ => True))) :=
  eq_refl.

(** ** Small objects: completeness alone intersects all subobjects *)

Definition special_initial_object_small@{o h so +| h <= so, o <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) : @Initial C :=
  special_initial_object comp G _
    (complete_intersection_IsIntersection comp
       (fun m : SubObj (cogen_prod comp G) => m)).

(** ** Relation to Freyd's construction *)

(* The existence half alone: the least subobject is weakly initial. *)
Definition special_weakly_initial@{o h so +| h <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C) (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  WeaklyInitial (Subobject.sub_dom w) :=
  special_initial_zero comp G w Hw.

(* Freyd's construction on that singleton family, at [so = h]. *)
Definition special_vs_freyd@{o h +} {C : Category@{o h h}}
  (comp : @Complete@{h h h o} C) (G : Cogenerator@{h o h} C)
  (w : SubObj (cogen_prod comp G))
  (Hw : ∀ v : SubObj (cogen_prod comp G), sub_le w v) :
  @initial_obj C (special_initial_object_least comp G w Hw)
  ≅ @initial_obj C
      (initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
         (wif_of_weakly_initial (special_weakly_initial comp G w Hw))) :=
  initial_unique _ _.

(* The subobjects of the cogenerator product, indexed by a well-powered
   datum at that one object, are a weakly initial family. *)
Definition wif_of_cogenerator@{o h w s t so d +|
    h < t, h < d, o <= s, h <= s, h <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{so o h} C)
  (W : WellPoweredAt@{w o s h t} (cogen_prod@{so d so o h} comp G)) :
  WeaklyInitialFamily@{w o h} C.
Proof.
  refine (Build_WeaklyInitialFamily C (wp_index W)
            (fun i => Subobject.sub_dom (wp_to W i)) _).
  intro c.
  exists (wp_from W (cogen_pullback_sub comp G c)).
  exact (cogen_pullback_to comp G c
           ∘ `1 (sub_le_of_equiv _ _
                   (wp_to_from W (cogen_pullback_sub comp G c)))).
Defined.

Definition freyd_of_cogenerator@{o h s t d +|
    h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{h o s h t} (cogen_prod@{h d h o h} comp G)) :
  @Initial C :=
  initial_from_weakly_initial_complete comp (Complete_HasEqualizers comp)
    (wif_of_cogenerator comp G W).

Definition special_vs_freyd_of_cogenerator@{o h s t d +|
    h < t, h < d, o <= s, h <= s +}
  {C : Category@{o h h}} (comp : @Complete@{h h h o} C)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{h o s h t} (cogen_prod@{h d h o h} comp G)) :
  @initial_obj C (special_initial_object_wellpowered_at comp G W)
  ≅ @initial_obj C (freyd_of_cogenerator comp G W) :=
  initial_unique _ _.
