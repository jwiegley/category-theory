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

Generalizable All Variables.

(** * The special adjoint functor theorem, as a characterization *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab:      https://ncatlab.org/nlab/show/well-powered+category
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.8, Theorem 2, the unnumbered Lemma inside its proof and the
   Corollary after it, book pp. 129-130 (PDF pp. 138-139; catalogue ids
   [maclane:V.8:thm2], [maclane:V.8:lem1], [maclane:V.8:cor1]).  Awodey,
   "Category Theory", §9.8, Remark 9.35, printed pp. 255-256
   ([awodey:9.8:remark35]).  Riehl, "Category Theory in Context",
   Theorem 4.7.10 and Corollary 4.7.13, printed pp. 177-178
   ([riehl:4.7:thm10], [riehl:4.7:cor13]), and the Epilogue's two
   restatements, printed p. 252 ([riehl:E.1:thm-gaft] clause (iii),
   [riehl:E.1:thm-representability-criteria] clause (i)).  CITED BY
   LOCATION AND BY THE IN-TREE CATALOGUE: the printed books were not
   consulted for this file, and every statement attributed to them below
   is the catalogue's summary, read from doc/plan/books/maclane/
   inventory/V.json, doc/plan/books/awodey/inventory/inventory-9.json
   and doc/plan/books/riehl/inventory/inventory-4.json and
   inventory-E.json.  Mac Lane's three items read there:

     thm2 -- "Let A be small-complete with small hom-sets and a small
     cogenerating set Q, and suppose every set of subobjects of an
     object of A has a pullback (hence an intersection).  Let X have
     small hom-sets.  Then a functor G : A -> X has a left adjoint if
     and only if G preserves all small limits and all pullbacks of
     families of monics."

     lem1 -- an arrow of the comma category (x ↓ G) is monic if and only
     if its underlying arrow in A is; for the harder half "the comma
     projection ... creates all limits (by the lemma of section 6), in
     particular kernel pairs, and A has all kernel pairs, so the
     projection preserves kernel pairs".

     cor1 -- "If A is small-complete, well-powered, with small hom-sets
     and a small cogenerating set, and X has small hom-sets, then a
     functor G : A -> X has a left adjoint if and only if it is
     continuous (preserves all small limits).  In particular, every
     continuous functor K : A -> Set is representable."

   Awodey's Remark 9.35 is cor1's sufficiency (a complete, locally small,
   well-powered category with a cogenerating set; a functor out of it
   that preserves limits has a left adjoint; the proof is referred to
   Mac Lane).  Riehl's 4.7.10 is taken up in the fidelity paragraph
   below.  The representability half of cor1 (with Riehl's E.1
   criterion) and Riehl's 4.7.13 are the satellite Adjunction/SAFT/
   Characterization/Corollaries.v's; this file proves the theorem, the
   lemma and the adjoint half of the Corollary.

   ** What is proved

   THE MONOS LEMMA, STRONGER THAN THE BOOK.  [comma_monic_of_underlying]:
   an arrow of [=(d) ↓ U] whose C-component is monic is monic, with no
   hypothesis.  [underlying_monic_of_comma_monic]: the converse, from ONE
   kernel pair [K] of the underlying arrow in C and nothing about [U].
   The kernel-pair object takes the comma structure [fmap[U] (kp_diag m
   K) ∘ `2 X] through its diagonal [kp_diag] ([kp_obj]); both projections
   are then comma arrows into [X] ([kp_fst], [kp_snd], whose triangles
   close by [kp_diag_fst] and [kp_diag_snd]); the comma-monic [m]
   equalizes them; and a pair [g1 g2 : z ~> a] equalized by the
   underlying arrow factors through the kernel pair, so [z] need carry
   no comma structure.  [comma_monic_iff_underlying_monic] is the book's
   biconditional over [HasPullbacks C].  Mac Lane's route asks the comma
   projection to create kernel pairs, which needs G to preserve them;
   here G preserves nothing, so the lemma holds for every functor, and
   #438's Construction/Comma/Creation.v is neither needed nor imported.
   That some object with a comma structure must receive the pair is a
   meta-argument, not built here: two arrows out of an object with no
   arrow from [d] into its image under [U] are invisible to the comma.

   THE COMMA'S COGENERATING FAMILY.  [comma_cogenerator]: a cogenerating
   family [G] of C gives the family of comma objects [(cog_obj G j, k)],
   indexed by [{ j : cog_index G & d ~> U (cog_obj G j) }] -- Mac Lane's
   Q', indexed by the arrows OUT OF [d] -- and separation descends to
   [cog_separates G].  It was prototyped for #452 and is landed here.

   WELL-POWEREDNESS OF THE COMMA.  [comma_WellPoweredAt]: well-
   poweredness of C at the underlying object of [X] gives well-
   poweredness of the comma at [X].  Its index [comma_wp_index] pairs a
   C-subobject index with a factorization of [X]'s structure arrow
   through [fmap[U]] of that subobject's mono.  [comma_wp_to] uses the
   easy half of the monos lemma and [comma_wp_from] the hard half,
   through [underlying_sub], a comma subobject read in C;
   [comma_wp_to_from] lifts the C-isomorphism of [wp_to_from] to the
   comma.  [U] preserving monos is never asked for: the stored
   factorization makes the reverse triangle hold by construction.
   [comma_WellPowered] does so at every object.

   THE COROLLARY, TRANSPARENT (Mac Lane cor1, Awodey 9.35).
   [SAFT_wellpowered U comp cont G WP : { F : D ⟶ C & F ⊣ U }] takes
   [comp : Complete C], [cont : PreservesImageLimit U] (Construction/
   Comma/Limit.v's cone-level continuity), [G : Cogenerator C]
   (Adjunction/SAFT.v) and [WP : WellPowered C] (#451's Structure/
   WellPowered.v), and nothing else: no covering datum and no subobject
   index.  At each [d], [SAFT_comma_initial] is #452's
   [special_initial_object_wellpowered_at] in the comma, fed
   [Comma_Complete cont comp], [comma_cogenerator U d G] and
   [comma_WellPoweredAt] at the comma's cogenerator product;
   [SAFT_universal_arrow] packages it; [SAFT_left] is Theory/Universal/
   Arrow.v's transparent [LeftAdjointFunctorFromUniversalArrows] and
   [SAFT_adjunction] its [AdjunctionFromUniversalArrows]; and
   [SAFT_wellpowered] is the pair.  Adjunction/GAFT.v's
   [GAFT_from_initials] does the same assembly and ends in [Qed]; it is
   not used.  [SAFT_wellpowered_iff] is the Corollary's biconditional,
   left adjoint ↔ [PreservesImageLimit U], its necessity Construction/
   Comma/Limit.v's [right_adjoint_PreservesImageLimit].

   Where [U] preserves the intersection in the Corollary: #452's
   theorem takes it as Structure/WellPowered.v's [complete_intersection]
   in the comma, the wide pullback of a family indexed at [Complete]'s
   shape universe ([wp_class_family]), built from the comma's products
   and equalizers, which [Comma_Complete] creates from C's through
   [cont].  Mac Lane's second preservation clause is spent inside
   continuity there, and the Corollary's "continuous" is all it asks.

   THEOREM 2.  [HasSubobjectWidePullbacks C]: every family of subobjects
   of an object of C, indexed by a type at a universe [q], has a wide
   pullback.  That is the book's "every set of subobjects of an object of
   A has a pullback", read as a LIMIT (Structure/Pullback/Wide.v's
   [WidePullback]) and with the index a universe parameter (the class
   reading, for the reason Structure/WellPowered.v's header gives: a set
   of subobjects is a set of equivalence classes, carried by a large
   family).  "Preserves all pullbacks of families of monics" is
   Adjunction/SpanningArrow.v's [PreservesWidePullbacks] (#448), reused
   unchanged.  [SAFT_thm2 U comp cont G HW HU] builds at each [d] the
   least subobject of the comma's cogenerator product [X]: [least_index U
   d X] is Mac Lane's corresponding family, the C-subobjects of [X]'s
   underlying object through which [X]'s structure arrow factors
   ([SubFactorsThrough]); [HW] intersects it in C; [HU] makes [U]'s image
   of that wide pullback a wide pullback, whose mediator [least_lift] is
   the D-arrow that makes the intersection a comma object ([least_dom]);
   [least_sub] is the resulting subobject and [least_le] its leastness,
   witnessed by the projection at [least_index_of v], a comma subobject
   read in C with its own factorization.  Only the existence half of
   [HU]'s universal property is used, and #452's
   [special_initial_object_least] consumes only [∀ v, sub_le w v].  The
   adjoint is assembled as in the Corollary ([SAFT_thm2_initial],
   [SAFT_thm2_universal_arrow], [SAFT_thm2_left],
   [SAFT_thm2_adjunction]).  For an empty family,
   Structure/Pullback/Wide.v's [WidePullback] has no leg to [x] and is a
   terminal object (that file's paragraph THE EMPTY INDEX IS A REAL
   BOUNDARY), so [HasSubobjectWidePullbacks] asks there for a terminal
   object, not for [x] as Mac Lane's pullback of an empty set of
   subobjects of [x] is, and [PreservesWidePullbacks] asks [U] to
   preserve it.  The proof never consults that case, since [least_index]
   always holds [least_top]; a terminal object is the limit of the empty
   diagram, which [Complete] provides (not restated as a constant here).
   [Complete_HasSubobjectWidePullbacks] is the route from completeness,
   at every index universe [q <= so].
   [right_adjoint_PreservesWidePullbacks] is the necessity of the second
   clause, absent from the tree before this file (at master 9613c9a5 a
   grep for the name over the .v files found no file; the same grep for
   [right_adjoint_PreservesImageLimit] found eight): a right adjoint
   preserves every wide pullback, of monos or not, at every index
   universe; the monicity clause of [PreservesWidePullbacks] is accepted
   and ignored, as in Instance/Mod/Spanning.v's
   [Bilin_PreservesWidePullbacks].  The proof transposes along [adj] with
   [from_adj_nat_r], [to_adj_nat_r] and [from_adj_comp_law], since a wide
   pullback has no shape category for Adjunction/Continuity.v's
   [rapl_ump] (Adjunction/SpanningArrow.v's "WHY [PreservesWidePullbacks]
   IS BESPOKE"); with the [Require] of Instance/Sets.v dropped, its [from
   (adj ...) (q i)] is refused ("Illegal application (Non-functional
   construction)", measured).  [SAFT_iff] is Theorem 2 as the book states
   it: left adjoint ↔ [PreservesImageLimit U * PreservesWidePullbacks U].

   WHY #452's [HasClassIntersections] CANNOT BE THEOREM 2's HYPOTHESIS.
   It asks for a greatest lower bound in the subobject order (Theory/
   Subobject/Lattice.v's [IsIntersection]) and carries no limit cone.
   The comma step needs the intersection [w] of the corresponding family
   to receive [X]'s structure arrow, an arrow [d ~> U w] over the arrows
   [d ~> U m_k]; that is a mediator into [U]'s image of a LIMIT cone,
   which [HU] supplies for a wide pullback, and a glb gives [U] no cone
   to preserve.  Adjunction/SAFT/InitialObject.v's header reads the glb
   form as weaker than the book's hypothesis and so safe for Theorem 1;
   for Theorem 2 it is the other direction.  A bridge from
   [HasSubobjectWidePullbacks] to [HasClassIntersections] through
   Lattice.v's [sub_wide_intersection_IsIntersection] is not written.

   IN TREE, THEOREM 2 IS APPLIED ONLY AT A THIN CATEGORY.  Completeness
   supplies [HasSubobjectWidePullbacks] at every index [q <= so],
   whatever the objects' universe ([Complete_HasSubobjectWidePullbacks]),
   and Theorem 2 asks it at [q] at or above the objects, where
   [least_index] lives ([o <= lq], [About least_index];
   Test/ProbeSAFT453.v's N26, [p453_n26_least_index_small], refuses
   [least_index] handed to [HW] at [q < o], beside the control
   [p453_least_index_at_objects]); so completeness serves Theorem 2 only
   when the objects fit in the shape universe.  In a scratch file
   carrying this file's import list, the same term asked for the index at
   the objects' universe, [fun x I S => complete_wide_pullback comp (fun
   i => Subobject.sub_mono (S i)) : HasSubobjectWidePullbacks@{o h o o k}
   C] from [comp : Complete@{so so h o} C], is accepted at [o <= so, h <=
   so], closed under the global context, and refused at [so < o], at the
   index: "The term "i" has type "?J" while it is expected to have type
   "I" (unable to find a well-typed instantiation for "?J": cannot ensure
   that "Type@{o}" is a subtype of "Type@{…}")".  Test/ProbeSAFT453.v
   pins it as N22 ([p453_n22_hw_large], beside the control
   [p453_hw_at_objects] at [o <= so]) and peels it as N23
   ([p453_n23_hw_large_index]); its [p453_hw_is_library] reads
   [Complete_HasSubobjectWidePullbacks] at the index at the objects as
   that same term, by [eq_refl].  [so < o] is the regime of the adjoint
   functor theorems; at [o <= so], Structure/Complete/Freyd.v's
   [small_complete_is_thin] makes a category with decidable object
   equality and decidable hom-setoids thin, as
   Adjunction/SAFT/InitialObject.v's header measures for its own small
   route.  No other route to [HasSubobjectWidePullbacks] at the objects'
   universe was attempted (a [Prop]-valued intersection under
   [Untruncate], say).  What IS known: (i) every right adjoint satisfies
   [PreservesWidePullbacks] ([right_adjoint_PreservesWidePullbacks]), and
   Instance/Mod/Spanning.v's [Bilin_PreservesWidePullbacks] is a witness
   proved directly rather than through an adjunction; (ii)
   Adjunction/SAFT/Characterization/Examples.v's
   [subsets_inverse_image_thm2] applies [SAFT_thm2] at the thin [Subsets
   Y] with [U := InverseImage f], every premise inhabited --
   Instance/Powerset/WellPowered.v's [Subsets_Complete_free Y],
   [Complete_HasSubobjectWidePullbacks] of it (objects at or below its
   shape universe), Adjunction/SAFT/InitialObject/Examples.v's
   [Subsets_Cogenerator_empty Y], and both preservation premises read off
   Instance/Powerset.v's [image_preimage_adjunction f] itself.  That is
   CIRCULAR, as Adjunction/GAFT/Sets.v's [Sets_Id_PreservesImageLimit]
   is: the premises come from the adjunction whose left adjoint the
   theorem then builds, so the witness shows them satisfiable together
   and constructs no adjoint that was not known.  (iii) At [Sets] no
   [HasSubobjectWidePullbacks] at the objects' universe was built.  At
   [Sets@{o so}] ([Set < o < so], objects at [so], homs and
   [Sets_Complete]'s shapes at [o]), [Complete_HasSubobjectWidePullbacks
   Sets_Complete] is accepted as [HasSubobjectWidePullbacks@{so o o o
   k}], the index at the homs, in a scratch file carrying this file's
   import list and Instance/Sets/Complete.v; in the same file the term
   above at [Sets_Complete] is refused as [HasSubobjectWidePullbacks@{so
   o so so k}], the index at the objects: "(universe inconsistency:
   Cannot enforce o = <1> because o < so <= <2> <= <1>)" (<1>, <2> the
   scratch file's generated universes).  Test/ProbeSAFT453.v pins the
   pair: the refusal as N24 ([p453_n24_sets_hw_large]), the acceptance as
   [p453_sets_hw_library] (the constant) and [p453_sets_hw_small] (its
   body).  Instance/Sets/SubobjectLattice.v's [Sets_HasWidePullbacks]
   indexes its families at the hom universe too
   (Adjunction/SpanningArrow.v's NOT DELIVERED (3) measures that for its
   [FactoringFamily], a family of the same shape as [least_index]).

   RIEHL 4.7.10, A FIDELITY FLAG AND A STATED DEVIATION.  The catalogue's
   summary, paraphrased: a CONTINUOUS functor U : A -> S between locally
   small categories, out of a COMPLETE A with a small coseparating set in
   which every collection of subobjects of a fixed object has an
   INTERSECTION, has a left adjoint; the proof says that intersections of
   subobjects are "created" in s ↓ U.  Creating an intersection of a
   large collection in s ↓ U needs U to preserve it, and continuity,
   preservation of small limits, does not reach it here:
   [PreservesImageLimit] quantifies over shapes at [so] (the binder
   [PreservesImageLimit@{o h dobj h pk so pa so}]), while the
   corresponding family [least_index] has its sort at [lq] with [o <= lq]
   ([About least_index]), so at [so < o] no shape continuity speaks of is
   indexed by it (read off the two [About]s, not measured as a refusal).
   Riehl's statement is approached here from two sides, each with a
   hypothesis her catalogue summary does not list: the Corollary adds
   well-poweredness and asks no intersections, and Theorem 2 adds
   [PreservesWidePullbacks]; neither is her statement.  So the Riehl
   4.7.10 checkbox of #453, "the in-tree statement's hypothesis list
   matches the book's", is NOT met as worded, and neither is the
   Epilogue's clause (iii) ([riehl:E.1:thm-gaft]), whose summary glosses
   the intersection as "a wide pullback": both are stated deviations of
   #453.  Whether Riehl's "collection" is meant small, or her proof
   supplies the preservation some other way, stays open until the printed
   page is read.

   THE COVERING DATUM.  Adjunction/SAFT.v's [SAFT] takes a covering datum
   [SubobjectCover], which Adjunction/SAFT/Sets.v's
   [SubobjectCover_Id_Sets_absurd] refutes at [Id[Sets]].
   [SAFT_wellpowered]'s premises are the book's list (complete, small
   homs through the shared [h], a small cogenerating family,
   well-powered, continuous), and it applies at that very [Id[Sets]]:
   Adjunction/SAFT/Characterization/Examples.v's [sets_id_saft Un] is
   [SAFT_wellpowered (@Id Sets@{o so}) Sets_Complete
   Sets_Id_PreservesImageLimit (Sets_Cogenerator_untruncate Un)
   (Sets_WellPowered_untruncate Un)] at [Set < o < so] for [Un :
   Untruncate@{o}], closed under the global context, and its
   [sets_id_old_cover_refuted Un] applies [SubobjectCover_Id_Sets_absurd]
   to the same three witnesses (the well-powering through
   Adjunction/SAFT/WellPowered.v's [WellPowered_SubobjectIndex]).  So
   Awodey's checkbox "[SubobjectCover] becomes a theorem" cannot be met
   as worded -- the datum is refuted at [Id[Sets]], where under
   [Untruncate] the book's hypotheses hold -- and is met by supersession:
   [SAFT], [SubobjectCover] and their satellites stay, unchanged.  The
   covering datum over the [d]-dependent product, which IS a theorem, is
   the satellite Adjunction/SAFT/Characterization/Cover.v's.

   ** Strengths, measured

   [eq_refl]:
     - [SAFT_left_obj]: [fobj[`1 (SAFT_wellpowered U comp cont G WP)] d]
       IS [snd (`1 (Subobject.sub_dom (complete_intersection
       (Comma_Complete cont comp) (wp_class_family (comma_WellPoweredAt …)
       (fun _ => True)))))], the C-object under the intersection of all
       subobjects of the comma's cogenerator product -- Mac Lane's
       initial object of the comma, read in C;
     - [SAFT_thm2_left_obj]: [fobj[`1 (SAFT_thm2 U comp cont G HW HU)] d]
       IS [WPull (HW _ (least_index U d X) (fun k => `1 k))], [X] the
       comma's cogenerator product: the C-wide pullback of the
       corresponding family.
   Through [GAFT_from_initials] neither holds: in a scratch file carrying
   this file's import list and Adjunction/GAFT.v (under the import list
   alone [GAFT_from_initials] is not in scope), [GAFT_from_initials U
   (SAFT_comma_initial U comp cont G WP)] and [GAFT_from_initials U
   (SAFT_thm2_initial U comp cont G HW HU)] are accepted, and the same
   [eq_refl] against each is refused by conversion, "(cannot unify
   "fobj[projT1 (…)] d" and "snd (projT1 (Subobject.sub_dom
   (complete_intersection …" and "(cannot unify "fobj[projT1 (…)] d" and
   "WPull (HW …" respectively, beside the two readbacks above restated
   there as controls.  Test/ProbeSAFT453.v pins both refusals, as N4 and
   N5 ([p453_n4_gaft_route_obj], [p453_n5_thm2_gaft_route_obj]), beside
   the formed routes [p453_gaft_route] and [p453_thm2_gaft_route] and the
   transparent controls [p453_left_obj] and [p453_thm2_left_obj].  So the
   decision to make Theorem 2 transparent too is measured, not assumed.
   Everything else is [≈].  Forty-seven constants ([Print Module]), no
   [Program] obligation: forty-two transparent and five [Qed], two
   [Monic] proofs ([comma_monic_of_underlying],
   [underlying_monic_of_comma_monic]) and three [≈] between arrows
   ([kp_diag_fst], [kp_diag_snd], [least_lift_commutes]); the readbacks
   compile with the five opaque.

   ** Universes, measured

   With [Set Printing Universes. About …], stdlib bounds and the comma
   category's unnamed internal universes omitted ([oc] below is the
   comma's object universe, printed unnamed):

     comma_monic_iff_underlying_monic@{o hc dobj h …} :
       {C : Category@{o hc hc}} {D : Category@{dobj h h}} … →
       HasPullbacks@{o hc} C → Monic@{oc h} m ↔ Monic@{o hc} (snd `1 m)
       (* hc <= h *)
     comma_cogenerator@{o hc dobj h c cc …} :
       Cogenerator@{c o hc} C → Cogenerator@{cc oc h} (=(d) ↓ U)
       (* hc <= h, c <= cc, h <= cc *)
     comma_WellPoweredAt@{o hc dobj h w s t … wc sc tc …} :
       WellPoweredAt@{w o s hc t} (snd `1 X) → WellPoweredAt@{wc oc sc h tc} X
       (* hc < t, h < tc, o <= s, hc <= s, hc <= h, w <= wc, h <= wc,
          oc <= sc, h <= sc *)
     comma_WellPowered@{o hc dobj h w s t sc tc …} :
       WellPowered@{o hc w s t} C → WellPowered@{oc h h sc tc} (=(d) ↓ U)
     SAFT_wellpowered@{o dobj h so c w s t pk pa …} :
       Complete@{so so h o} → PreservesImageLimit@{o h dobj h pk so pa so}
       → Cogenerator@{c o h} C → WellPowered@{o h w s t} C →
       ∃ F, Adjunction@{o h h dobj h h h h pa h …} F U
       (* h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < pk,
          h < pa, so < pk, o <= pk, dobj <= pk *)
     HasSubobjectWidePullbacks@{o h q r k} : Category@{o h h} → Type@{k}
       (* q < k, q <= r, h <= r, o <= k, h <= k, r <= k *)
     Complete_HasSubobjectWidePullbacks@{o h so q r k …} :
       Complete@{so so h o} → HasSubobjectWidePullbacks@{o h q r k} C
       (* h <= so, q <= so, q <= r, h <= r, q < k, r <= k, o <= k *)
     SAFT_thm2@{o dobj h so c pk pa q r rd pw k …} :
       … → HasSubobjectWidePullbacks@{o h q r k} C →
       PreservesWidePullbacks@{o h dobj h pw q r rd} U → ∃ F, F ⊣ U
       (* h <= so, c <= so, o <= q, h <= q, q <= r, q <= rd, q < pw, … *)
     right_adjoint_PreservesWidePullbacks@{o dobj h pw q r rd …} :
       F ⊣ U → PreservesWidePullbacks@{o h dobj h pw q r rd} U
       (* q < pw, q <= r, q <= rd, h <= r, h <= rd, r <= pw, rd <= pw *)

   [SAFT_wellpowered_iff] and [SAFT_iff] carry the blocks of
   [SAFT_wellpowered] and [SAFT_thm2].  No constant here carries an
   equation between two universes it names (the About of all forty-seven,
   searched for " = ", finds none).

   - [h < so] holds.  In a scratch file carrying this file's import list,
     [SAFT_wellpowered] and [SAFT_wellpowered_iff] are accepted at [h <
     so, so < o, c < so, w < h], [SAFT_thm2] and [SAFT_iff] at [h < so,
     so < o, c < so, o < q, h < q], and [SAFT_wellpowered] at
     Adjunction/SAFT.v's own regime ([Complete@{h h h o}],
     [Cogenerator@{h o h}]); all closed.  The instrument, the same
     application of [SAFT_wellpowered] at [so < h], is refused there:
     "Universe inconsistency. Cannot enforce h <= so because so < h".
     Test/ProbeSAFT453.v pins the acceptances ([p453_small],
     [p453_small_iff], [p453_thm2_small], [p453_thm2_small_iff]; the
     Corollary at Adjunction/SAFT.v's regime inside [p453_cover_iso]) and
     the instrument as N8 ([p453_n8_shapes_below_homs]), which that
     command's binder alone refuses (the probe's paragraph KINDS).
     Nothing relates [o] to [so].  The [so = h] that one unannotated
     comma instantiation printed for #452
     (Adjunction/SAFT/InitialObject.v's "What #453 needs from here") was
     minimization.
   - C's homs may sit below D's ([hc <= h]) in the monos lemma and the
     comma constructions; the theorems share [h], as
     [PreservesImageLimit]'s own identification of the two hom universes
     requires.
   - The cogenerator's index [c] is free below [so].  #452's donor
     collapse (the index of the family handed to [cogen_prod] equals
     [so]) is absorbed by [comma_cogenerator], whose index [cc] is free
     above [c] and [h] and is set to [so] where the comma's
     [cogen_prod] is taken.
   - Theorem 2's class index [q] is bounded by [o <= q, h <= q], where
     [least_index] lives (Test/ProbeSAFT453.v's N9 refuses [q < o] at
     [SAFT_thm2]'s binder, and its N26 at the body, the paragraph IN TREE
     above).  [HW]'s and [HU]'s C-side wide-pullback universe [r] is one
     universe in this term: [wide_pullback_is_pullback] hands [HW]'s cone
     to [HU] at one universe ([About]: from [WidePullback@{u u0 u1 u2}]
     to [IsWidePullback@{u u0 u1 u2}]), and in a scratch file carrying
     this file's import list, the body of [SAFT_thm2_initial] restated
     with [HU]'s slot named [r2] apart from [HW]'s [r] reads back "r =
     r2".  Test/ProbeSAFT453.v pins that as a refusal at [r < r2], N27
     ([p453_n27_initial_r_apart], at [wide_pullback_is_pullback]), beside
     the readback's control [p453_thm2_initial_r_le]; its N10 records the
     same identification in [SAFT_thm2]'s own binder, which gives [HW]
     and [HU] one [r].  Rebuilding the [IsWidePullback] record at a
     second universe from [HW]'s fields was not tried.
   - The conclusion's [Adjunction] carries [pa] in its strict slot, as
     Adjunction/SAFT.v's [SAFT] readback carries its
     [PreservesImageLimit] slot.  The donor is Construction/Comma/
     Limit.v's [Comma_Complete]: [About Comma_Complete] under [Set
     Printing Implicit] shows its comma at [Comma@{… u5 u5 u5}] and the
     comma's [Diagonal] at [Diagonal@{… u5 …}], [u5] being the auxiliary
     slot of its [PreservesImageLimit@{u u0 u1 u2 u4 u3 u5 u6}], and
     [AdjunctionFromUniversalArrows] passes the comma's universe on to
     the adjunction.
   - Four collapses were found and removed, each measured by [About]:
     (a) a top-level [comma_WellPoweredAt] identified the comma's
     internal universe strictly above C's homs with [WellPowered]'s [t],
     and [Comma_Complete] identifies the same comma universe with [pa]
     (the previous item), so [SAFT_wellpowered] read "t = pa"; stated in
     the section [CommaWellPowered], where the comma's universes are
     fixed when [X] is declared, the equation is gone.  Naming
     [PreservesImageLimit]'s slots alone does not remove it: with [pa]
     named and [comma_WellPoweredAt] top-level, the readback was that
     equation between two named universes.
     (b) Assembling the Σ-type by the tactic [exists] brought "t = pa"
     back, where the term [existT _ (SAFT_left …) (SAFT_adjunction …)]
     does not, so [SAFT_wellpowered] and [SAFT_thm2] are terms.  (c)
     [least_index] at an unnamed sort made [SAFT_thm2] read "q = r" and
     "q = rd"; its sort [lq] and the wide-pullback universes [r] and
     [rd] of the [least_*] binders are named.  (d) A top-level
     [comma_WellPowered] read "oc = sc", from [comma_wp_to_from]'s
     setoid universe collapsing onto the comma's objects, and put the
     comma's [Diagonal] universe at [tc]; [comma_wp_to_from] names its
     setoid universes, and [comma_WellPowered] is stated over a [Let] of
     the comma in the section [CommaWellPoweredAll].
   - [underlying_sub] is top-level, with its own binder [@{o hc dobj h +|
     hc <= h +}].  Declared inside [CommaWellPowered] it did not use [W]
     but inherited the section's [w s t] and their constraints ([hc < t],
     [o <= s], [hc <= s], [About]); top-level, [About underlying_sub]
     names [o hc dobj h] and no universe of [W].
   - Stdlib bounds are inherited: [h < eq_rect_r.u0] and the [VectorDef]
     bounds appear ([About]) on Structure/Limit/Finite.v's
     [FinitelyComplete_HasPullbacks], reached through #452's
     [complete_pullbacks], and [so <= Fin.case0.u0] on #452's
     [special_initial_object_wellpowered_at];
     [Complete_HasSubobjectWidePullbacks] carries the [Fin.case0] and
     [VectorDef] bounds of Structure/Pullback/Wide/Complete.v's
     [complete_wide_pullback] ([About]: on its [Complete]'s first
     universe).

   ** Non-vacuity

   The Corollary applies at [Id[Sets]] under one [Untruncate] (the
   covering-datum paragraph), and its landed witnesses -- that one, the
   hom-functors of [Sets], and the thin [Subsets Y] and [Indiscrete] --
   are the satellite Adjunction/SAFT/Characterization/Examples.v's.
   Theorem 2 applies at the thin [Subsets Y] only, circularly (clause
   (ii) of the paragraph IN TREE, THEOREM 2 IS APPLIED ONLY AT A THIN
   CATEGORY, [subsets_inverse_image_thm2]).  The monos lemma and the
   comma constructions are consumed by both theorems at each [d].

   ** Not delivered

   No [HasSubobjectWidePullbacks] at an index at or above the objects,
   the one Theorem 2 asks, at a category that is not thin, so Theorem 2
   is not applied at one; [SAFT_iff] is a conditional there.

   NO ROUTE FROM WELL-POWEREDNESS TO THEOREM 2's HYPOTHESES.  No constant
   derives [HasSubobjectWidePullbacks] from [WellPowered] and [Complete]
   (a whole-word grep for the name over the .v files outside Test/ finds
   this file only), nor [PreservesWidePullbacks] from continuity over a
   well-powered [C].  That is Mac Lane's route from Theorem 2 to the
   Corollary (the catalogue's [def1]: "if A is well-powered and
   small-complete, then every set of subobjects of an object has an
   intersection, formed by the usual pullback, so the extra hypothesis of
   Theorems 1 and 2 is automatic"), and the first clause of #453's Work
   item 3; here the Corollary is proved directly, by
   [comma_WellPoweredAt], and [SAFT_wellpowered] is not derived from
   [SAFT_thm2].  This is a stated deviation of #453.  What a derivation
   would need: a wide pullback of a family indexed at [q], [o <= q], from
   limits of shapes at [so < o].  Well-poweredness reindexes the family's
   members onto the small [wp_index], as Structure/WellPowered.v's
   [wellpowered_complete_has_intersections] does for a class given by a
   predicate, but the indices that the family hits form a small type only
   as a [Prop]-truncated image (a Σ over the family's index is at [q]
   again).  A cone over the family then gives, at a hit index, an arrow
   into that member only once a member of the family hitting it is
   chosen, an elimination of that truncation into [Type] (unique choice
   for an arrow through a mono); or images, to factor the cone's common
   arrow into [x] before comparing it with the greatest lower bound; or a
   resizing along [wp_to_from].  None of the three is attempted here, and
   whether the tree supplies one is not measured; nothing here says the
   derivation is impossible.

   Mac Lane's own route for the monos lemma, through the comma projection
   creating kernel pairs, is not written.  Only the left adjoint's value
   on objects is read back; its action on arrows and the unit are not
   measured at [eq_refl].  [SubobjectCover] is not derived (it is
   refuted), and [SAFT_wellpowered] is not compared with
   Adjunction/SAFT.v's [SAFT].  One direction separates them in tree: at
   [Id[Sets]] under [Untruncate] [SAFT_wellpowered]'s premises hold and
   [SAFT]'s covering datum is refuted (the covering-datum paragraph).
   The other direction, a category where [SAFT]'s premises hold and
   [WellPowered] does not, is not exhibited; [SubobjectIndex] alone lacks
   well-poweredness's exhaustiveness clause
   ([SubobjectIndex_not_exhaustive]), which does not settle it for
   [SubobjectIndex] and [cover] together.  The Riehl question above is
   open.  The scratch measurements quoted name their environments.
   Test/ProbeSAFT453.v pins, where each is cited above, the refusals
   quoted here and the body-level refusals behind two of its readbacks
   (N4, N5, N8, N22-N24, N26, N27); it does not pin the "Illegal
   application" refusal with Instance/Sets.v's [Require] dropped (a
   shorter import list than a probe may carry) nor the [About] readbacks
   of the Universes section, and of the collapses there it pins (a)-(c)
   as staying removed and not (d).  The file compiles with Coq 8.19.2 and
   8.20.1 against copies of prebuilt trees of its closure, the files that
   differ from this tree's compiled afresh, and all forty-seven constants
   report closed there too.

   MEASUREMENTS.  Forty-seven constants ([Print Module]), no [Program]
   obligation; each reports "Closed under the global context" by its
   fully qualified name.  Closure 112 files excluding itself, counted
   over .Makefile.coq.d (Adjunction/SAFT/InitialObject.v's is 110). *)

(** ** The monos lemma *)

(* The easy half: an arrow of the comma whose C-component is monic is
   monic.  No hypothesis. *)
Lemma comma_monic_of_underlying@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  Monic (snd (`1 m)) → Monic m.
Proof.
  intros Hm; constructor; intros Z g1 g2 H.
  split.
  - destruct (fst (`1 g1)), (fst (`1 g2)); exact eq_refl.
  - apply (monic (Monic := Hm)).
    exact (snd H).
Qed.

(* The hard half, from ONE kernel pair [K] of the underlying arrow in C
   and nothing about [U]: the kernel-pair object takes the comma
   structure [fmap[U] (kp_diag m K) ∘ `2 X] through its diagonal, and
   the two projections become comma arrows into [X] equalized by [m]. *)
Definition kp_diag@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  snd (`1 X) ~{C}~> Pull _ _ K :=
  unique_obj (ump_pullbacks _ _ K (snd (`1 X)) id id (reflexivity _)).

Lemma kp_diag_fst@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  pullback_fst _ _ K ∘ kp_diag m K ≈ id.
Proof.
  exact (fst (unique_property (ump_pullbacks _ _ K _ id id (reflexivity _)))).
Qed.

Lemma kp_diag_snd@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  pullback_snd _ _ K ∘ kp_diag m K ≈ id.
Proof.
  exact (snd (unique_property (ump_pullbacks _ _ K _ id id (reflexivity _)))).
Qed.

Definition kp_obj@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) : =(d) ↓ U :=
  ((ttt, Pull _ _ K); fmap[U] (kp_diag m K) ∘ `2 X).

Definition kp_fst@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  kp_obj m K ~{=(d) ↓ U}~> X.
Proof.
  unshelve refine ((ttt, pullback_fst _ _ K); _).
  change (`2 X ∘ id[d]
            ≈ fmap[U] (pullback_fst _ _ K) ∘ (fmap[U] (kp_diag m K) ∘ `2 X)).
  rewrite id_right, comp_assoc, <- fmap_comp, kp_diag_fst, fmap_id, id_left.
  reflexivity.
Defined.

Definition kp_snd@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  kp_obj m K ~{=(d) ↓ U}~> X.
Proof.
  unshelve refine ((ttt, pullback_snd _ _ K); _).
  change (`2 X ∘ id[d]
            ≈ fmap[U] (pullback_snd _ _ K) ∘ (fmap[U] (kp_diag m K) ∘ `2 X)).
  rewrite id_right, comp_assoc, <- fmap_comp, kp_diag_snd, fmap_id, id_left.
  reflexivity.
Defined.

Lemma underlying_monic_of_comma_monic@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y)
  (K : Pullback (snd (`1 m)) (snd (`1 m))) :
  Monic m → Monic (snd (`1 m)).
Proof.
  intros Hm; constructor; intros z g1 g2 H.
  assert (Hp : kp_fst m K ≈ kp_snd m K).
  { apply (monic (Monic := Hm)).
    split.
    - destruct (fst (`1 m)); exact eq_refl.
    - exact (pullback_commutes _ _ K). }
  destruct (ump_pullbacks _ _ K z g1 g2 H) as [u [Hu1 Hu2] _].
  rewrite <- Hu1, <- Hu2.
  simpl in Hp.
  now rewrite (snd Hp).
Qed.

Definition comma_monic_iff_underlying_monic@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  Monic m ↔ Monic (snd (`1 m)) :=
  (underlying_monic_of_comma_monic m (pullback _ _),
   comma_monic_of_underlying m).

(** ** The cogenerating family of the comma category *)

(* Mac Lane's Q': the objects [(cog_obj G j, k)], one for each arrow
   [k : d ~> U (cog_obj G j)].  The index universe [cc] is free above the
   old index and the homs. *)
Definition comma_cogenerator@{o hc dobj h c cc +| hc <= h, c <= cc, h <= cc +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (G : Cogenerator@{c o hc} C) : Cogenerator@{cc _ h} (=(d) ↓ U).
Proof.
  refine (@Build_Cogenerator (=(d) ↓ U)
            { j : cog_index G & d ~> U (cog_obj G j) }
            (fun p => ((ttt, cog_obj G (projT1 p)); projT2 p)) _).
  intros x y f g H.
  split.
  - destruct (fst `1 f), (fst `1 g); exact eq_refl.
  - apply (cog_separates G (snd `1 f) (snd `1 g)); intros j k.
    unshelve refine (snd (H (j; fmap[U] k ∘ `2 y) ((ttt, k); _))).
    simpl; cat.
Defined.

(** ** Well-poweredness of the comma category *)

(* A comma subobject read in C, through the monos lemma.  Top-level, so
   that it carries only the universes its type names: declared in the
   section below it inherited the well-powering's [w s t] and their
   constraints without naming [W]. *)
Definition underlying_sub@{o hc dobj h +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X : =(d) ↓ U} (v : SubObj X) :
  SubObj (snd (`1 X)) :=
  @Build_SubObj C (snd (`1 X)) (snd (`1 (Subobject.sub_dom v)))
    (snd (`1 (Subobject.sub_mono v)))
    (underlying_monic_of_comma_monic (Subobject.sub_mono v) (pullback _ _)
       (Subobject.sub_is_monic v)).

(* A section rather than top-level binders, and the reason is measured
   (the header's universes section, collapse (a)): declared here, the
   comma category's universes are fixed when [X] is declared, and none of
   them is identified with [W]'s [t]. *)
Section CommaWellPowered.

Universes o hc dobj h w s t.
Constraint hc <= h.

Context {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D).
Context (HP : HasPullbacks C) (X : =(d) ↓ U).
Context (W : WellPoweredAt@{w o s hc t} (snd (`1 X))).

(* A subobject of [X] in the comma: a C-subobject of the underlying
   object, named by [W], with a factorization of [X]'s structure arrow
   through [U] of its mono. *)
Definition comma_wp_index : Type :=
  { i : wp_index W &
    { s : d ~> U (Subobject.sub_dom (wp_to W i)) &
      fmap[U] (Subobject.sub_mono (wp_to W i)) ∘ s ≈ `2 X } }.

Definition comma_wp_dom (k : comma_wp_index) : =(d) ↓ U :=
  ((ttt, Subobject.sub_dom (wp_to W (`1 k))); `1 (`2 k)).

Definition comma_wp_mono (k : comma_wp_index) : comma_wp_dom k ~{=(d) ↓ U}~> X.
Proof.
  unshelve refine ((ttt, Subobject.sub_mono (wp_to W (`1 k))); _).
  change (`2 X ∘ id[d] ≈ fmap[U] (Subobject.sub_mono (wp_to W (`1 k)))
                            ∘ `1 (`2 k)).
  rewrite id_right; symmetry; exact (`2 (`2 k)).
Defined.

Definition comma_wp_to (k : comma_wp_index) : SubObj X :=
  @Build_SubObj (=(d) ↓ U) X (comma_wp_dom k) (comma_wp_mono k)
    (comma_monic_of_underlying (comma_wp_mono k)
       (Subobject.sub_is_monic (wp_to W (`1 k)))).

Definition comma_wp_from (v : SubObj X) : comma_wp_index.
Proof using HP.
  pose (e := wp_to_from W (underlying_sub HP v)).
  exists (wp_from W (underlying_sub HP v)).
  exists (fmap[U] (from (`1 e)) ∘ `2 (Subobject.sub_dom v)).
  rewrite comp_assoc, <- fmap_comp.
  assert (Hm : Subobject.sub_mono (wp_to W (wp_from W (underlying_sub HP v)))
                 ∘ from (`1 e) ≈ snd (`1 (Subobject.sub_mono v))).
  { rewrite <- (`2 e). simpl. rewrite <- comp_assoc, iso_to_from. cat. }
  rewrite Hm.
  symmetry.
  exact (comma_square (Subobject.sub_mono v)).
Defined.

Definition comma_wp_iso_to (v : SubObj X) :
  comma_wp_dom (comma_wp_from v) ~{=(d) ↓ U}~> Subobject.sub_dom v.
Proof using HP.
  unshelve refine ((ttt, to (`1 (wp_to_from W (underlying_sub HP v)))); _).
  simpl.
  rewrite id_right, comp_assoc, <- fmap_comp, iso_to_from, fmap_id.
  now rewrite id_left.
Defined.

Definition comma_wp_iso_from (v : SubObj X) :
  Subobject.sub_dom v ~{=(d) ↓ U}~> comma_wp_dom (comma_wp_from v).
Proof using HP.
  unshelve refine ((ttt, from (`1 (wp_to_from W (underlying_sub HP v)))); _).
  simpl. now rewrite id_right.
Defined.

Definition comma_wp_to_from@{sc tc +| h <= sc, h < tc +} (v : SubObj X) :
  @equiv _ (@SubObj_Setoid@{_ h h sc tc} (=(d) ↓ U) X)
    (comma_wp_to (comma_wp_from v)) v.
Proof using HP.
  unshelve eexists.
  - unshelve refine (@Build_Isomorphism (=(d) ↓ U) _ _
                       (comma_wp_iso_to v) (comma_wp_iso_from v) _ _).
    + split; [reflexivity|]. simpl.
      exact (iso_to_from (`1 (wp_to_from W (underlying_sub HP v)))).
    + split; [reflexivity|]. simpl.
      exact (iso_from_to (`1 (wp_to_from W (underlying_sub HP v)))).
  - split; [reflexivity|]. simpl.
    exact (`2 (wp_to_from W (underlying_sub HP v))).
Defined.

Definition comma_WellPoweredAt@{wc sc tc +| w <= wc, h <= wc, h <= sc, h < tc +} :
  @WellPoweredAt@{wc _ sc h tc} (=(d) ↓ U) X :=
  {| wp_index := comma_wp_index;
     wp_to := comma_wp_to;
     wp_from := comma_wp_from;
     wp_to_from := comma_wp_to_from |}.

End CommaWellPowered.

(* At every object.  The comma is a [Let] of the section, so that its
   universes are fixed before the result type names [sc] and [tc]
   (collapse (d) of the header). *)
Section CommaWellPoweredAll.

Universes o hc dobj h w s t sc tc.
Constraint hc <= h, h <= sc, h < tc.

Context {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D).
Context (HP : HasPullbacks C) (WP : WellPowered@{o hc w s t} C).

Let K : Category := =(d) ↓ U.

Definition comma_WellPowered : @WellPowered@{_ h h sc tc} K :=
  fun X => comma_WellPoweredAt U d HP X (WP (snd (`1 X))).

End CommaWellPoweredAll.

(** ** The Corollary: the well-powered form *)

(* #452's special initial-object theorem in the comma [=(d) ↓ U]: its
   completeness from [Comma_Complete], its cogenerating family from
   [comma_cogenerator], its well-poweredness at the one object that
   matters from [comma_WellPoweredAt]. *)
Definition SAFT_comma_initial@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  @Initial (=(d) ↓ U) :=
  special_initial_object_wellpowered_at (Comma_Complete cont comp)
    (comma_cogenerator U d G)
    (comma_WellPoweredAt U d (complete_pullbacks comp) _ (WP _)).

Definition SAFT_universal_arrow@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) (d : D) :
  UniversalArrow d U :=
  {| arrow_initial := SAFT_comma_initial U comp cont G WP d |}.

(* The left adjoint, transparent: Theory/Universal/Arrow.v's assembly,
   not Adjunction/GAFT.v's [Qed] [GAFT_from_initials]. *)
Definition SAFT_left@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) : D ⟶ C :=
  @LeftAdjointFunctorFromUniversalArrows D C U
    (SAFT_universal_arrow U comp cont G WP).

Definition SAFT_adjunction@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  SAFT_left U comp cont G WP ⊣ U :=
  @AdjunctionFromUniversalArrows D C U (SAFT_universal_arrow U comp cont G WP).

(* The pair is a term, not an [exists]: the tactic form re-introduces
   the equation "t = pa" (collapse (b) of the header). *)
Definition SAFT_wellpowered@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  existT _ (SAFT_left U comp cont G WP) (SAFT_adjunction U comp cont G WP).

(* READBACK, [eq_refl]: the left adjoint at [d] is the C-object under the
   intersection of all subobjects of the comma's cogenerator product. *)
Example SAFT_left_obj@{o dobj h so c w s t pk pa +|
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

(* Mac Lane's Corollary, Awodey's Remark 9.35: over a complete,
   well-powered C with a small cogenerating family, [U] has a left
   adjoint iff it is continuous. *)
Definition SAFT_wellpowered_iff@{o dobj h so c w s t pk pa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ @PreservesImageLimit@{o h dobj h pk so pa so} C D U :=
  (fun H => right_adjoint_PreservesImageLimit (`2 H),
   fun cont => SAFT_wellpowered U comp cont G WP).

(** ** Theorem 2: every set of subobjects has a pullback *)

(* Mac Lane's "every set of subobjects of an object has a pullback": a
   LIMIT, over an index at the universe [q] (the class reading). *)
Definition HasSubobjectWidePullbacks@{o h q r k +}
  (C : Category@{o h h}) : Type@{k} :=
  ∀ (x : C) (I : Type@{q}) (S : I → SubObj x),
    WidePullback@{q r o h} (fun i => Subobject.sub_mono (S i)).

(* Completeness supplies it at every index universe [q] at or below its
   shape universe [so], whatever the objects' universe: Structure/
   Pullback/Wide/Complete.v's [complete_wide_pullback] at each family.
   Theorem 2 asks it at [q] at or above the objects (the header's
   paragraph IN TREE, THEOREM 2 IS APPLIED ONLY AT A THIN CATEGORY). *)
Definition Complete_HasSubobjectWidePullbacks@{o h so q r k +|
    h <= so, q <= so +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C) :
  HasSubobjectWidePullbacks@{o h q r k} C :=
  fun x I S => complete_wide_pullback comp (fun i => Subobject.sub_mono (S i)).

(* The least subobject of a comma object [X], from a C-wide pullback of
   Mac Lane's corresponding family that [U] carries to a wide pullback.
   [least_index] is that family: the C-subobjects of [X]'s underlying
   object through which [X]'s structure arrow factors. *)
Definition least_index@{o hc dobj h lq +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (X : =(d) ↓ U) : Type@{lq} :=
  { m : SubObj (snd (`1 X)) & SubFactorsThrough U (`2 X) m }.

Definition least_top@{o hc dobj h lq +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (X : =(d) ↓ U) : least_index U d X :=
  (sub_top; factors_through_top U (`2 X)).

(* The D-arrow into [U] of the intersection: the mediator of the
   factorizations, which [HU]'s wide pullback supplies.  Only this
   existence half of its universal property is used. *)
Definition least_lift@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k))) :
  d ~> U (WPull W).
Proof.
  refine (unique_obj (wpull_ump HUW (fun k => `1 (`2 k)) _)).
  intros i j. rewrite (`2 (`2 i)), (`2 (`2 j)). reflexivity.
Defined.

Lemma least_lift_commutes@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k)))
  (k : least_index U d X) :
  fmap[U] (wide_pullback_proj W k) ∘ least_lift HUW ≈ `1 (`2 k).
Proof. exact (unique_property (wpull_ump HUW _ _) k). Qed.

Definition least_dom@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k))) : =(d) ↓ U :=
  ((ttt, WPull W); least_lift HUW).

Definition least_mono@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k))) :
  least_dom HUW ~{=(d) ↓ U}~> X.
Proof.
  unshelve refine ((ttt, Subobject.sub_mono
                           (sub_wide_intersection (fun k => `1 k)
                              (least_top U d X) W)); _).
  simpl. rewrite id_right, id_left.
  symmetry. exact (least_lift_commutes HUW (least_top U d X)).
Defined.

Definition least_sub@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k))) : SubObj X :=
  @Build_SubObj (=(d) ↓ U) X (least_dom HUW) (least_mono HUW)
    (comma_monic_of_underlying (least_mono HUW)
       (Subobject.sub_is_monic
          (sub_wide_intersection (fun k => `1 k) (least_top U d X) W))).

(* A comma subobject [v] read as a member of the corresponding family. *)
Definition least_index_of@{o hc dobj h lq +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X : =(d) ↓ U} (v : SubObj X) : least_index U d X.
Proof.
  exists (underlying_sub HP v).
  exists (`2 (Subobject.sub_dom v)).
  symmetry. exact (comma_square (Subobject.sub_mono v)).
Defined.

Definition least_le@{o hc dobj h lq r rd +| hc <= h +}
  {C : Category@{o hc hc}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (HP : HasPullbacks C) {X : =(d) ↓ U}
  {W : WidePullback@{lq r o hc}
         (fun k : least_index U d X => Subobject.sub_mono (`1 k))}
  (HUW : IsWidePullback@{lq rd dobj h}
           (fun k : least_index U d X => fmap[U] (Subobject.sub_mono (`1 k)))
           (U (WPull W))
           (fun k => fmap[U] (wide_pullback_proj W k)))
  (v : SubObj X) : sub_le (least_sub HUW) v.
Proof.
  unshelve eexists.
  - unshelve refine ((ttt, wide_pullback_proj W (least_index_of HP v)); _).
    simpl. rewrite id_right. symmetry.
    exact (least_lift_commutes HUW (least_index_of HP v)).
  - split; [reflexivity|]. simpl.
    rewrite id_left.
    exact (transitivity
             (wide_pullback_commutes W (least_index_of HP v) (least_top U d X))
             (id_left _)).
Defined.


(** ** Theorem 2, sufficiency *)

(* #452's theorem over a least subobject, in the comma, at the least
   subobject built above; assembled transparently as the Corollary is. *)
Definition SAFT_thm2_initial@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
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

Definition SAFT_thm2_universal_arrow@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) (d : D) :
  UniversalArrow d U :=
  {| arrow_initial := SAFT_thm2_initial U comp cont G HW HU d |}.

Definition SAFT_thm2_left@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) : D ⟶ C :=
  @LeftAdjointFunctorFromUniversalArrows D C U
    (SAFT_thm2_universal_arrow U comp cont G HW HU).

Definition SAFT_thm2_adjunction@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  SAFT_thm2_left U comp cont G HW HU ⊣ U :=
  @AdjunctionFromUniversalArrows D C U
    (SAFT_thm2_universal_arrow U comp cont G HW HU).

Definition SAFT_thm2@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pk so pa so} C D U)
  (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C)
  (HU : PreservesWidePullbacks@{o h dobj h pw q r rd} U) :
  { F : D ⟶ C & F ⊣ U } :=
  existT _ (SAFT_thm2_left U comp cont G HW HU)
    (SAFT_thm2_adjunction U comp cont G HW HU).

(* READBACK, [eq_refl]: the left adjoint at [d] is the C-wide pullback of
   the corresponding family of the comma's cogenerator product. *)
Example SAFT_thm2_left_obj@{o dobj h so c pk pa q r rd pw k +|
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

(** ** Theorem 2, necessity: right adjoints preserve wide pullbacks *)

(* Every wide pullback, of monos or not, at every index universe: the
   monicity clause [Hm] is accepted and ignored.  Elementary, by
   transposition along [adj], since a wide pullback has no shape
   category for [rapl_ump]. *)
Definition right_adjoint_PreservesWidePullbacks@{o dobj h pw q r rd +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) : PreservesWidePullbacks@{o h dobj h pw q r rd} U.
Proof.
  intros I B z g _ P p HP.
  constructor.
  - intros i j. rewrite <- !fmap_comp. now rewrite (wpull_commutes HP i j).
  - intros Q q Hq.
    pose (qb := fun i => from (@adj _ _ _ _ A Q (B i)) (q i)).
    assert (Hq' : ∀ i j, g i ∘ qb i ≈ g j ∘ qb j).
    { intros i j; unfold qb.
      rewrite <- (@from_adj_nat_r C D F U A _ _ _ (g i) (q i)).
      rewrite <- (@from_adj_nat_r C D F U A _ _ _ (g j) (q j)).
      apply from_adj_respects. exact (Hq i j). }
    destruct (wpull_ump HP qb Hq') as [u Hu Huu].
    unshelve refine {| unique_obj := to (@adj _ _ _ _ A Q P) u |}.
    + intro i.
      rewrite <- (@to_adj_nat_r C D F U A _ _ _ (p i) u).
      etransitivity; [apply to_adj_respects; exact (Hu i)|].
      apply from_adj_comp_law.
    + intros v Hv.
      etransitivity; [|apply (from_adj_comp_law v)].
      apply to_adj_respects.
      apply Huu; intro i; unfold qb.
      rewrite <- (@from_adj_nat_r C D F U A _ _ _ (p i) v).
      apply from_adj_respects. exact (Hv i).
Defined.

(** ** Theorem 2, the biconditional *)

(* Mac Lane §V.8 Theorem 2: over a complete C with a small cogenerating
   family in which every family of subobjects has a wide pullback, [U] has
   a left adjoint iff it preserves small limits and wide pullbacks of
   monos. *)
Definition SAFT_iff@{o dobj h so c pk pa q r rd pw k +|
    h <= so, c <= so, o <= q, h <= q +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{c o h} C)
  (HW : HasSubobjectWidePullbacks@{o h q r k} C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ (@PreservesImageLimit@{o h dobj h pk so pa so} C D U
       * PreservesWidePullbacks@{o h dobj h pw q r rd} U) :=
  (fun H => (right_adjoint_PreservesImageLimit (`2 H),
             right_adjoint_PreservesWidePullbacks (`2 H)),
   fun H => SAFT_thm2 U comp (fst H) G HW (snd H)).
