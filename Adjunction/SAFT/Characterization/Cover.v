Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Span.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.InitialObject.

Generalizable All Variables.

(** * The covering step of the special adjoint functor theorem, derived *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab:      https://ncatlab.org/nlab/show/well-powered+category

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   Theorem 2 and its Corollary, book pp. 129-130 (catalogue ids
   [maclane:V.8:thm2], [maclane:V.8:cor1]); Awodey, "Category Theory",
   Remark 9.35, printed p. 255 ([awodey:9.8:remark35]); Riehl, "Category
   Theory in Context", Theorem 4.7.10, printed p. 177
   ([riehl:4.7:thm10]).  The statements are read from the catalogue's
   summaries under doc/plan/books; the printed books were not consulted.
   The Corollary: a small-complete, well-powered category [C] with small
   hom-sets and a small cogenerating set, and a functor [U : C ⟶ D] into
   a category with small hom-sets; [U] has a left adjoint if and only if
   it is continuous.  Awodey's remark states the sufficiency half and
   refers the proof to Mac Lane.

   Mac Lane proves it in the comma categories d↓U, which is
   Adjunction/SAFT/Characterization.v's route.  This satellite is the
   other classical route, Freyd's: build a SOLUTION SET at every [d] and
   hand it to Adjunction/GAFT.v's [GAFT].  Its content is the covering
   step that Adjunction/SAFT.v assumes.

   ** The covering datum, reshaped

   Adjunction/SAFT.v's [SAFT] takes a covering datum [SubobjectCover]:
   every [h : d ~> U c] factors through a subobject of the ONE object
   [cogen_prod comp G], the product of the cogenerating family.  That
   product does not depend on [d], and Adjunction/SAFT/Sets.v's
   [SubobjectCover_Id_Sets_absurd] refutes the datum at the identity of
   [Sets].  The classical argument takes its product over the arrows OUT
   OF [d] (nLab: the cogenerating set of d↓R is "the set of all objects
   of the form d→Rc_α").  Here that product is [saft_prod U comp G d],
   the product of [cog_obj G j] over the index [saft_index U G d := { j &
   d ~> U (cog_obj G j) }], and the datum [SubobjectCoverAt U comp G d W]
   indexes subobjects of it by a well-powering [W] of that one object.
   [saft_cover_at] PROVES the datum from completeness, preservation and
   the cogenerating family, at every [W]; nothing about it is assumed,
   and [W] is only its indexing (CONSUMED, below).

   THE ARGUMENT, for [h : d ~> U c]:

     - [saft_point]: the canonical point [d ~> U (saft_prod …)], whose
       [(j, f)] component is [f], from [cont] at the discrete limit
       ([image_family_cone] builds the cone over the image of a discrete
       diagram);
     - [saft_kappa]: Mac Lane's k : q_0 → ∏_H q, now depending on [h]:
       [saft_prod … ~> cogen_power comp G c], whose component at [(j, k)]
       is the projection at [(j, U k ∘ h)];
     - [saft_square]: [U κ ∘ point ≈ U (cogen_canonical comp G c) ∘ h],
       by uniqueness in [cont] at [cogen_power_limit], both sides having
       image legs [U k ∘ h];
     - [saft_sub]: the pullback of #452's [cogen_canonical_sub] along
       [κ] (Theory/Subobject/Functor.v's [sub_reindex] over
       [complete_pullbacks]).  It is monic by [monic_pullback_stable] of
       Adjunction/SAFT.v's [cogenerator_canonical_monic], the one place
       [cog_separates] is consumed;
     - [saft_lift]: [cont] at that pullback, fed the cone [saft_pb_cone]
       of vertex [d], gives [d ~> U (Pull)], and [saft_lift_commutes]
       says its second leg returns [h];
     - [saft_cover_at]: [wp_from W] names the subobject, and the
       exhaustiveness clause [wp_to_from] supplies the isomorphism that
       moves the lift onto the named representative.

   CONSUMED: [Complete] (the two products and the pullback),
   [PreservesImageLimit] (three times: the point, the square's
   uniqueness, the lift) and [Cogenerator] (separation, through the
   monicity above).  [W] is only the indexing of the datum, read through
   [wp_from] and [wp_to_from]: Structure/WellPowered.v's [wp_trivial]
   supplies one at every object of every category, with index [SubObj x],
   so the cover follows from completeness, preservation and the
   cogenerating family alone.  In a scratch file carrying this file's
   import list, [saft_cover_at U comp cont G d (wp_trivial (saft_prod U
   comp G d))] is accepted over an arbitrary [C], closed under the global
   context, and reads back [SubobjectCoverAt@{o dobj h so dp u u dp u} …
   (wp_trivial@{o h u u dp} …)].  Test/ProbeSAFT453.v's positive control
   [p453_cover_trivial] pins the acceptance, with the datum at
   [wp_trivial]'s own named universes ([o <= w], [h <= w]) rather than
   the minimized ones read back here; its [p453_sets_cover_trivial] does
   the same at [Sets] without [Untruncate].  Well-poweredness becomes a
   condition at [GAFT]'s index pin ([SAFT_cover_wp_at]'s [w <= h]; the
   Universes section below).  [wp_trivial]'s index is at or above the
   objects ([About wp_trivial]: [o <= w]), so at [h < o] [GAFT] refuses
   the solution sets built from it, Test/ProbeSAFT453.v's N28
   ([p453_n28_gaft_trivial_large], beside [p453_gaft_trivial_small] at [o
   <= h]), and [SAFT_cover_wp_at] refuses it at its own [w <= h], N14
   ([p453_n14_cover_wp_trivial_large], beside
   [p453_cover_wp_trivial_small]).  What [WellPoweredAt] adds over
   Adjunction/SAFT.v's [SubobjectIndex] is the exhaustiveness clause: the
   empty [SubobjectIndex] has no [wp_from]
   ([SubobjectIndex_not_exhaustive]).

   NOT CONSUMED: no image factorization, no intersection and no monos
   lemma.  A case-insensitive grep of this file's code, with its comments
   stripped, for "factori", "intersection", "sub_le", "HasImages",
   "comma_monic", "StrongEpi" and "Regular" finds nothing (instrument:
   "cogen_canonical" is found on five lines of the same stripped text).
   Structure/Factorization.v, Structure/Regular/Factorization.v and
   Theory/Subobject/Lattice.v are in this file's closure, through
   Structure/WellPowered.v, so the claim is "not used", not "not
   imported".  The reshaped datum is derived with a pullback and its
   preservation and no factorization; the old datum is refuted, so the
   route of the Awodey checkbox of #453 (derive [SubobjectCover] through
   "an epi-mono factorization in a complete well-powered category") does
   not arise.

   ** The Awodey and Riehl checkboxes

   "SubobjectCover becomes a theorem" is met by SUPERSESSION in the
   reshaped form, not by deriving the old datum.  The old datum is
   refuted where, under [Untruncate], the book's hypotheses hold:
   Adjunction/SAFT/Characterization/Examples.v's
   [sets_id_cover_separation] states, at [Id[Sets@{o so}]] under one [Un
   : Untruncate], with Instance/Sets/Complete.v's [Sets_Complete],
   Instance/Sets/Cogenerator.v's [Sets_Cogenerator_untruncate Un] and
   Instance/Sets/WellPowered.v's [Sets_WellPowered_untruncate Un], both
   that this file's datum is inhabited at every [d] and that
   [SubobjectCover], fed [WellPowered_SubobjectIndex] of the SAME
   well-powering, implies [False].  So a statement "the book's hypotheses
   give [SubobjectCover]", at the separation's universes ([Set < o], [o <
   so], [o < t]), would with [sets_id_cover_separation] prove
   [Untruncate@{o} → False]; it can be stated in tree only if
   [Untruncate] is refutable there (a meta-argument, not a constant).
   Adjunction/SAFT.v's [SAFT] is not a corollary of [SAFT_cover_wp]: its
   [cover] is not derivable from [SAFT_cover_wp]'s premises (the
   separation), and [SubobjectIndex] alone does not give [WellPowered]
   ([SubobjectIndex_not_exhaustive]).  Only that direction is witnessed:
   no category where [SAFT]'s premises hold and [WellPowered] does not is
   exhibited.  The two are applications of [GAFT], neither derived from
   the other.  [SAFT] is kept, unchanged.

   Riehl's checkbox asks for the in-tree hypothesis list to match the
   book's.  [SAFT_cover_wp]'s list is [Complete], [PreservesImageLimit],
   [Cogenerator] and [WellPowered]: Mac Lane's Corollary and Awodey's
   remark.  Riehl's catalogue summary assumes intersections of every
   collection of subobjects instead of well-poweredness; with
   completeness, well-poweredness gives those (Structure/WellPowered.v's
   [wellpowered_complete_has_intersections]), so for Riehl this is the
   theorem under a stronger hypothesis, and her checkbox is not met as
   worded (a stated deviation of #453;
   Adjunction/SAFT/Characterization.v's paragraph RIEHL 4.7.10).  The
   form over Mac Lane's Theorem 2 hypotheses is
   Adjunction/SAFT/Characterization.v's.

   ** The theorem through [GAFT], and why it is opaque

   [saft_solution_set_at] is the solution set at [d]: index [{ i :
   wp_index W & d ~> U (sub_dom (wp_to W i)) }], arrows [projT2], covering
   by [saft_cover_at].  [SAFT_cover_wp_at] feeds it to [GAFT] with a
   well-powering at each [saft_prod U comp G d] only; [SAFT_cover_wp]
   takes #451's [WellPowered].  [GAFT] is [Theorem … Qed] ([About GAFT]:
   "GAFT is opaque"), so the left adjoint of this route does not read
   back at any [d]; [SAFT_cover_wp_is_GAFT] records by [eq_refl] that the
   constant IS [GAFT] at these solution sets.  The transparent left
   adjoint is Adjunction/SAFT/Characterization.v's [SAFT_wellpowered],
   and Adjunction/SAFT/Characterization/Corollaries.v's
   [SAFT_cover_wp_iso] compares the two by Theory/Adjunction.v's
   [left_adjoint_iso].  They are not convertible: in a scratch file with
   Corollaries.v's import list, [projT1 (SAFT_cover_wp …) = projT1
   (SAFT_wellpowered …)] at [eq_refl] is refused by conversion ("cannot
   unify …").  Test/ProbeSAFT453.v pins it as N6
   ([p453_n6_routes_convertible]), beside [p453_cover_is_gaft] and
   [p453_cover_iso].

   ** Strengths

   Every constant is transparent except the three [≈] lemmas
   [saft_point_commutes], [saft_square] and [saft_lift_commutes] ([Qed]).
   The readbacks, all [eq_refl]: [saft_cover_at_index] (the cover's index
   at [h] IS [wp_from W (saft_sub … h)]), [saft_solution_set_at_index]
   (the solution set's index) and [SAFT_cover_wp_is_GAFT].

   ** Universes, measured

   With [Set Printing Universes. About …] (stdlib bounds omitted):

     saft_cover_at@{o dobj h so dp cp w s t pl pa …} :
       Complete@{so so h o} → PreservesImageLimit@{o h dobj h pl so pa so}
       → ∀ (G : Cogenerator@{so o h} C) d
           (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)),
         SubobjectCoverAt@{o dobj h so dp w s t u} U comp G d W
       (* h < dp, h < cp, h < t, h < pl, h < pa, so < pl, o <= s,
          h <= so, h <= s, w <= u, … *)
     SAFT_cover_wp@{o dobj h dp cp w s t pl pa …} :
       Complete@{h h h o} → PreservesImageLimit@{o h dobj h pl h pa h}
       → Cogenerator@{h o h} C → WellPowered@{o h w s t} C
       → { F & Adjunction@{o h h dobj h h h h pa h u} F U }
       (* h < dp, h < cp, h < t, h < pl, h < pa, w <= h, o <= s,
          h <= s, … *)

   - The COVER puts no bound on the well-powering's index [w]: only the
     sort of [SubobjectCoverAt] ([w <= u]) mentions it.  [GAFT] pins it:
     its [SolutionSet@{h …}] index is [h] (applied to [GAFT] directly, a
     solution set indexed one universe up is refused, as
     Adjunction/SAFT/Characterization/Examples.v's header quotes and
     Test/ProbeSAFT453.v's N12, N28 and N29 pin), so [SAFT_cover_wp] has
     [w <= h], and [GAFT]'s [Complete@{h h h o}] puts [Complete]'s shape
     universe at [h].  That is [GAFT]'s regime, [so = h]; the comma route
     of Adjunction/SAFT/Characterization.v is not so pinned.
   - [Cogenerator@{so o h}]: the family's index universe EQUALS the shape
     universe [so].  That is #452's donor collapse through [cogen_power]
     and [cogen_canonical_sub] (Adjunction/SAFT/InitialObject.v's header,
     universes section), not repaired here.
   - The binders are load-bearing.  [dp] is [saft_prod]'s product
     universe (Instance/Discrete.v's [DiscreteCat_Functor], [h < dp]),
     [cp] is [cogen_power]'s, and [ro], [pc], [sa] are the shape,
     [Compose] and [ASpan] universes of [saft_pb_cone]'s cospan.  Before
     they were named, minimization identified [saft_prod]'s product
     universe with [WellPoweredAt]'s [t] in [SubobjectCoverAt], and with
     [PreservesImageLimit]'s seventh slot [pa] in [saft_point], and
     [saft_cover_at]'s readback carried the equation [t = pa]; after,
     no equation between named universes remains in any of the
     twenty-two readbacks.  Where [cont] is applied, its type fixes the
     cone's shape universe at [so] and its [Compose] universe at [pa],
     so [saft_point] writes [image_family_cone@{o dobj h so pa dp}] and
     [saft_lift] writes [saft_pb_cone@{… so pa _}].  Measured in a
     scratch file with this file's import list: the lift with a named
     [pc], [pa < pc], in [pa]'s place is refused with "cannot unify
     "Functor.Compose_obligation_1@{dobj so o pc h} …" and
     "Functor.Compose_obligation_1@{dobj so o pa h} …"", while the same
     definition with [pa] (the control) is accepted.  Test/ProbeSAFT453.v
     pins it as N18 ([p453_n18_lift_at_pc], beside [p453_lift_at_pa]).
   - [pa] in the conclusion's [Adjunction@{… pa …}] is [GAFT]'s own:
     Adjunction/SAFT.v's header quotes [GAFT]'s readback with the same
     slot of [PreservesImageLimit] in the same slot of the adjunction.
   - Stdlib bounds are inherited, not introduced ([About] of each
     constant and of the donors): [h <= EqdepFacts.eq_sigT_sig_eq.u2] and
     [h <= eq_rect_r.u1] on every constant but [saft_index] and
     [saft_fam], from Instance/Discrete.v's [DiscreteCat_Functor] and
     Adjunction/SAFT.v's [cogen_canonical]; [so <= VectorDef.nth.u0], [so
     <= VectorDef.of_list.u0], [h < eq_rect_r.u0] and [dp <=
     eq_rect_r.u0] on [saft_sub], [saft_sub_to], [saft_lift],
     [saft_lift_commutes], [SubobjectCoverAt], [saft_cover_at],
     [saft_solution_set_at] and the two index readbacks, from
     Adjunction/SAFT/InitialObject.v's [complete_pullbacks] ([r <=
     VectorDef.nth.u0], [r <= VectorDef.of_list.u0], [h < eq_rect_r.u0]
     and an [eq_rect_r.u0] bound on one of its internal universes); and
     the same with [h] for [so] on [SAFT_cover_wp_at], [SAFT_cover_wp]
     and [SAFT_cover_wp_is_GAFT], where [so] is [h].  The corollaries
     built on Adjunction/SAFT/Characterization.v's [SAFT_wellpowered] add
     [so <= Fin.case0.u0] and [t <= eq_rect_r.u0], from #452's
     [special_initial_object_wellpowered_at]
     (Adjunction/SAFT/Characterization/Corollaries.v).

   ** Non-vacuity

   Adjunction/SAFT/Characterization/Examples.v applies this file at
   [Id[Sets]] under [Untruncate] ([sets_id_saft_cover] and the separation
   above).  Its header records the boundaries: at [Sets] without
   [Untruncate], and at [Sets^op], the cover is inhabited, as at every
   category, and [GAFT]'s index pin refuses the one-universe-up
   well-powering available there, applied to [GAFT] directly as well as
   through [SAFT_cover_wp_at] (Test/ProbeSAFT453.v's N11, N12, N25 and
   N29).

   ** Not delivered

   No readback of this route's left adjoint.  No covering datum over the
   hypotheses of Mac Lane's Theorem 2 itself (a wide pullback of every
   set of subobjects, and its preservation);
   Adjunction/SAFT/Characterization.v states that theorem.  [cogen_prod]
   and [cogen_power] are not annotated.  The refusals quoted here are
   measured in scratch files whose environments are named, and
   Test/ProbeSAFT453.v pins each where it is cited (N6, N14, N18, N28,
   and N11, N12, N25 and N29 from Examples.v's header); the collapse "t =
   pa" of the Universes section is pinned as staying removed by that
   file's [p453_cover_t_below_pa] and [p453_cover_pa_below_t].

   MEASUREMENTS.  Twenty-two constants ([Print Module]), no [Program]
   obligation, each "Closed under the global context" by its fully
   qualified name.  Closure 111 files excluding itself, counted over
   .Makefile.coq.d: Adjunction/SAFT/InitialObject.v's 110 and that file
   (the same count reproduces InitialObject.v's own 110). *)

(** ** The product over arrows out of [d] *)

(* A cone over [U ◯ DiscreteCat_Functor f] from a plain family of legs. *)
Definition image_family_cone@{o dobj h a pc dq +| h < pc, h < dq +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  {A : Type@{a}} (f : A -> C) (x : D) (pi : ∀ i, x ~> U (f i)) :
  Cone (@Compose@{dobj a o pc h} _ _ _ U (DiscreteCat_Functor@{a h h o h h dq} f)).
Proof.
  unshelve econstructor.
  - exact x.
  - unshelve econstructor.
    + exact pi.
    + intros i j e; destruct e; simpl.
      rewrite fmap_id; apply id_left.
Defined.

(* One factor [cog_obj G j] per arrow [d ~> U (cog_obj G j)]. *)
Definition saft_index@{o dobj h so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (G : Cogenerator@{so o h} C) (d : D) : Type@{so} :=
  { j : cog_index G & d ~> U (cog_obj G j) }.

Definition saft_fam@{o dobj h so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (G : Cogenerator@{so o h} C) (d : D) : saft_index U G d -> C :=
  fun p => cog_obj G (projT1 p).

Definition saft_prod_limit@{o dobj h so dp +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (d : D) :=
  comp _ (DiscreteCat_Functor@{so h h o h h dp} (saft_fam U G d)).

Definition saft_prod@{o dobj h so dp +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (d : D) : C :=
  iprod (saft_fam U G d) (saft_prod_limit@{o dobj h so dp} U comp G d).

(* The canonical point [d ~> U (saft_prod …)], from preservation. *)
Definition saft_point@{o dobj h so dp pl pa +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) :
  d ~> U (saft_prod@{o dobj h so dp} U comp G d) :=
  unique_obj (cont _ _ (saft_prod_limit@{o dobj h so dp} U comp G d)
                (image_family_cone@{o dobj h so pa dp} U (saft_fam U G d) d
                   (fun p => projT2 p))).

Lemma saft_point_commutes@{o dobj h so dp pl pa +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (p : saft_index U G d) :
  fmap[U] (iprod_proj (saft_fam U G d)
             (saft_prod_limit@{o dobj h so dp} U comp G d) p)
    ∘ saft_point@{o dobj h so dp pl pa} U comp cont G d ≈ projT2 p.
Proof.
  exact (unique_property
           (cont _ _ (saft_prod_limit@{o dobj h so dp} U comp G d)
              (image_family_cone@{o dobj h so pa dp} U (saft_fam U G d) d
                 (fun p => projT2 p))) p).
Qed.

(** ** Mac Lane's k, now depending on [h] *)

(* Component [(j, k)] is the projection at [(j, U k ∘ h)]. *)
Definition saft_kappa@{o dobj h so dp cp +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (d : D) (c : C) (h : d ~> U c) :
  saft_prod@{o dobj h so dp} U comp G d ~> cogen_power@{cp so o h so} comp G c :=
  unique_obj (iprod_ump (cogen_power_fam G c)
                (cogen_power_limit@{o h cp so so} comp G c)
                (saft_prod@{o dobj h so dp} U comp G d)
                (fun p => iprod_proj (saft_fam U G d)
                            (saft_prod_limit@{o dobj h so dp} U comp G d)
                            (existT _ (projT1 p) (fmap[U] (projT2 p) ∘ h)))).

Lemma saft_square@{o dobj h so dp cp pl pa +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  fmap[U] (saft_kappa@{o dobj h so dp cp} U comp G d c h)
    ∘ saft_point@{o dobj h so dp pl pa} U comp cont G d
    ≈ fmap[U] (cogen_canonical@{cp so h so o} comp G c) ∘ h.
Proof.
  pose (N := image_family_cone@{o dobj h so pa cp} U (cogen_power_fam G c) d
               (fun p => fmap[U] (projT2 p) ∘ h)).
  pose proof (uniqueness
                (cont _ _ (cogen_power_limit@{o h cp so so} comp G c) N)) as Hu.
  transitivity
    (unique_obj (cont _ _ (cogen_power_limit@{o h cp so so} comp G c) N)).
  - symmetry; apply Hu; intro p; unfold image_leg; simpl.
    rewrite comp_assoc, <- fmap_comp.
    pose proof (unique_property
                  (iprod_ump (cogen_power_fam G c)
                     (cogen_power_limit@{o h cp so so} comp G c)
                     (saft_prod@{o dobj h so dp} U comp G d)
                     (fun p => iprod_proj (saft_fam U G d)
                                 (saft_prod_limit@{o dobj h so dp} U comp G d)
                                 (existT _ (projT1 p) (fmap[U] (projT2 p) ∘ h))))
                  p) as Hk.
    unfold saft_kappa; simpl in Hk |- *.
    rewrite Hk.
    exact (saft_point_commutes@{o dobj h so dp pl pa} U comp cont G d
             (existT _ (projT1 p) (fmap[U] (projT2 p) ∘ h))).
  - apply Hu; intro p; unfold image_leg; simpl.
    rewrite comp_assoc, <- fmap_comp.
    destruct p as [j k].
    pose proof (cogen_canonical_commutes comp G c j k) as Hc.
    simpl in Hc |- *.
    rewrite Hc; reflexivity.
Qed.

(** ** The subobject: the pullback of the canonical mono along [k] *)

Definition saft_sub@{o dobj h so dp cp +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (d : D) (c : C) (h : d ~> U c) :
  SubObj (saft_prod@{o dobj h so dp} U comp G d) :=
  @sub_reindex C (complete_pullbacks comp) _ _
    (saft_kappa@{o dobj h so dp cp} U comp G d c h)
    (cogen_canonical_sub@{o h so cp} comp G c).

Definition saft_sub_to@{o dobj h so dp cp +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C)
  (d : D) (c : C) (h : d ~> U c) :
  Subobject.sub_dom (saft_sub@{o dobj h so dp cp _ _} U comp G d c h) ~> c :=
  pullback_snd _ _ (@pullback C (complete_pullbacks comp) _ _ _
                      (saft_kappa@{o dobj h so dp cp} U comp G d c h)
                      (cogen_canonical@{cp so h so o} comp G c)).

(* [U] carries that pullback to a limit: the cone over the image of the
   cospan, with vertex [d]. *)
Definition saft_pb_cone@{o dobj h so dp cp pl pa ro pc sa +|
    h <= so, h < dp, h < cp, h < pc, h < sa +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  Cone (@Compose@{dobj ro o pc h} _ _ _ U
          (Opposite_Functor@{ro h o}
             (@ASpan@{ro o sa h} (C^op) _ _ _
                (saft_kappa@{o dobj h so dp cp} U comp G d c h)
                (cogen_canonical@{cp so h so o} comp G c)))).
Proof.
  unshelve econstructor.
  - exact d.
  - unshelve econstructor.
    + intro x; destruct x; simpl.
      * exact (saft_point@{o dobj h so dp pl pa} U comp cont G d).
      * exact (fmap[U] (saft_kappa@{o dobj h so dp cp} U comp G d c h)
                 ∘ saft_point@{o dobj h so dp pl pa} U comp cont G d).
      * exact h.
    + (* Nine pairs of objects of [Roof], in the order [destruct] gives;
         [f] is a [RoofHom] from the second to the first. *)
      intros x y f; destruct x, y; simpl in f |- *.
      * (* RNeg, RNeg: an identity *)
        rewrite fmap_id; cat.
      * (* RNeg, RZero: [ZeroNeg], the leg at [RZero] on both sides *)
        reflexivity.
      * (* RNeg, RPos: no arrow *)
        inversion f.
      * (* RZero, RNeg: no arrow *)
        inversion f.
      * (* RZero, RZero: an identity *)
        rewrite fmap_id; cat.
      * (* RZero, RPos: no arrow *)
        inversion f.
      * (* RPos, RNeg: no arrow *)
        inversion f.
      * (* RPos, RZero: [ZeroPos], the square [saft_square] *)
        symmetry; apply saft_square.
      * (* RPos, RPos: an identity *)
        rewrite fmap_id; cat.
Defined.

Definition saft_lift@{o dobj h so dp cp pl pa +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  d ~> U (Subobject.sub_dom (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)) :=
  unique_obj (cont _ _ _ (saft_pb_cone@{o dobj h so dp cp pl pa so pa _}
                            U comp cont G d c h)).

Lemma saft_lift_commutes@{o dobj h so dp cp pl pa +| h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D) (c : C) (h : d ~> U c) :
  fmap[U] (saft_sub_to@{o dobj h so dp cp _ _} U comp G d c h)
    ∘ saft_lift@{o dobj h so dp cp pl pa _ _} U comp cont G d c h ≈ h.
Proof.
  exact (unique_property (cont _ _ _ (saft_pb_cone U comp cont G d c h)) RPos).
Qed.

(** ** The covering datum at [d], and its derivation *)

Definition SubobjectCoverAt@{o dobj h so dp w s t +| h <= so, h < dp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C) (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :
  Type :=
  ∀ (c : C) (h : d ~> U c),
    { i : wp_index W &
      { s : d ~> U (Subobject.sub_dom (wp_to W i)) &
        { t : Subobject.sub_dom (wp_to W i) ~> c & fmap[U] t ∘ s ≈ h } } }.

Definition saft_cover_at@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :
  SubobjectCoverAt@{o dobj h so dp w s t _} U comp G d W.
Proof.
  intros c h.
  exists (wp_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h)).
  destruct (wp_to_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h))
    as [iso _].
  exists (fmap[U] (from iso)
            ∘ saft_lift@{o dobj h so dp cp pl pa _ _} U comp cont G d c h).
  exists (saft_sub_to@{o dobj h so dp cp _ _} U comp G d c h ∘ to iso).
  rewrite fmap_comp, <- comp_assoc, (comp_assoc (fmap[U] (to iso))).
  rewrite <- fmap_comp, iso_to_from, fmap_id, id_left.
  apply saft_lift_commutes.
Defined.

(** ** The solution set at [d], and SAFT through [GAFT] *)

Definition saft_solution_set_at@{o dobj h so dp cp w s t pl pa i +|
    h <= so, h < dp, h < cp, w <= i, h <= i +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :
  SolutionSet@{i dobj o h} U d.
Proof.
  unshelve refine
    {| sol_index := { i : wp_index W & d ~> U (Subobject.sub_dom (wp_to W i)) }
     ; sol_obj := fun p => Subobject.sub_dom (wp_to W (projT1 p))
     ; sol_arr := fun p => projT2 p |}.
  intros c h.
  destruct (saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _}
              U comp cont G d W c h) as [i [s [t e]]].
  exists (existT _ i s); simpl.
  exists t; exact e.
Defined.

Definition SAFT_cover_wp_at@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C)
  (W : ∀ d : D, WellPoweredAt@{w o s h t} (saft_prod@{o dobj h h dp} U comp G d)) :
  { F : D ⟶ C & F ⊣ U } :=
  GAFT U comp cont
    (fun d => saft_solution_set_at@{o dobj h h dp cp w s t pl pa h _ _ _}
                U comp cont G d (W d)).

Definition SAFT_cover_wp@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  { F : D ⟶ C & F ⊣ U } :=
  SAFT_cover_wp_at@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G
    (fun d => WP (saft_prod@{o dobj h h dp} U comp G d)).

(** ** Readbacks *)

(* The cover's index at [h] IS the well-powering's name for the pullback
   subobject [saft_sub]. *)
Example saft_cover_at_index@{o dobj h so dp cp w s t pl pa +|
    h <= so, h < dp, h < cp +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d))
  (c : C) (h : d ~> U c) :
  projT1 (saft_cover_at@{o dobj h so dp cp w s t pl pa _ _ _}
            U comp cont G d W c h)
    = wp_from W (saft_sub@{o dobj h so dp cp _ _} U comp G d c h) := eq_refl.

(* The solution set's index is the well-powering's index paired with a
   [d]-arrow. *)
Example saft_solution_set_at_index@{o dobj h so dp cp w s t pl pa i +|
    h <= so, h < dp, h < cp, w <= i, h <= i +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl so pa so} C D U)
  (G : Cogenerator@{so o h} C) (d : D)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o dobj h so dp} U comp G d)) :
  sol_index (saft_solution_set_at@{o dobj h so dp cp w s t pl pa i _ _ _}
               U comp cont G d W)
    = { i : wp_index W & d ~> U (Subobject.sub_dom (wp_to W i)) } := eq_refl.

(* The theorem IS [GAFT] at those solution sets, whose [Qed] seals the
   left adjoint. *)
Example SAFT_cover_wp_is_GAFT@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP
    = GAFT U comp cont
        (fun d => saft_solution_set_at@{o dobj h h dp cp w s t pl pa h _ _ _}
                    U comp cont G d (WP (saft_prod@{o dobj h h dp} U comp G d)))
  := eq_refl.
