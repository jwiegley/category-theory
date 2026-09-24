Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Cover.

Generalizable All Variables.

(** * Corollaries of the special adjoint functor theorem *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   nLab:      https://ncatlab.org/nlab/show/representable+functor
   nLab:      https://ncatlab.org/nlab/show/complete+category

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
   Corollary, book p. 130 ([maclane:V.8:cor1]): in particular every
   continuous functor K : A → Set is representable, A small-complete,
   well-powered, with small hom-sets and a small cogenerating set.
   Riehl, "Category Theory in Context", Epilogue §E.1, printed p. 252
   ([riehl:E.1:thm-representability-criteria]), clause (i), gives the
   same criterion for a limit-preserving [F : C → Set], with
   intersections of subobjects in place of well-poweredness.  Riehl,
   Corollary 4.7.13, printed p. 178 ([riehl:4.7:cor13]): a category
   satisfying the hypotheses of the special adjoint functor theorem is
   COCOMPLETE, by the theorem applied to the constant-diagram functor
   [Δ : C → C^J].  The statements are read from the catalogue's summaries
   under doc/plan/books; the printed books were not consulted.

   Both corollaries are consequences of any theorem that concludes [{ F
   & F ⊣ U }].  They are stated over Adjunction/SAFT/Characterization.v's
   [SAFT_wellpowered], whose hypotheses are Mac Lane's Corollary's:
   [Complete], [PreservesImageLimit], a [Cogenerator] and #451's
   [WellPowered].

   ** Representability

   [continuous_Set_functor_representable] composes [SAFT_wellpowered] at
   [K : C ⟶ Sets] with Adjunction/Representability/Sets.v's
   [representable_of_left_adjoint] (§V.8 Exercise 1, forward: #348's
   [adj_representable] at the singleton, transported along
   [homafter_one_iso]).  Its representing object is the left adjoint at
   the singleton, by [eq_refl]
   ([continuous_Set_functor_representable_obj]).
   [continuous_Set_functor_representable_iff] is the criterion as a
   biconditional, [Representable K ↔ PreservesImageLimit K]: the forward
   half is Representability/Sets.v's [preserves_image_of_representable].
   It supersedes that file's [saft_representable], the same passage over
   Adjunction/SAFT.v's refutable covering datum, which is kept.

   [continuous_Set_functor_representable_at] follows Riehl's route: it
   asks for well-poweredness at the ONE object the singleton needs,
   [saft_prod K comp G SetsOne], and goes through the category of
   elements rather than through an adjunction:
   Adjunction/SAFT/Characterization/Cover.v's [saft_solution_set_at] at
   the singleton, Adjunction/GAFT.v's [comma_initial_of_sols], and
   Representability/Sets.v's [representable_of_comma_initial].  It runs
   at [GAFT]'s regime, [Complete@{h h h o}] and [Cogenerator@{h o h}].

   ** Cocompleteness

   [saft_colim] applies [SAFT_wellpowered] to [@Diagonal C J : C ⟶ [J,
   C]], with [C] the DOMAIN, so only [C]'s completeness, cogenerating
   family and well-powering appear; [[J, C]] needs nothing.  Continuity
   of the diagonal is #450's Adjunction/Diagonal/Limit.v
   [Diagonal_continuous], read as [PreservesImageLimit] by
   Construction/Comma/Creation.v's [Continuous_PreservesImageLimit].
   [saft_cocomplete] turns the left adjoint into colimits of every shape
   by #353's [Diagonal_left_adjoint_HasColimits].

   THE [[J, C]] PROVISO.  Riehl's proof uses that [C^J] is locally small
   for small [J].  In tree the theorem needs [D := [J, C]] to share [C]'s
   hom universe [h], and the homs of [Fun J C] sit at or above the
   objects of [J], so the shapes are [J : Category@{jo h h}] with [jo <=
   h].  Measured in scratch files with this file's import list, each
   beside an instrument and a control at [jo <= h] that are accepted: at
   [h < jo], [@Diagonal C J] alone is accepted, and [SAFT_wellpowered
   (@Diagonal C J) comp (Continuous_PreservesImageLimit
   Diagonal_continuous) G WP] is refused at the functor, "(universe
   inconsistency: Cannot enforce <1> = h because h < <2> <= <1>)", <1>
   being the hom universe of the [Fun] the diagonal lands in (the
   placeholders number universes the scratch compile generated, by first
   appearance).  Test/ProbeSAFT453.v pins it as N19
   ([p453_n19_diag_large]), beside [p453_diag_small] and
   [p453_diag_alone]; it quotes the whole message, whose numbering reads
   the same chain as "<2> = h because h < <7> <= <2>".  That refusal is
   the substantive one.  [saft_colim] itself is refused at its argument
   [J], "The term "J" has type "Category@{jo h h}" while it is expected
   to have type "Category@{<3> h h}" (universe inconsistency: Cannot
   enforce jo = <3> because <3> <= <4> < jo)", but that second refusal
   only restates [saft_colim]'s own binder [jo <= h], is quoted as such
   and is not pinned.  So completeness is assumed at shapes [so >= h] and
   cocompleteness is delivered at shapes [jo <= h]; they meet at [so =
   h], which is where [Sets_Complete] sits.

   [Cocomplete@{h jo h o}]: the colimit-datum universe is [h].  That is
   inherited from [Diagonal_left_adjoint_HasColimits], whose readback is
   [HasColimitsOfShape@{u7 u0 u u0 u1} J C] with the colimit-datum slot
   (the second) the hom universe [u0]; declaring a separate [cr] for it
   in [saft_cocomplete]'s binder read back as the equation [h = cr].
   Test/ProbeSAFT453.v pins it as a refusal at [h < cr], N20
   ([p453_n20_cocomplete_cr_above], [saft_cocomplete]'s body restated),
   beside [p453_cocomplete_cr_le] at [h <= cr].

   ** The two routes, and the two families

   [SAFT_cover_wp_iso] compares Cover.v's [SAFT_cover_wp] (through
   [GAFT], opaque) with [SAFT_wellpowered] (through the comma categories,
   transparent) by Theory/Adjunction.v's [left_adjoint_iso]: their left
   adjoints are isomorphic in [Cat].  They are not convertible (Cover.v's
   header, measured; Test/ProbeSAFT453.v's N6).  They index the same
   family: [comma_cogenerator_index] reads the index of
   Adjunction/SAFT/Characterization.v's [comma_cogenerator U d G] as
   Cover.v's [saft_index U G d] by [eq_refl].  The PRODUCTS are not
   convertible: in a scratch file with this file's import list, [snd (`1
   (cogen_prod (Comma_Complete cont comp) (comma_cogenerator U d G))) =
   saft_prod U comp G d] at [eq_refl] is refused by conversion ("cannot
   unify …"), beside an accepted control ([comma_cogenerator_index]'s
   statement): they are limits of two different diagram terms.
   Test/ProbeSAFT453.v pins it as N7 ([p453_n7_same_product]), beside
   [p453_same_index].

   ** Universes

   Every constant names its universes: [o] the objects of [C], [h] the
   homs, [so] [Complete]'s shape universe, [c] the cogenerating family's
   index, [w s t] the well-powering's, [pl pa] [PreservesImageLimit]'s
   sort and auxiliary slots, [su] the objects of [Sets@{h su}] ([K]'s
   codomain has its homs at [h]: small hom-sets), [ra rt] the two
   universes of [Representable], [jo] the shapes, and [fo fa] the object
   and auxiliary universes of [[J, C]] and of [Diagonal].  Without the
   last two, minimization identified [[J, C]]'s object universe with
   [WellPowered]'s [s], and [Diagonal]'s auxiliary with [WellPowered]'s
   [t] (the collapse the #453 scouts measured); without [ra rt],
   [Representable]'s sort was identified with [WellPowered]'s [s].  Two
   equations are inherited from donors and are not repaired here: [h =
   cr] above, and, in [continuous_Set_functor_representable_iff] only,
   [pa = su], through [preserves_image_of_representable], whose readback
   is [PreservesImageLimit@{u8 u7 u1 u7 u u0 u1 u2}] with its seventh
   slot equal to [Sets]' object universe [u1] (Test/ProbeSAFT453.v's N21,
   [p453_n21_repr_iff_pa_below_su], refuses the biconditional at [pa <
   su], beside [p453_repr_pa_below_su] and [p453_repr_iff_pa_le_su]).
   Every constant here built on [SAFT_wellpowered] also inherits whatever
   equation that constant's own readback carries between its named
   universes; [continuous_Set_functor_representable_at], built on Cover.v
   alone, reads back with no equation between named universes.  Against
   the landed Adjunction/SAFT/Characterization.v, whose
   [SAFT_wellpowered] carries none, [About] of the eight constants
   searched for " = " finds [su = pa] in
   [continuous_Set_functor_representable_iff] and nothing else (the one
   other hit is the equality stated by
   [continuous_Set_functor_representable_obj]).  Stdlib bounds are
   inherited ([About]): on the constants built on [SAFT_wellpowered], [so
   <= Fin.case0.u0] and [t <= eq_rect_r.u0] from #452's
   [special_initial_object_wellpowered_at]; on every constant but
   [comma_cogenerator_index], the [VectorDef] bounds and [h <
   eq_rect_r.u0] from Adjunction/SAFT/InitialObject.v's
   [complete_pullbacks] (at [h] where [so] is [h]), and [h <=
   EqdepFacts.eq_sigT_sig_eq.u2] as on Cover.v's constants.

   ** Not delivered

   No representability or cocompleteness over the hypotheses of Mac
   Lane's Theorem 2 (wide pullbacks of subobjects in place of
   well-poweredness), nor over Riehl's intersections.  No cocompleteness
   at shapes whose objects sit above the homs (the proviso).  No
   comparison of the two products beyond the index.

   MEASUREMENTS.  Eight constants ([Print Module]), no [Program]
   obligation, all transparent, each "Closed under the global context" by
   its fully qualified name.  A satellite because
   Adjunction/Representability/Sets.v, Adjunction/Diagonal/Limit.v and
   Construction/Comma/Creation.v are needed here and are not in
   Adjunction/SAFT/Characterization/Cover.v's closure (measured over
   .Makefile.coq.d), nor in Adjunction/SAFT/Characterization.v's.
   Closure 149 files excluding itself, counted over .Makefile.coq.d. *)

(** ** Mac Lane's Corollary: continuous [Sets]-valued functors are representable *)

Definition continuous_Set_functor_representable@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K :=
  representable_of_left_adjoint K (projT2 (SAFT_wellpowered K comp cont G WP)).

(* The representing object is the left adjoint at the singleton. *)
Example continuous_Set_functor_representable_obj@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @repr_obj C K
    (continuous_Set_functor_representable K comp cont G WP
       : Representable@{ra rt su o h} K)
    = fobj[projT1 (SAFT_wellpowered K comp cont G WP)] SetsOne := eq_refl.

Definition continuous_Set_functor_representable_iff@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K
    ↔ @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K.
Proof.
  split.
  - exact preserves_image_of_representable.
  - intro cont; exact (continuous_Set_functor_representable K comp cont G WP).
Defined.

(* Riehl's route (the category of elements), with well-poweredness at the
   ONE object the singleton needs, through the d-dependent cover. *)
Definition continuous_Set_functor_representable_at@{o h dp cp w s t su pl pa ra rt +|
    h < dp, h < cp, w <= h, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h su h pl h pa h} C Sets@{h su} K)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o su h h dp} K comp G SetsOne)) :
  Representable@{ra rt su o h} K :=
  representable_of_comma_initial K
    (comma_initial_of_sols K SetsOne comp cont
       (saft_solution_set_at@{o su h h dp cp w s t pl pa h _ _ _}
          K comp cont G SetsOne W)).

(** ** Riehl 4.7.13: the SAFT hypotheses give cocompleteness *)

Definition saft_colim@{o h so c w s t jo fo fa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa +}
  (C : Category@{o h h}) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C)
  (J : Category@{jo h h}) :
  { L : @Fun@{jo h o h fo h fa} J C ⟶ C & L ⊣ @Diagonal@{fo h fa jo o h} C J } :=
  SAFT_wellpowered (@Diagonal@{fo h fa jo o h} C J) comp
    (Continuous_PreservesImageLimit Diagonal_continuous) G WP.

Definition saft_cocomplete@{o h so c w s t jo fo fa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @Cocomplete@{h jo h o} C :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (saft_colim C comp G WP J
                        : { L : @Fun@{jo h o h fo h fa} J C ⟶ C
                          & L ⊣ @Diagonal@{fo h fa jo o h} C J })) F.

(** ** The two routes to the left adjoint agree up to isomorphism *)

Definition SAFT_cover_wp_iso@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  projT1 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP)
    ≈ projT1 (SAFT_wellpowered U comp cont G WP) :=
  left_adjoint_iso U _ _
    (projT2 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP))
    (projT2 (SAFT_wellpowered U comp cont G WP)).

(** ** The two routes index the same family *)

(* The comma category's cogenerating family is indexed by the arrows out of
   [d], exactly the index of [saft_prod]. *)
Example comma_cogenerator_index@{o dobj h so +| h <= so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (G : Cogenerator@{so o h} C) :
  cog_index (comma_cogenerator U d G) = saft_index U G d := eq_refl.
