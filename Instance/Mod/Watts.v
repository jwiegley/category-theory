(** * Watts' theorem through SAFT: Mac Lane's contravariant text form and
      Exercise 3's covariant form *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
              ed. (GTM 5), §V.8, printed pp. 131–132 (PDF pp. 140–141),
              ledger items `maclane:V.8:thm-watt` and `maclane:V.8:ex3`
              (issue #454), read from the printed page.  The text, p. 131:
              "Watt's Theorem [1960] is another example.  Any ring R is a
              generator in the category R-Mod, hence a cogenerator in
              (R-Mod)^op.  It follows that any contravariant additive
              functor T on R-Mod to Ab which takes small colimits to
              limits is representable by a group isomorphism
              T ≅ hom_R(−, C) for some R-module C."  Exercise 3, p. 132:
              "Use Exercise 2(b) and the special adjoint functor theorem
              to prove that any continuous additive functor T: R-Mod → Ab
              is representable. (Watt's theorem)."  The book spells the
              name "Watt's"; the author is Charles E. Watts.  (The in-repo
              catalogue, doc/plan/books/maclane/inventory/V.json,
              summarises both in its own words; the quotations here are
              the printed page's.)
   Papers:    C. E. Watts, "Intrinsic characterizations of some additive
              functors", Proc. Amer. Math. Soc. 11 (1960), 5–8; and
              S. Eilenberg, "Abstract description of some basic
              functors", J. Indian Math. Soc. (N.S.) 24 (1960), 231–234 —
              the two original articles, as the nLab page lists them.
   nLab:      https://ncatlab.org/nlab/show/Eilenberg-Watts+theorem
   nLab:      https://ncatlab.org/nlab/show/cogenerator
   nLab:      https://ncatlab.org/nlab/show/injective+object
              The nLab page "injective cogenerator" does not exist (HTTP
              404, measured with curl on 2026-09-24, as
              Instance/Mod/Cogenerator.v also records).

   PATH.  The issue suggests Instance/Module/Watts.v.  The tree keeps its
   module files under Instance/Mod/ (#258, #401, #449), so this file is
   Instance/Mod/Watts.v: a deviation in path only.

   THIS FILE AND THE UNCONDITIONAL THEOREM.  For the text form this file
   is strictly weaker than Instance/Mod/Watts/Unconditional.v's
   [watts_theorem_unconditional], which proves the book's contravariant
   statement with no hypothesis beyond the book's own two (and
   [Set < c]), through GAFT and an explicit solution set; that file is
   #454's headline for the text form.  This one is kept because it is
   Mac Lane's SAFT route, which the issue's Reviewer line names ("the
   representability must be derived from SAFT plus additivity"), and
   because Exercise 3, the covariant form, is delivered only here, and
   conditionally.  It imports the unconditional file, and section 6
   measures the relation in tree: [watts_theorem_via_unconditional]
   derives [watts_theorem]'s statement from [watts_theorem_unconditional],
   with [Untruncate] carried and not consumed, and
   [watts_unconditional_coext] and [watts_unconditional_coext_2a] are the
   text-form witness of section 4 without [Untruncate].  Which of this
   file's constants the unconditional theorem subsumes, and which not, is
   listed in that file's header, THE HEADLINE, AND THE SAFT ROUTE.

   ** BACKGROUND

   Watts and Eilenberg showed, independently and in the same year, that
   the functors between module categories which respect colimits are the
   tensor functors: an additive, cocontinuous F : Mod_R → Mod_S is
   naturally isomorphic to − ⊗_R N, where N is F(R) and R acts on it by F
   applied to left multiplications (the nLab page's statement and its
   first Remark).  The reason is that R generates R-Mod: every module is a
   quotient of a free one, a coproduct of copies of R, so a functor that
   respects colimits is fixed by its value at R and by the action of R's
   endomorphisms there.  The nLab page records generalisations to right
   exact functors (Nyman and Smith), to homotopical and higher algebra
   (Hovey; Lurie) and to categories enriched in a bicategory (Arkor and
   McDermott).  Mac Lane gives the result as an application of the
   special adjoint functor theorem and states the dual reading: a
   CONTRAVARIANT additive functor that turns colimits into limits is a
   hom functor hom_R(−, C).  Exercise 3 asks for the covariant analogue,
   a continuous additive T : R-Mod → Ab is hom_R(A, −), which needs a
   cogenerator of R-Mod and so Exercise 2(b).

   ** THE BOOK'S PROOF, AND THE ONE HERE

   Mac Lane's sketch: "by the special adjoint functor theorem T:
   (R-Mod)^op → Ab has a left adjoint F; since T is additive, the
   adjunction Ab(G, TA) ≅ hom_R(A, FG), G ∈ Ab, A ∈ R-Mod, is an
   isomorphism of additive groups; set G = Z to get
   TA ≅ Ab(Z, TA) ≅ hom_R(A, FZ)", so C = Fℤ.  The first step is
   [watts_theorem_adjoint] below, verbatim; the last is section 5's
   [ab_hom_Z_iso], Ab(ℤ, X) ≅ X natural in X as Ab-valued functors, with
   ℤ read as the free abelian group on one point [FreeAb SetsOne], and
   [watts_theorem_Fz], the representing object ≅ F(ℤ) in RMod R.  (The
   isomorphism Ab(ℤ, X) ≅ X is the additive upgrade at Id[Ab] of the
   representation [free_ab_adjunction] gives, and the comparison of
   representing objects does not even need it.  Still open: no
   isomorphism of the free group on one point with Instance/Ab/Free.v's
   [ab_int] is built, the comparison Instance/Ab/Generator.v records as
   left undone for [FreeAbObject unit_setoid_object]; [SetsOne] is
   Construction/Elements.v's name for the terminal object of [Sets].)
   The representation itself is obtained the way the issue's Reviewer
   line asks, "derived from SAFT plus additivity", through Yoneda:

     SAFT.  Adjunction/SAFT/Characterization/Corollaries.v's
     [continuous_Set_functor_representable] — Mac Lane's Corollary on
     book p. 130, built on #453's [SAFT_wellpowered] — represents the
     Sets-valued functor [Ab_Forget ◯ T]; its representing object is the
     left adjoint of [Ab_Forget ◯ T] at the one-point set.
     ADDITIVITY.  Functor/Representable/Additive.v's [watt_ab_repr]
     upgrades a representation of [Ab_Forget ◯ T], for T additive, to an
     isomorphism [HomAb A ≅ T] in the functor category into [Ab], with
     the SAME components.

   For the text form the SAFT is applied at C := (RMod R)^op: complete
   because RMod R is cocomplete, cogenerated by R, and well-powered because
   RMod R is co-well-powered.  For Exercise 3 it is applied at
   C := RMod R: complete, well-powered, with a cogenerator supplied.

   ** CONSUMED, NOT BUILT

     - Adjunction/SAFT/Characterization.v's [SAFT_wellpowered] and its
       satellite Corollaries.v's [continuous_Set_functor_representable]
       (#453).
     - Instance/Mod/Colimit.v's [RMod_Cocomplete_via_GAFT], read as
       completeness of (RMod R)^op by Construction/Product/Limit.v's
       [Complete_op_of_Cocomplete]; Instance/Mod/Limit.v's
       [RMod_Complete] and [RMod_Forget_Ab_creates_continuous] (#449).
     - Instance/Mod/WellPowered.v's [RModop_Cogenerator] (R as a
       generator of RMod R, read as a cogenerator of the opposite),
       [RMod_CoWellPowered_untruncate] and [RMod_WellPowered_untruncate].
     - Functor/Representable/Additive.v's [HomAb], [CoHomAb],
       [CoHomAb_continuous], [LocallyPropositional_op], [watt_ab_repr],
       [watt_ab_iso] and [wab_obj].
     - Construction/Comma/Limit.v's [PreservesImageLimit] with
       Construction/Comma/Creation.v's [PreservesImageLimit_Continuous]
       and [Continuous_PreservesImageLimit]; Structure/Limit/
       Preservation.v's [continuous_compose] and [cone_assoc_inv];
       Instance/Ab/Limit.v's [Ab_Forget_creates_continuous] and
       [Ab_Forget_reflects_limits]; Functor/Hom/Continuous.v's
       [representable_iso_ContinuousFunctor]; Instance/Fun.v's
       [iso_equiv] and [equiv_iso].
     - Instance/Mod/Cogenerator.v's [QZ_injective_cogenerator],
       [QZ_family_cogenerates], [QZ_Cogenerator] and [coext_cogenerator]
       (Exercise 2(b)); Instance/Mod/Coextension.v's [coex_adjunction] and
       [CoextObj]; Instance/Mod/HomTensor.v's [HomZL] and
       [homzl_coext_iso] (Exercise 2(a) at B := R).
     - Adjunction/Continuity.v's [right_adjoint_Continuous] with
       Adjunction/Opposite.v's [Opposite_Adjunction];
       Instance/Mod/Representable.v's [rmod_representable];
       Functor/Representable.v's [repr_induced_iso] and
       [repr_unique_iso]; Construction/Opposite.v's
       [Isomorphism_Opposite]; Instance/Sets/Classifier/OneLevel.v's
       [Untruncate].
     - For section 5: Instance/Ab/Free.v's [FreeAb] and
       [free_ab_adjunction]; Adjunction/Representability/Sets.v's
       [representable_of_left_adjoint] and [Representable_transport];
       Adjunction/Compose.v's [Adjunction_Compose];
       Construction/Elements.v's [SetsOne]; Structure/AbCategory.v's
       [Id_AdditiveFunctor].
     - For section 6: Instance/Mod/Watts/Unconditional.v's
       [watts_theorem_unconditional] and
       [RModop_continuous_representable].

   ** WHAT IS BUILT

   (1) [RMod_Forget_Ab_additive]: the forgetful functor is additive, at
   [reflexivity].  The continuity of the Ab-valued hom functors,
   [HomAb_continuous] and [CoHomAb_continuous], is not built here: its
   one definition each is in Functor/Representable/Additive.v, and both
   Watts files consume it.

   (2) The text form.  **[watts_theorem T AF contT U]**, the name the
   issue's Verification block prints: for T : (RMod R)^op ⟶ Ab additive
   ([AF], against [AbEnriched_op (RMod_AbEnriched R)] and
   [Ab_AbEnriched]) and continuous on (RMod R)^op ([contT :
   PreservesImageLimit T] — for every diagram K into (RMod R)^op, that is
   every diagram of modules read backwards, and every chosen limit of K
   there, that is every chosen COLIMIT of modules, T carries it to a
   limit of Ab), and [U : Untruncate], some module A with
   [CoHomAb (RMod_AbEnriched R) A ≅ T] in [@Fun ((RMod R)^op) Ab]: T is
   naturally isomorphic, as an Ab-valued functor, to hom_R(−, A).
   [watts_theorem_sets] is the Sets-level representation it upgrades,
   [watts_theorem_obj] reads the representing object back as that
   representation's at [eq_refl], and [watts_theorem_to_at] reads back
   the iso's components as the representation's own, at [eq_refl].
   [watts_theorem_adjoint] is the book's first step: the left adjoint of
   T itself, by [SAFT_wellpowered] at D := Ab.  The continuity
   hypothesis is stated in the form SAFT consumes; Construction/Comma/
   Creation.v converts it to and from [ContinuousFunctor] in both
   directions.

   (3) Exercise 3.  **[watts_ex3 T AF contT G U]**: for T : RMod R ⟶ Ab
   additive and continuous, a cogenerator [G] of RMod R and [U :
   Untruncate], some A with [HomAb (RMod_AbEnriched R) A ≅ T]; the
   Sets-level step is [watts_ex3_sets].  **[watts_ex3_QZ]** takes the
   cogenerator from Exercise 2(b), [snd (QZ_injective_cogenerator R HI
   HC)], so that its premises are the book's "The additive group Q/Z of
   rational numbers modulo 1 is known to be an injective cogenerator of
   Ab" (Exercise 2(b)), taken as hypotheses ([HI : Injective Ab QZ], [HC
   : QZ_family_cogenerates]), together with [U].  [watts_ex3_QZ_cogenerator]
   shows at [eq_refl] that the cogenerator used is
   [coext_cogenerator R (QZ_Cogenerator HC)]: the
   injectivity premise [HI] is carried, as the exercise states it, but
   not consumed, SAFT asking only for the cogenerating half.

   (4) The witnesses of NON-VACUITY below: [watts_ex3_forget],
   [RMod_Forget_equiv] and [watts_ex3_forget_obj]; [HomAbForget R A] (the
   functor M ↦ Hom_Ab(U M, A) on (RMod R)^op), [HomAbForget_additive],
   [HomAbForget_continuous], [watts_theorem_coext], [coext_representable],
   [watts_theorem_coext_obj] and [watts_theorem_coext_obj_2a].  And
   [watt_at_forget], the one with NO hypothesis:
   [HomAb (RMod_AbEnriched R) (Ring_RMod R) ≅ RMod_Forget_Ab R] in the
   functor category into [Ab], Functor/Representable/Additive.v's
   upgrade applied to Instance/Mod/Representable.v's [rmod_representable]
   carried along [RMod_Forget_equiv].  It is the conclusion of Exercise 3
   at T := [RMod_Forget_Ab R], reached without the special adjoint
   functor theorem, and so without [G] or [U].

   (5) Mac Lane's last step (section 5).  [ab_hom_Z_iso :
   HomAb Ab_AbEnriched (FreeAb SetsOne) ≅ Id[Ab]] in [@Fun Ab Ab] is
   Ab(ℤ, X) ≅ X, natural in X, with ℤ the free abelian group on one
   point: the upgrade at T := Id[Ab] of the representation of [Ab_Forget]
   that [free_ab_adjunction] gives, through [Ab_Forget_Id_equiv].
   [watts_theorem_Fz T AF contT U] is C ≅ F ℤ: the representing object of
   [watts_theorem] is isomorphic in RMod R to the left adjoint F of
   [watts_theorem_adjoint] at [FreeAb SetsOne] -- [repr_unique_iso]
   between the SAFT representation of [Ab_Forget ◯ T] and the one the
   composite adjunction FreeAb ⊣ Ab_Forget, F ⊣ T gives.  It carries
   [watts_theorem]'s hypotheses, [U] among them.

   (6) What the unconditional theorem subsumes (section 6).
   [watts_theorem_via_unconditional] has [watts_theorem]'s statement,
   hypotheses and universe binders (Representable's two excepted, which
   the statement does not mention), and its body is
   [watts_theorem_unconditional T AF (PreservesImageLimit_Continuous
   contT)]: [U] is carried and not consumed.
   [watts_unconditional_coext R A] is the text form at T :=
   [HomAbForget R A] with NO [Untruncate]: the module
   [watts_theorem_unconditional] returns there is ≅ [CoextObj R A] in
   RMod R, by [repr_unique_iso] between [coext_representable] and
   [RModop_continuous_representable]; [watts_unconditional_coext_2a]
   continues it to [HomZL R_R A] through [homzl_coext_iso].  These are
   the unconditional counterparts of [watts_theorem_coext_obj] and
   [watts_theorem_coext_obj_2a].

   ** THE CONDITIONS, PLAINLY

   Neither theorem of this file is unconditional, and no in-tree term
   discharges its conditions.  The text form's CONCLUSION needs neither
   condition: Instance/Mod/Watts/Unconditional.v proves it with no
   hypothesis, and section 6 derives [watts_theorem]'s statement from
   it; what is conditional here is the SAFT route.

     - [Untruncate] — "every propositionally truncated type has an
       element" — is a hypothesis of both.  The tree inhabits it nowhere
       (Adjunction/SAFT.v's header: "the tree inhabiting neither
       [Untruncate] nor [IEM]"), and Instance/Sets/Classifier/OneLevel.v
       derives it from informative excluded middle
       ([untruncate_of_IEM]).  The text form spends it exactly once, in
       [RMod_CoWellPowered_untruncate]: a quotient object of a module is
       indexed by its kernel only if a preimage under the epi can be
       produced as data, and [rmod_epic_surjective] returns it only in
       [Prop].  Exercise 3 spends it in [RMod_WellPowered_untruncate], to
       rebuild a subobject's domain from its truncated image.
       Instance/Mod/WellPowered.v quotes the refusals at the pin without
       it.  One universe up neither needs it: that file's
       [RMod_WellPoweredAt_up] and [RMod_CoWellPowered_up] (the latter
       indexing each quotient object by its codomain, map and
       [Prop]-level surjectivity) are unconditional.  But
       [SAFT_wellpowered] consumes a [WellPowered], whose index sits at
       or below the hom universe ([w <= h] in its binder), and both one-up
       families are refused where [WellPowered@{o c c o x}] (respectively
       [CoWellPowered@{o c c o x}]) is expected, "Cannot enforce <1> = c
       because c < <1>" (the same file's WHY [Untruncate], MEASURED); so
       [U] stays.
     - Everything else the text form uses is unconditional: the
       cocompleteness [RMod_Cocomplete_via_GAFT] (Prop-congruence solution
       sets, #450's template) and the cogenerator R of (RMod R)^op
       ([RModop_Cogenerator]).
     - Exercise 3 takes a cogenerator of RMod R as well, the hypothesis
       [G], which the special adjoint functor theorem consumes at RMod R.
       In [watts_ex3_QZ] that hypothesis becomes the book's premise on
       ℚ/ℤ, and Instance/Mod/Cogenerator.v shows the premise is
       classical: [QZ_cogenerates_Ab_DNE] derives ∀ P, ¬¬P → P from [HC],
       and [QZ_injective_WLEM] derives the informative ∀ P, (¬P) + (¬¬P)
       from [HI].  Those are closed theorems of the core that do not
       refute the premises; they show the premises cannot be proved
       without an axiom unless double-negation elimination can.  So
       [watts_ex3_QZ]'s hypotheses have no in-tree inhabitant, and no
       inhabitant of all of them is constructible axiom-free unless DNE
       is.  The ℚ/ℤ premise is the one condition of Exercise 3 PROVED
       classical.  Nothing in tree proves [G] or [U] NECESSARY for the
       covariant form: the SAFT route consumes both, no other route to it
       is attempted, and [RMod R] well-powered at the pin without [U] is
       neither built nor refuted (Instance/Mod/WellPowered.v).
     - The text form holds at [RingObject@{c c c}] only: the ring's
       auxiliary, carrier and proof universes coincide (UNIVERSES below).
       [watts_theorem_unconditional] keeps them apart.

   ** STRENGTHS, STRICT FIRST

   At [eq_refl]: [watts_theorem_obj] (the representing object of the text
   form IS [repr_obj] of [watts_theorem_sets], so by Corollaries.v's
   [continuous_Set_functor_representable_obj] the SAFT left adjoint of
   [Ab_Forget ◯ T] at the one-point set), [watts_theorem_to_at] (each
   component of the Ab-level isomorphism is the Sets-level
   representation's component, unchanged) and [watts_ex3_QZ_cogenerator].
   Up to ≅ in RMod R: the representing objects of the two witnesses,
   [watts_ex3_forget_obj] (≅ [Ring_RMod R]) and [watts_theorem_coext_obj]
   (≅ [CoextObj R A]) with [watts_theorem_coext_obj_2a] (≅ [HomZL R_R A],
   Exercise 2(a)'s hom_ℤ(R, A)).  The headline isomorphisms are
   isomorphisms in the functor category into [Ab], componentwise ≈ of
   group homomorphisms.  REFUSED at [eq_refl], measured by appending one
   [Example] to a copy of this whole file, in environment
   [R : RingObject], [G : Cogenerator (RMod R)], [U : Untruncate]:
   [projT1 (watts_ex3_forget R G U) = Ring_RMod R] — "The term "eq_refl"
   has type "projT1 (watts_ex3_forget R G U) = projT1 (watts_ex3_forget R
   G U)" while it is expected to have type "projT1 (watts_ex3_forget R G
   U) = Ring_RMod R" (cannot unify "projT1 (watts_ex3_forget R G U)" and
   "Ring_RMod R")": the SAFT object is an intersection of subobjects of
   a cogenerator power, and it depends on the variable [U]; the
   comparison is an isomorphism, not a conversion.

   By conversion, and so named in the statements: [watt_at_forget]'s
   representing object is [Ring_RMod R] and [ab_hom_Z_iso]'s is
   [FreeAb SetsOne].  Up to ≅ in RMod R: [watts_theorem_Fz], the
   representing object of the text form ≅ F ℤ.

   Transparency: five [Defined] and no [Qed], counted by token outside
   comments; [RMod_Forget_Ab_additive], [RMod_Forget_equiv],
   [HomAbForget_additive], [coext_representable] and
   [Ab_Forget_Id_equiv].  Every other constant is a term [Definition] or
   [Example].  FLIPS: see AXIOMS AND MEASUREMENTS.

   ** UNIVERSES, MEASURED

   By [About] under [Set Printing Universes], stdlib bounds
   ([compose.u0], [Projections.u0], [prod_rect.u0], [ID.u0],
   [Fin.case0.u0], [VectorDef.*], ...) left out, except [eq_rect_r],
   attributed below.  [RMod@{o x a p c} : RingObject@{a c p} →
   Category@{o c c}] names the ring's (auxiliary, carrier, proof)
   universes, [RMod]'s object universe o and its second universe x; the
   homs sit at the carrier c.  [Ab@{b c}] is the target, its object
   universe b (a in the text form) and its carrier the same c.
   [PreservesImageLimit@{o c b c pk c pa c}] names its sort [pk] and its
   auxiliary slot [pa]; its shape slots are c.  [Representable@{ra rt pa
   o c}] names Representable's two own universes [ra rt].

     watts_theorem@{c o x a pk pa ra rt +} :
       ∀ {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c}),
       AdditiveFunctor@{o c a} T → PreservesImageLimit@{o c a c pk c pa c}
       → Untruncate@{c} → ∃ A : obj[RMod@{o x c c c} R],
         CoHomAb@{o c a} (RMod_AbEnriched@{x o c c c} R) A ≅ T
     watts_ex3@{a c p o x b g pk pa ra rt +} :
       ∀ {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c}),
       AdditiveFunctor@{o c b} T → PreservesImageLimit@{o c b c pk c pa c}
       → Cogenerator@{g o c} (RMod@{o x a p c} R) → Untruncate@{c}
       → ∃ A, HomAb@{o c b} (RMod_AbEnriched@{x o a p c} R) A ≅ T
     watts_ex3_QZ@{r o x b pk pa ra rt +} :
       ∀ {R : RingObject@{r r r}} (T : RMod@{o x r r r} R ⟶ Ab@{b r}),
       … → Injective Ab@{o r} QZ@{r r r _}
       → QZ_family_cogenerates@{o r _ o _} → Untruncate@{r} → ∃ A, …
       (the third slot of [QZ_family_cogenerates], the index universe of
       the one-member family, is left free, bounded by the carrier r:
       SAFT's [c <= so])

   Explicit universe instances are written only on constants whose
   instance length has a precedent elsewhere in tree ([RMod], [Ab],
   [Sets], [RingObject], [AbObject], [Cogenerator], [Representable],
   [PreservesImageLimit], [Untruncate]); [ContinuousFunctor], [QZ],
   [RMod_Forget], [RMod_Forget_Ab] and this file's own extensible
   [HomAbForget] are reached through type ascriptions instead, so that a
   different instance length on another Coq version cannot refuse them.

   No constant of this file carries a universe EQUATION: searching the
   constraint blocks of the [About] output of all twenty-seven, each
   queried by its fully qualified name, for " = " finds none (run on a
   scratch file, the same search finds the equation of a definition
   taking [F : D ⟶ C] and [U : C ⟶ D] and those of [Adjunction]'s own
   [About]).  Over the whole output, " = " occurs only in the statements
   of the [eq_refl] readbacks [watts_theorem_obj], [watts_theorem_to_at]
   and [watts_ex3_QZ_cogenerator].  What each inherits, and from where:

     - [RingObject@{c c c}] in the text form and its witness.  Forced by
       [RModop_Cogenerator], whose ring is [RingObject@{c c c}] because
       [Ring_RMod R] carries R's own abelian group
       (Instance/Mod/WellPowered.v measures that).  Here:
       [watts_theorem_sets]'s body at [R : RingObject@{a c p}] with
       [c < a] declared is refused, "The term "R" has type
       "RingObject@{a c p}" while it is expected to have type
       "RingObject@{<1> <1> <1>}" (universe inconsistency: Cannot enforce
       c = a because c < a)"; the same body
       with no constraint declared is accepted and reads back [a = c],
       [a = p].  Exercise 3 keeps the ring's three universes apart;
       [watts_ex3_QZ] is at [RingObject@{r r r}] by [CoextObj]'s own
       identification (Instance/Mod/Coextension.v), and the [Ab] of its
       two ℚ/ℤ premises sits at RMod's object universe o, as in
       [QZ_injective_cogenerator]'s own readback, which under this file's
       imports prints [@Injective Ab@{a r} QZ@{r r r u0}] beside
       [Cogenerator@{c a r} (RMod@{a u r r r} R)] ([Injective] is the
       notation for [Projective] at the opposite category).
     - [Set < c]: from [RMod_WellPowered_untruncate] and
       [RMod_CoWellPowered_untruncate] (their [Prop]-valued index lives at
       [max(Set+1, c)]) and from [RMod_Cocomplete_via_GAFT] (GAFT's index
       placement).  So a ring whose carrier sits at [Set] is excluded;
       [Int_Ring] is universe polymorphic and meets it above [Set].
     - The Sets level is [pa].  [Ab_Forget@{b pa c}] lands in
       [Sets@{c pa}], the auxiliary slot of the continuity hypothesis.
       That identification is forced by the route:
       [PreservesImageLimit_Continuous] turns [pa] into the tenth slot of
       [ContinuousFunctor], [continuous_compose] shares that slot between
       T and [Ab_Forget], and [Ab_Forget_creates_continuous] has its
       tenth slot equal to its [Sets] object universe.  With a separate
       [s] for [Ab_Forget] and [pa < s] declared, [watts_theorem_sets]'s
       body is refused, expected "Representable@{ra rt s o c}
       (Ab_Forget@{a s c} ◯ T)" against the body's
       "Representable@{<1> <2> pa o c} (Ab_Forget@{a pa c} ◯ T)"
       "(universe inconsistency: Cannot enforce pa = s because pa < s)";
       the constants therefore use [pa] for that level.
     - Strict and non-strict [eq_rect_r] bounds: [c < eq_rect_r.u0] and
       [c <= eq_rect_r.u1] on every constant built on the SAFT, from
       [continuous_Set_functor_representable] and [SAFT_wellpowered]
       (whose readbacks carry [h < eq_rect_r.u0], attributed in
       Corollaries.v's header to Adjunction/SAFT/InitialObject.v's
       [complete_pullbacks]), and [x <= eq_rect_r.u0], which is those
       constants' [t <= eq_rect_r.u0] (from #452's
       [special_initial_object_wellpowered_at], per the same header) at
       [t := x], the fifth slot of [WellPowered@{o c c o x}].
     - The witnesses.  [HomAbForget]'s intermediate [Ab] sits at RMod's
       object universe o.  The continuity proof stated for the composite
       with that [Ab] at its own [m], and [o < m] declared, is refused,
       "… (cannot unify "@padd_respects _ (@abenriched_preadditive _
       (@AbEnriched_op@{m c} Ab@{m c} Ab_AbEnriched@{m <1> c})) A
       (fobj[(RMod_Forget_Ab@{x o m c c c} R)^op] (fobj[K] x0))" and
       "@padd_respects _ (@abenriched_preadditive _ (@AbEnriched_op@{o c}
       Ab@{o c} Ab_AbEnriched@{o <1> c})) A (fobj[(RMod_Forget_Ab@{x o o
       c c c} R)^op] (fobj[K] x0))")" (<1> a universe the scratch compile
       generated); the same statement with no constraint declared is
       accepted and reads back [o = m].  The cause is [coex_adjunction],
       whose left adjoint lands in an [Ab] at RMod's object universe (its
       readback: [RMod_Forget_Ab@{u3 u2 u2 u u1 u0} R ⊣
       Coextension@{u u0 u1 u2 u3} R]).  [HomAbForget_continuous]'s
       tenth slot is x: named [k6] with [x < k6] declared the proof is
       refused, and with [k6 < x] declared it is refused too, both with
       "cannot unify "Functor.Compose_obligation_1 J (RMod R)^op Ab
       (HomAbForget R A) K" and "Functor.Compose_obligation_1 J
       (RMod R)^op Ab (CoHomAb Ab_AbEnriched A ◯ (RMod_Forget_Ab R)^op)
       K"".  So the Sets level of the text form at
       that witness is x, and [coext_representable] is stated at
       [Sets@{c x}] to meet it in [repr_unique_iso].  Likewise at the
       Exercise 3 witness, [RMod_Forget_Ab_creates_continuous] has its
       tenth slot at RMod's x, and [rmod_representable] lands in
       [Sets@{c x}]; neither shows in [watts_ex3_forget_obj]'s type.
     - Two equations appeared in drafts and are NOT forced, each measured
       by appending the draft to a copy of this whole file with the
       opposite order declared: [x = s] in a draft of [watts_ex3] (with
       a [ContinuousFunctor] hypothesis, [Ab_Forget@{b s c}] ascribed once
       and [watts_ex3_sets] elaborated a second time inside [exact]),
       which is accepted with [s < x] declared; and [x = s] in a draft of
       [coext_representable] at a separate [Sets@{c s}], accepted with
       [x < s] declared.  Both came from elaboration, not from a donor;
       the landed constants route [watts_ex3_sets] through ONE ascribed
       occurrence and name the level they need.
     - The constants added with [watt_at_forget] and section 5.
       [watt_at_forget] is at [RingObject@{c c c}] because its
       representing object [Ring_RMod R] is (the collapse
       Instance/Mod/WellPowered.v measures), and reads back
       [HomAb@{o c b} (RMod_AbEnriched@{x o c c c} R) (Ring_RMod@{c c c}
       R) ≅ RMod_Forget_Ab@{x o b c c c} R].  [ab_hom_Z_iso@{a c +}]
       lands in [Ab@{a c}] at both ends; the free group's own universes
       and the one-point set's are left to inference, reached through
       [FreeAb] and [SetsOne] without instances.  [watts_theorem_Fz]
       carries [watts_theorem]'s named universes.
     - Section 6.  [watts_theorem_via_unconditional@{c o x a pk pa +}]
       carries [watts_theorem]'s named universes but [ra rt].
       [watts_unconditional_coext] and its [_2a] instantiate
       [watts_theorem_unconditional@{c c c o x b x …}]: the ring collapsed
       by [CoextObj], and that theorem's Sets level s at x, which is
       [HomAbForget_continuous]'s tenth slot, as above.  The [Ab] of
       [HomAbForget] is ascribed at [b] in both statements; left to
       inference it was set to x, and [About] read back
       [HomAbForget@{c o x x}] with the binder's b unused.

   ** NON-VACUITY

   Exercise 3 at T := [RMod_Forget_Ab R]: [watts_ex3_forget R G U], whose
   continuity is #449's creation ([RMod_Forget_Ab_creates_continuous]),
   not an adjunction, so the witness is not circular.  Its representing
   object is ≅ [Ring_RMod R] ([watts_ex3_forget_obj], at
   [RingObject@{c c c}]): [repr_induced_iso] against
   Instance/Mod/Representable.v's [rmod_representable], along the
   identity-component iso [RMod_Forget_equiv] between [RMod_Forget R] and
   [Ab_Forget ◯ RMod_Forget_Ab R].  It inherits both [G] and [U].

   The text form at T := [HomAbForget R A], M ↦ Hom_Ab(U M, A), for any
   abelian group A: [watts_theorem_coext R A U].  Additivity is
   [HomAbForget_additive]; continuity is [HomAbForget_continuous], the
   composite of [RMod_Forget_Ab R]^op — continuous because
   [RMod_Forget_Ab R] is a LEFT adjoint, [coex_adjunction], read through
   [Opposite_Adjunction] and [right_adjoint_Continuous] — with
   [CoHomAb_continuous].  Its representing object is ≅ [CoextObj R A]
   ([watts_theorem_coext_obj]): [repr_unique_iso] against
   [coext_representable], whose components are the coextension
   adjunction's own hom bijections, read in (RMod R)^op and brought back
   by [Isomorphism_Opposite]; and ≅ [HomZL R_R A], Exercise 2(a)'s
   hom_ℤ(R, A) ([watts_theorem_coext_obj_2a], through HomTensor.v's
   [homzl_coext_iso]).  Mac Lane's C is therefore identified, up to
   isomorphism, as hom_ℤ(R, A) at this T.  It inherits [U] and nothing
   else.

   Every witness of the two theorems inherits [Untruncate], which has no
   in-tree inhabitant, so neither theorem has an unconditional instance
   in tree.  The text form's witness has an unconditional counterpart
   through Instance/Mod/Watts/Unconditional.v's theorem, in this file's
   section 6: [watts_unconditional_coext] (≅ [CoextObj R A]) and
   [watts_unconditional_coext_2a] (≅ [HomZL R_R A]).  [watt_at_forget]
   is not an instance of either theorem but of the additive upgrade both
   are built on, at the forgetful functor, and it needs nothing:
   Exercise 3's conclusion at that T, without the special adjoint
   functor theorem.

   ** AXIOMS AND MEASUREMENTS

   [Print Module Category.Instance.Mod.Watts] lists twenty-seven
   constants and no [Program] obligation (the file uses no [Program]);
   each reports "Closed under the global context" under [Print
   Assumptions] by its fully qualified name.
   FLIPS: each of the five [Defined] was turned to [Qed] alone in a copy
   of the whole file; [coext_representable] is load-bearing (its
   representing object must reduce to [CoextObj R A] for
   [watts_theorem_coext_obj] to typecheck, and, measured with that
   constant and its [_2a] removed from the flipped copy, for
   [watts_unconditional_coext] too) and the other four recompile as
   [Qed]; they are kept transparent as data, like
   Functor/Representable/Additive.v's [HomAb_additive].  [make todo] is
   unchanged by this file.

   ** NOT DELIVERED

   No unconditional covariant form: Exercise 3 is delivered only over
   [Untruncate] and a cogenerator of RMod R, which no in-tree term
   supplies at a size [cogen_prod] accepts (the unconditional
   [RMod_Cogenerator_large] is large, and Instance/Mod/Cogenerator.v's
   metatheorems show the book's ℚ/ℤ one classical).  Nothing in tree
   proves either hypothesis necessary: the SAFT route here consumes both,
   no other route to the covariant form is attempted, and [RMod R]
   well-powered at the pin without [Untruncate] is neither built nor
   refuted.  The contravariant form without [Untruncate] is
   Instance/Mod/Watts/Unconditional.v's, through GAFT with an explicit
   solution set, and section 6 consumes it.  No
   isomorphism of the free abelian group on one point with
   Instance/Ab/Free.v's [ab_int], so section 5's ℤ is [FreeAb SetsOne],
   not the integers of [Int_Ring]; and [watts_theorem_Fz] compares
   objects only, with no Ab-level isomorphism CoHomAb (F ℤ) ≅ T through
   [ab_hom_Z_iso] (that would need [CoHomAb] functorial in its object).
   The text form only at [RingObject@{c c c}].  No
   uniqueness beyond Functor/Representable.v's [repr_unique_iso].  No
   Eilenberg–Watts tensor form (a cocontinuous additive
   Mod_R → Mod_S is − ⊗_R N) and no bimodule-valued version.  No
   naturality of the representing object in T.  No [Instance] is
   registered.  The refusals quoted above were measured in scratch copies
   of this whole file, and Test/ProbeWatts454.v pins them under its own
   import list: the [eq_refl] refusal of [watts_ex3_forget]'s object as
   its N16; [watts_theorem_sets]'s body at [c < a] as N17 (peeled to
   [RModop_Cogenerator] as N18); the Sets level, at [pa < s] and at
   [s < pa], as N19 and N29; [HomAbForget_continuous]'s body with the
   witness's [Ab] at m, at [o < m] and at [m < o], as N31 and N32 (at its
   first factor as N20 and N30); and that body at the tenth slot k6, at
   [x < k6] and at [k6 < x], as N33 and N34 (the constant itself as N21
   and N22).  Its controls [p454_sets_apart_free], [p454_ex3_twice],
   [p454_hafc_body_at_o] and [p454_hafc_body_at_x] restate the accepted
   forms, and its N23 pins that the representing object is not F ℤ by
   conversion while Adjunction/GAFT.v's [GAFT], at which both sides stop
   reducing, is opaque.  It does not pin the draft of
   [coext_representable] at a separate [Sets@{c s}], a whole proof. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Functor.Representable.Additive.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Projective.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Character.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Instance.Mod.Coextension.
Require Import Category.Instance.Mod.Representable.
Require Import Category.Instance.Mod.WellPowered.
Require Import Category.Instance.Mod.Colimit.
Require Import Category.Instance.Mod.HomTensor.
Require Import Category.Instance.Mod.Cogenerator.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Corollaries.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Mod.Watts.Unconditional.

Generalizable All Variables.

(** ** 1. The forgetful functor is additive *)

Definition RMod_Forget_Ab_additive@{a c p o x b +} (R : RingObject@{a c p}) :
  @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c} (RMod_AbEnriched R)
    Ab_AbEnriched (RMod_Forget_Ab R).
Proof. constructor. intros x y f g m; simpl; reflexivity. Defined.

(** ** 2. Watts' theorem, the book's text form *)

(* SAFT at (RMod R)^op: complete because RMod R is cocomplete, cogenerated
   by R, well-powered because RMod R is co-well-powered under [U].  The
   continuity of [Ab_Forget ◯ T] is T's composed with [Ab_Forget]'s; the
   Sets level [pa] is forced (the header's UNIVERSES). *)
Definition watts_theorem_sets@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T)
    (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* The book's first step, verbatim: T itself has a left adjoint. *)
Definition watts_theorem_adjoint@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { F : Ab@{a c} ⟶ (RMod@{o x c c c} R)^op & F ⊣ T } :=
  SAFT_wellpowered T (Complete_op_of_Cocomplete (RMod_Cocomplete_via_GAFT R))
    contT (RModop_Cogenerator R) (RMod_CoWellPowered_untruncate U).

(* The theorem: T ≅ hom_R(−, A) as Ab-valued functors.  The representation
   enters ONCE, ascribed, so that no second elaboration of it adds a
   universe equation (the header's UNIVERSES). *)
Definition watts_theorem@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { A : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{a c})
      (CoHomAb (RMod_AbEnriched R) A) T } :=
  @watt_ab_repr ((RMod R)^op)
    (LocallyPropositional_op (RMod_LocallyPropositional R))
    (AbEnriched_op (RMod_AbEnriched R)) T AF
    (watts_theorem_sets T contT U
       : Representable@{ra rt pa o c} (Ab_Forget ◯ T)).

(* The representing object IS the SAFT representation's. *)
Example watts_theorem_obj@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    = @repr_obj _ _ (watts_theorem_sets T contT U
                      : Representable@{ra rt pa o c} (Ab_Forget ◯ T)) :=
  eq_refl.

(* ...and each component of the Ab-level isomorphism is the Sets-level
   representation's component, unchanged: additivity adds proofs, not
   data. *)
Example watts_theorem_to_at@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) (M : RMod@{o x c c c} R)
  (f : M ~{RMod@{o x c c c} R}~> projT1 (watts_theorem T AF contT U)) :
  cmon_map (transform[to (projT2 (watts_theorem T AF contT U))] M) f
    = transform[to (@represented _ _ (watts_theorem_sets T contT U
                      : Representable@{ra rt pa o c} (Ab_Forget ◯ T)))] M f :=
  eq_refl.

(** ** 3. Exercise 3, the covariant form *)

(* SAFT at RMod R: complete, well-powered under [U], cogenerated by [G]. *)
Definition watts_ex3_sets@{a c p o x b g pk pa ra rt +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             (RMod@{o x a p c} R) Ab@{b c} T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  Representable@{ra rt pa o c} (Ab_Forget ◯ T) :=
  continuous_Set_functor_representable (Ab_Forget ◯ T) (RMod_Complete R)
    (Continuous_PreservesImageLimit
       (continuous_compose (PreservesImageLimit_Continuous contT)
          Ab_Forget_creates_continuous))
    G (RMod_WellPowered_untruncate U).

Definition watts_ex3@{a c p o x b g pk pa ra rt +}
  {R : RingObject@{a c p}} (T : RMod@{o x a p c} R ⟶ Ab@{b c})
  (AF : @AdditiveFunctor (RMod@{o x a p c} R) Ab@{b c}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c b c pk c pa c}
             (RMod@{o x a p c} R) Ab@{b c} T)
  (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun (RMod@{o x a p c} R) Ab@{b c})
      (HomAb (RMod_AbEnriched R) A) T } :=
  watt_ab_repr (RMod_AbEnriched R) T AF
    (watts_ex3_sets T contT G U
       : Representable@{ra rt pa o c} (Ab_Forget ◯ T)).

(* Exercise 3 as the book words it: "Use Exercise 2(b)".  The premises
   [HI] and [HC] are Exercise 2(b)'s "Q/Z ... is known to be an injective
   cogenerator of Ab", taken as hypotheses (Instance/Mod/Cogenerator.v). *)
Definition watts_ex3_QZ@{r o x b pk pa ra rt +}
  {R : RingObject@{r r r}} (T : RMod@{o x r r r} R ⟶ Ab@{b r})
  (AF : @AdditiveFunctor (RMod@{o x r r r} R) Ab@{b r}
          (RMod_AbEnriched R) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o r b r pk r pa r}
             (RMod@{o x r r r} R) Ab@{b r} T)
  (HI : @Injective Ab@{o r} QZ)
  (HC : QZ_family_cogenerates)
  (U : Untruncate@{r}) :
  { A : RMod@{o x r r r} R &
    @Isomorphism (@Fun (RMod@{o x r r r} R) Ab@{b r})
      (HomAb (RMod_AbEnriched R) A) T } :=
  watts_ex3 T AF contT
    (snd (QZ_injective_cogenerator R HI HC)) U.

(* Only the cogenerating half of Exercise 2(b) is consumed: the
   cogenerator does not mention [HI]. *)
Example watts_ex3_QZ_cogenerator@{r o x +}
  {R : RingObject@{r r r}} (HI : @Injective Ab@{o r} QZ)
  (HC : QZ_family_cogenerates) :
  snd (QZ_injective_cogenerator R HI HC)
    = coext_cogenerator R (QZ_Cogenerator HC) := eq_refl.

(** ** 4. Witnesses *)

(* Exercise 3 at the forgetful functor, continuous by #449's creation. *)
Definition watts_ex3_forget@{a c p o x b g +}
  (R : RingObject@{a c p}) (G : Cogenerator@{g o c} (RMod@{o x a p c} R))
  (U : Untruncate@{c}) :
  { A : RMod@{o x a p c} R &
    @Isomorphism (@Fun (RMod@{o x a p c} R) Ab@{b c})
      (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) } :=
  watts_ex3 (RMod_Forget_Ab R) (RMod_Forget_Ab_additive R)
    (Continuous_PreservesImageLimit (RMod_Forget_Ab_creates_continuous R)) G U.

(* Instance/Mod.v builds [RMod_Forget R] directly rather than as the
   composite; the two agree up to identity components. *)
Definition RMod_Forget_equiv@{a c p o x b +} (R : RingObject@{a c p}) :
  (RMod_Forget R : RMod@{o x a p c} R ⟶ Sets@{c x})
    ≈ (@Compose _ Ab@{b c} _ Ab_Forget (RMod_Forget_Ab R)
         : RMod@{o x a p c} R ⟶ Sets@{c x}).
Proof.
  exists (fun M => iso_id).
  intros M N f m; simpl. reflexivity.
Defined.

(* The additive upgrade with NO hypothesis: [rmod_representable], R
   representing the forgetful functor to sets, carried along
   [RMod_Forget_equiv] to a representation of [Ab_Forget ◯ RMod_Forget_Ab
   R], and upgraded.  The representing object is [Ring_RMod R] by
   conversion, so the statement names it. *)
Definition watt_at_forget@{c o x b +} (R : RingObject@{c c c}) :
  @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
    (HomAb (RMod_AbEnriched R) (Ring_RMod R)) (RMod_Forget_Ab R) :=
  watt_ab_iso (RMod_AbEnriched R) (RMod_Forget_Ab R)
    (RMod_Forget_Ab_additive R)
    (Representable_transport (equiv_iso (RMod_Forget_equiv R))
       (rmod_representable R)).

(* The representing object is R itself, up to isomorphism: two
   representations of isomorphic functors. *)
Definition watts_ex3_forget_obj@{c o x b g +}
  (R : RingObject@{c c c}) (G : Cogenerator@{g o c} (RMod@{o x c c c} R))
  (U : Untruncate@{c}) :
  projT1 (watts_ex3_forget R G U
           : { A : RMod@{o x c c c} R &
               @Isomorphism (@Fun (RMod@{o x c c c} R) Ab@{b c})
                 (HomAb (RMod_AbEnriched R) A) (RMod_Forget_Ab R) })
    ≅[RMod@{o x c c c} R] Ring_RMod R :=
  repr_induced_iso (rmod_representable R)
    (watts_ex3_sets (RMod_Forget_Ab R)
       (Continuous_PreservesImageLimit
          (RMod_Forget_Ab_creates_continuous R)) G U)
    (equiv_iso (RMod_Forget_equiv R)).

(* The text form's witness: M ↦ Hom_Ab(U M, A), contravariant in M.  The
   intermediate [Ab] is at RMod's object universe, where
   [coex_adjunction]'s left adjoint lands. *)
Definition HomAbForget@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) : (RMod@{o x c c c} R)^op ⟶ Ab@{b c} :=
  @CoHomAb Ab@{o c} _ Ab_AbEnriched A ◯ Opposite_Functor (RMod_Forget_Ab R).

Definition HomAbForget_additive@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{b c}
    (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched
    (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}).
Proof.
  constructor. intros x y f g h m; simpl.
  apply (cmon_map_plus h).
Defined.

(* [RMod_Forget_Ab R] is a left adjoint, so its opposite is a right
   adjoint and continuous; [CoHomAb A] is continuous by
   Functor/Representable/Additive.v's [CoHomAb_continuous]. *)
Definition HomAbForget_continuous@{c o x b +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  ContinuousFunctor (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) :=
  continuous_compose
    (right_adjoint_Continuous (Opposite_Adjunction _ _ (coex_adjunction R)))
    (CoHomAb_continuous Ab_AbEnriched A).

Definition watts_theorem_coext@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  { A' : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
      (CoHomAb (RMod_AbEnriched R) A')
      (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) } :=
  watts_theorem (HomAbForget R A) (HomAbForget_additive R A)
    (Continuous_PreservesImageLimit (HomAbForget_continuous R A)) U.

(* The coextension adjunction represents the witness directly: its hom
   bijection Hom_R(M, CoextObj R A) ≅ Hom_Ab(U M, A), natural in M.  The
   naturality square, evaluated at a ∈ N and r ∈ R, is R-linearity of f
   and g together with 1 · r ≈ r. *)
Definition coext_representable@{c o x b ra rt +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  Representable@{ra rt x o c}
    (@Compose _ Ab@{b c} _ Ab_Forget
       (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})).
Proof.
  unshelve econstructor.
  - exact (CoextObj R A).
  - apply equiv_iso.
    exists (fun M => iso_sym (@adj _ _ _ _ (coex_adjunction R) M A)).
    intros M N f g; simpl.
    intros a r.
    pose proof (rm_map_smul f r a) as H1.
    assert (H2 : cmon_map (rm_hom g) (cmon_map (rm_hom f) (rm_smul N r a))
                 ≈ cmon_map (rm_hom g) (rm_smul M r (cmon_map (rm_hom f) a)))
      by (apply proper_morphism; exact H1).
    specialize (H2 (rig_one (ring_rig R))).
    pose proof (rm_map_smul g r (cmon_map (rm_hom f) a) (rig_one (ring_rig R)))
      as H3.
    simpl in H2, H3.
    symmetry.
    etransitivity; [exact H2|].
    etransitivity; [exact H3|].
    apply proper_morphism. apply rig_mul_one_l.
Defined.

(* SAFT's representing object at the witness is the coextension, up to
   isomorphism in RMod R... *)
Definition watts_theorem_coext_obj@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  projT1 (watts_theorem_coext R A U
           : { A' : RMod@{o x c c c} R &
               @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
                 (CoHomAb (RMod_AbEnriched R) A')
                 (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) })
    ≅[RMod@{o x c c c} R] CoextObj R A :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (repr_unique_iso (coext_representable R A)
       (watts_theorem_sets (HomAbForget R A)
          (Continuous_PreservesImageLimit (HomAbForget_continuous R A)) U)).

(* ...and so Exercise 2(a)'s hom_ℤ(R, A), the module [HomZL R_R A]. *)
Definition watts_theorem_coext_obj_2a@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) (U : Untruncate@{c}) :
  projT1 (watts_theorem_coext R A U
           : { A' : RMod@{o x c c c} R &
               @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{b c})
                 (CoHomAb (RMod_AbEnriched R) A')
                 (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c}) })
    ≅[RMod@{o x c c c} R] HomZL (Ring_RMod (Ring_op R)) A :=
  iso_compose (iso_sym (homzl_coext_iso A)) (watts_theorem_coext_obj R A U).

(** ** 5. Mac Lane's last step: the representing object is F ℤ *)

(* ℤ is read as the free abelian group on one point, [FreeAb SetsOne]
   (Instance/Ab/Free.v).  [Ab_Forget] and [Ab_Forget ◯ Id[Ab]] agree up to
   identity components. *)
Definition Ab_Forget_Id_equiv@{a c x +} :
  (Ab_Forget : Ab@{a c} ⟶ Sets@{c x})
    ≈ (@Compose _ Ab@{a c} _ Ab_Forget Id[Ab@{a c}]
         : Ab@{a c} ⟶ Sets@{c x}).
Proof.
  exists (fun M => iso_id).
  intros M N f m; simpl. reflexivity.
Defined.

(* Ab(ℤ, X) ≅ X, natural in X, as an isomorphism of Ab-valued functors:
   the additive upgrade at T := Id[Ab], fed the representation of
   [Ab_Forget] by the free group on one point that
   Adjunction/Representability/Sets.v reads off [free_ab_adjunction]. *)
Definition ab_hom_Z_iso@{a c +} :
  @Isomorphism (@Fun Ab@{a c} Ab@{a c})
    (HomAb Ab_AbEnriched (FreeAb SetsOne)) Id[Ab@{a c}] :=
  watt_ab_iso Ab_AbEnriched Id[Ab] Id_AdditiveFunctor
    (Representable_transport (equiv_iso Ab_Forget_Id_equiv)
       (representable_of_left_adjoint Ab_Forget free_ab_adjunction)).

(* C = F ℤ, up to isomorphism in RMod R, F being the left adjoint of
   [watts_theorem_adjoint]: FreeAb ⊣ Ab_Forget composed with F ⊣ T
   represents [Ab_Forget ◯ T] by F (FreeAb SetsOne), and two
   representations of one functor have isomorphic representing objects. *)
Definition watts_theorem_Fz@{c o x a pk pa ra rt +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  projT1 (watts_theorem T AF contT U)
    ≅[RMod@{o x c c c} R]
  fobj[projT1 (watts_theorem_adjoint T contT U)] (FreeAb SetsOne) :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (@repr_unique_iso ((RMod R)^op) (Ab_Forget ◯ T)
       (representable_of_left_adjoint (Ab_Forget ◯ T)
          (Adjunction_Compose free_ab_adjunction
             (projT2 (watts_theorem_adjoint T contT U))))
       (watts_theorem_sets T contT U
          : Representable@{ra rt pa o c} (Ab_Forget ◯ T))).

(** ** 6. What the unconditional theorem subsumes *)

(* [watts_theorem]'s statement, derived from Instance/Mod/Watts/
   Unconditional.v's [watts_theorem_unconditional] without the special
   adjoint functor theorem: the continuity hypothesis converted by
   [PreservesImageLimit_Continuous], and [U] carried but not consumed. *)
Definition watts_theorem_via_unconditional@{c o x a pk pa +}
  {R : RingObject@{c c c}} (T : (RMod@{o x c c c} R)^op ⟶ Ab@{a c})
  (AF : @AdditiveFunctor ((RMod@{o x c c c} R)^op) Ab@{a c}
          (AbEnriched_op (RMod_AbEnriched R)) Ab_AbEnriched T)
  (contT : @PreservesImageLimit@{o c a c pk c pa c}
             ((RMod@{o x c c c} R)^op) Ab@{a c} T)
  (U : Untruncate@{c}) :
  { A : RMod@{o x c c c} R &
    @Isomorphism (@Fun ((RMod@{o x c c c} R)^op) Ab@{a c})
      (CoHomAb (RMod_AbEnriched R) A) T } :=
  watts_theorem_unconditional T AF (PreservesImageLimit_Continuous contT).

(* The text form's witness M ↦ Hom_Ab(U M, A) with NO [Untruncate]: the
   module the unconditional theorem returns is the coextension, up to
   isomorphism in RMod R ([repr_unique_iso] against
   [coext_representable]). *)
Definition watts_unconditional_coext@{c o x b +} (R : RingObject@{c c c})
  (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] CoextObj R A :=
  @Isomorphism_Opposite ((RMod R)^op) _ _
    (repr_unique_iso (coext_representable R A)
       (RModop_continuous_representable _
          (continuous_compose (HomAbForget_continuous R A)
             Ab_Forget_creates_continuous))).

(* ...and so Exercise 2(a)'s hom_ℤ(R, A), the module [HomZL R_R A]. *)
Definition watts_unconditional_coext_2a@{c o x b +}
  (R : RingObject@{c c c}) (A : AbObject@{c c c}) :
  projT1 (watts_theorem_unconditional
            (HomAbForget R A : (RMod@{o x c c c} R)^op ⟶ Ab@{b c})
            (HomAbForget_additive R A) (HomAbForget_continuous R A))
    ≅[RMod@{o x c c c} R] HomZL (Ring_RMod (Ring_op R)) A :=
  iso_compose (iso_sym (homzl_coext_iso A)) (watts_unconditional_coext R A).
