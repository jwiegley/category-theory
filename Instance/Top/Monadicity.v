Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Identity.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.

Generalizable All Variables.

(** * The discrete-space adjunction induces the identity monad, and is not
      monadic *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §VI.3, book p. 144 (PDF p. 153), read from the page image, right
     after the remark, which the page takes over from p. 143, that for
     "other authors (Barr-Wells [1985]), 'triplable' means only that K be
     an equivalence of categories": "However, here is an easy example when K
     is not an isomorphism, and not even an equivalence.  The forgetful
     functor G : Top → Set has a left adjoint D which assigns to each set
     X the discrete topological space (all subsets open in X), for the
     identity arrow η_X : X → GDX is trivially universal from the object
     X to the functor G.  This adjunction ⟨D, G, η, …⟩ : Set ⇀ Top
     defines on Set the monad I = ⟨I, 1, 1⟩ which is the identity
     (identity functor, identity as unit and as multiplication).  The
     I-algebras in Set are just the sets, so the comparison functor
     Top → Top^I = Set is in this case the given forgetful functor G"
     (catalog id maclane:VI.3:remark1).
   Awodey, "Category Theory", Carnegie Mellon pre-print of the 1st ed.
     (September 2005), §10.3, printed p. 278 (PDF p. 287), read from the
     page image, runs the same argument for posets: "An example of a
     right adjoint that is not monadic is the forgetful functor from
     posets, U : Pos → Sets" (awodey:10.3:example-pos-not-monadic);
     that example is Instance/Pos/Monadicity.v's.
   nLab: https://ncatlab.org/nlab/show/monadic+functor
   nLab: https://ncatlab.org/nlab/show/discrete+space

   BACKGROUND.  Every adjunction F ⊣ U induces a monad T = UF, and the
   comparison functor K into the Eilenberg-Moore category of T measures how
   far the right adjoint U is from forgetting algebraic structure; U is
   monadic when K is an equivalence (Monad/Comparison.v's [Monadic], the
   Barr-Wells reading quoted above); Mac Lane's "not an isomorphism, and
   not even an equivalence" covers the stronger reading too.  His example
   is the extreme case.  A set carries a unique discrete topology, so the
   unit is the identity and the induced monad is the identity monad: it
   records no structure at all, its algebras are the sets, and K can be no
   more than the forgetful functor itself.  That functor forgets a
   topology, which is not algebraic structure, and it is not full.  An
   isomorphic monad, with functor Id ◯ Id, is induced by Id ⊣ Id, whose
   right adjoint IS monadic (Monad/Monadicity/Examples.v's
   [identity_monadic]; Monad/Identity.v's header), so a monad does not
   determine whether the right adjoint that induced it is monadic.

   THE READING IMPLEMENTED.  The page prints the target of the
   comparison as "Top^I = Set".  The I-algebras live in Set, so K lands
   in the category of I-algebras in Set, and that is the target taken
   here: [EilenbergMoore] of the induced monad on [Sets].  "= Set" is
   read as an equivalence between that category and [Sets]: an algebra
   keeps its structure map, which is ≈ id and need not be id.  For
   Monad/Eilenberg/Moore/Limit/Examples.v's identity monad [IdSM] on
   [Sets], #467's [A_id_ne_A_true] exhibits two different algebras on one
   carrier; the same is not restated here for [PDiscMonad].

   WHY [PTopCat].  Over the tree's Type-valued [Top] the adjunction is
   not an [Adjunction] record at any universe assignment
   (Instance/Top/Forgetful.v's header; Test/ProbeUniversalArrows312.v
   pins it), so its induced monad and comparison functor cannot be
   formed.  By the maintainer's decision of 2026-09-24 such Top issues
   are built on Instance/Top/Prop.v's Prop-valued [PTopCat], where
   Instance/Top/Complete.v's [PDisc_PForget : PDisc ⊣ PForget] is one
   (#458).  Instance/Top/Monadicity/TypeValued.v states what remains
   formable over [Top]: that its underlying-set functor is not monadic.

   WHAT IS HERE.
     - The induced monad: [PDiscT] is [PForget ◯ PDisc] and [PDiscMonad]
       is Monad/Comparison.v's [Adjunction_Induced_Monad PDisc_PForget].
       Its functor is the identity on objects ([PDiscT_fobj]) and on
       arrows ([PDiscT_fmap]); its unit and multiplication are [id]
       ([PDiscMonad_ret], [PDiscMonad_join]); as functions, its four data
       fields are those of [IdMonad Sets] ([PDiscT_fields],
       [PDiscMonad_fields]); the unit of the adjunction
       is the identity arrow, Mac Lane's η_X ([PDisc_PForget_unit]), and
       the counit at a space is the identity on its points
       ([PDisc_PForget_counit]).
     - "The monad I = ⟨I, 1, 1⟩ which is the identity", as an isomorphism
       [disc_id_iso] in #468's category of monads [Monads Sets]
       (Monad/Morphism.v) between (PDiscT; PDiscMonad) and
       Monad/Identity.v's (Id[Sets]; IdMonad Sets).  Its two morphisms of
       monads, [disc_id_hom] and [id_disc_hom], have the identity as every
       component ([disc_id_hom_component], [id_disc_hom_component]).
     - "The comparison functor is the forgetful functor G": [PDiscK] is
       [EM_Comparison PDisc_PForget].  After the forgetful functor of the
       algebras it is [PForget] on objects and on arrows
       ([PDiscK_forget_obj], [PDiscK_forget_map]), in Theory/Functor.v's
       [Functor_StrictEq_Setoid] with every object equation [eq_refl]
       ([PDiscK_forget_strict]), and at Cat's ≈ ([PDiscK_forget], which is
       Monad/Comparison.v's [EM_Comparison_Forget] at this adjunction).
       The structure map of K X is the identity setoid morphism
       ([PDiscK_alg]).
     - "Top^I = Set": [EM_PDisc_equivalence], the forgetful functor of the
       algebras of [PDiscMonad] is an equivalence with quasi-inverse
       [EM_Free], because every structure map is ≈ id
       ([PDiscMonad_alg_id]); and [PDiscK_free]: K ≈ EM_Free ◯ PForget,
       with identity arrows underneath, so K is G followed by that
       equivalence.  For the identity monad itself, Monad/Identity.v's
       [IdMonad_EM_equivalence] at [Sets]; and [PDiscKI], K followed by
       #468's θ* of [id_disc_hom] (Monad/Morphism/Algebra.v's [mh_EM]), is
       the comparison into the algebras of [IdMonad Sets]: the structure
       map of each image is the identity function ([PDiscKI_alg]) and
       after the forgetful functor it is [PForget] on objects and arrows
       ([PDiscKI_forget_obj], [PDiscKI_forget_map]).  The four constants
       [EM_PDisc_counit], [EM_PDisc_unit_iso], [EM_PDisc_unit] and
       [EM_PDisc_equivalence] repeat Monad/Identity.v's [IdMonad_EM_counit],
       [IdMonad_EM_unit_iso], [IdMonad_EM_unit] and
       [IdMonad_EM_equivalence] line for line at [PDiscMonad]: those are
       stated for [IdMonad], and [PDiscMonad] is not [IdMonad Sets] at
       [eq_refl], neither as a functor (R1) nor as a monad (R3).  Carrying
       [IdMonad_EM_equivalence] across [disc_id_iso] instead, by θ*
       ([mh_EM], [mh_EM_id], [mh_EM_compose]) and Theory/Equivalence/
       Bundled.v's [EquivalenceOfCategories_Compose], is the other route;
       it is not taken.
     - "Not an isomorphism, and not even an equivalence."  Mac Lane gives
       no argument; this is the file's.  [pbool_to_indisc], the identity
       of [bool] from the discrete space [PBool] (Instance/Top/Prop.v) to
       the indiscrete [PTwoIndisc] (Instance/Top/Cocomplete.v), is
       continuous, and no continuous map back is the identity on points
       ([no_pindisc_to_bool]): the preimage of the open {true} would be an
       open of the indiscrete space holding at true and not at false.  So
       [PForget] is not full ([PForget_not_Full]); neither is K, the
       identity of [bool] being an algebra map K PTwoIndisc → K PBool
       ([PDiscK_not_Full]), and neither is [PDiscKI], the comparison into
       the algebras of [IdMonad Sets] itself ([PDiscKI_not_Full],
       [PDiscKI_not_Equivalence]); K is not an equivalence
       ([PDiscK_not_Equivalence], by Theory/Equivalence/FullFaithful.v's
       [Equivalence_Full]) and not an isomorphism in [Cat]
       ([PDiscK_not_Cat_iso]; a [Cat]-isomorphism repacks as an
       equivalence, as in Theory/Equivalence.v's
       [Cat_Iso_to_Equivalence]).
     - [PForget_not_Monadic]: no adjunction at all makes [PForget]
       monadic, not only this one.  The proof is by conservativity: an
       equivalence K is full, and the forgetful functor of any
       Eilenberg-Moore category reflects isomorphisms
       (Monad/Monadicity/BeckObjects.v's [em_forget_reflects_isos]), so K
       of [pbool_to_indisc], an isomorphism once forgotten, has an inverse
       algebra map, which fullness brings back to a continuous map that is
       the identity on points.  [PForget_not_ReflectsIsos] refutes
       conservativity of [PForget] on its own, hypothesis 3 of
       Monad/Monadicity/Crude.v's crude monadicity theorem:
       [pbool_to_indisc] goes to an isomorphism of [Sets] and is not one.
       The adjunction part of the premise is inhabited ([PDisc_PForget]),
       so what is refuted is the equivalence.  Before #469 the tree held no
       negation of [Monadic] (a grep of the .v files for [Monadic] within
       two lines of False, ¬ or Empty); #469 adds the first four, by the
       same grep: [PForget_not_Monadic] here,
       Instance/Top/Monadicity/TypeValued.v's [Top_Forget_not_Monadic],
       and Instance/Pos/Monadicity.v's [Pos_Forget_not_Monadic] and
       [PosPForget_not_Monadic].

   THE ISSUE'S PREMISES, dated.  Issue #469 was filed on 2026-07-23.  Its
   "there is no category Top and no discrete-topology functor" was
   accurate when filed, stale since PR #1054 (merged 2026-08-12, the
   Type-valued [Top]) and PR #1088 (merged 2026-08-14, [Top_Discrete]
   with the transposition [discrete_adj]); [PTopCat] is PR #1331's
   (merged 2026-09-25) and [PDisc_PForget] PR #1332's (merged
   2026-09-25).  Its "the identity monad appears only via the identity
   adjunction" was not accurate when filed: Monad/Strong.v's [Id_Monad]
   dates from 2026-06-18.  Its "(needs the category of posets from
   #641)" has been met since PR #1076 (merged 2026-08-13).

   STRENGTHS.  By [eq_refl]: [PDiscT_fobj], [PDiscT_fmap],
   [PDiscT_fields], [PDisc_PForget_unit], [PDisc_PForget_counit],
   [PDiscMonad_ret], [PDiscMonad_join], [PDiscMonad_fields],
   [disc_id_hom_component], [id_disc_hom_component], [PDiscK_forget_obj],
   [PDiscK_forget_map], [PDiscK_alg], the object equations of
   [PDiscK_forget_strict], [PDiscKI_forget_obj], [PDiscKI_forget_map] and
   [PDiscKI_alg].  [PDiscT_fields] and [PDiscMonad_fields] read the
   book's "identity functor, identity as unit and as multiplication" as
   equations between the four data fields and those of [IdMonad Sets].
   Up to ≈: [disc_id_iso]'s inverse laws, [PDiscK_forget],
   [PDiscMonad_alg_id], [EM_PDisc_equivalence] and [PDiscK_free].

   Refused, each read in a copy of the whole of Test/ProbeMonadicity469.v
   with that one command unguarded, and pinned there with its controls,
   all by conversion ("cannot unify"): the Leibniz equation
   PDiscT = Id[Sets] (R1), and its three proof fields [fmap_respects],
   [fmap_id] and [fmap_comp] one by one (R1a to R1c), the fields [fobj]
   and [fmap] converting (C1, C2); the Leibniz form of the book's "is the
   given forgetful functor G", EM_Forget ◯ PDiscK = PForget (R2), with
   its three proof fields (R2a to R2c) and the two data fields converting
   (C3, C4); the equality of the two monads as objects of [Monads Sets]
   (R3); K against EM_Free ◯ PForget on objects (R14), whose carriers and
   structure maps agree (C39), so [PDiscK_free] is ≈ and no more; and the
   structure map of an image of [PDiscKI] as a setoid morphism (R15), so
   [PDiscKI_alg] is pointwise and no more, while [PDiscK_alg] holds of
   the setoid morphism itself.
   CORRECTION (#1347): R15 now holds at [eq_refl], since Instance/Sets.v
   gives its identity's and composite's properness fields as terms; it is
   a control of the probe, and that structure map IS [setoid_morphism_id]
   as a setoid morphism, though [PDiscKI_alg] still states the pointwise
   form.  The other refusals above stand.

   CAUSES.  The eleven refusals R1 to R3 (with R1a to R1c and R2a to R2c), R14
   and R15 stand, and their controls are accepted, in a copy of this file's
   dependency closure with [Transparent Obligations] set and every [Qed]
   turned into [Defined], obligations included (checked by [About] on them),
   but for four files.  In Instance/Sets.v only the two proofs that occur in
   the refused terms were made transparent, the hom setoid's equivalence and
   [setoid_morphism_compose_respects], the second with a proof free of
   [rewrite], since turning its own [Qed] into [Defined] is refused ("Universe
   ... is unbound"). Instance/Discrete/Reconstruct.v (the same refusal),
   Structure/Limit/Preservation.v and Structure/Cartesian/Closed.v (whose
   proofs stop once the files below them are transparent) keep their [Qed]s;
   none defines a constant in the refused terms.  No flip of the tree reaches
   the standard library, and there the normal forms of the refused proof
   fields (R1a, R1b, R2a and R2b, read by [Eval cbv] in that copy) are headed
   by its opaque [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1],
   which the [rewrite] inside [Compose]'s obligations leaves; so is the unit
   law [t_id] of the algebra K X behind R14.  Unfolded by hand, that
   obligation's body is the variable setoid's transitivity applied to X x and
   a reflexivity, and the term is refused against X x (R13), while at the
   Leibniz setoid of [bool] the same term converts (C36). So R1 to R3 with
   their fields, and R14, are STRUCTURAL past the standard library, by the
   hand-unfolded control: the proof fields are different proofs of a
   [Type]-valued ≈, [Compose]'s built from those of its two factors, stuck on
   a projection of variable data.  R15 is STDLIB OPACITY: the properness field
   of the refused structure map normalizes to the standard library's opaque
   [Reflexive_partial_app_morphism], [proper_proper_proxy] and
   [CMorphisms.compose_proper_obligation_1] applied around
   [subrelation_id_proper] twice, where that of [setoid_morphism_id] is
   [subrelation_id_proper] alone; it is the kind of
   Test/ProbeMonadMorphism468.v's R12, which holds at [eq_refl] once
   Instance/Sets.v's properness fields are given as terms, a step argued here
   from the terms and not measured.
   CORRECTION (#1347): the step is now taken and measured: R15 holds at
   [eq_refl], so its classification, STDLIB OPACITY, was right.  The copy
   above predates #1347; R15 stood there because Instance/Sets.v's two
   fields were still those of instance resolution.

   Eleven proofs end [Defined] (counted by token).  Eight are
   load-bearing, measured by closing each alone [Qed] in a copy of this
   file preceded by Monad/Identity.v: [disc_to_id] and [id_to_disc]
   ([disc_id_hom] and [id_disc_hom] are then refused), [disc_id_hom] and
   [id_disc_hom] (their [_component] readbacks), [EM_PDisc_unit_iso]
   ([EM_PDisc_unit]) and [PDiscK_free_iso] ([PDiscK_free]); and, for the
   probe's controls only, [disc_id_iso] (C17) and [PDiscK_forget_strict]
   (C20).  [EM_PDisc_counit], [EM_PDisc_unit] and [PDiscK_free] are
   [Defined] by the data convention only: closed [Qed], nothing here or
   in the probe is refused.

   UNIVERSES, read off [About]; [o] the points and homs of
   [PTopCat@{o so}], [so] its objects; stdlib caps (compose, ID,
   prod_rect, projections, Logic_lemmas.equality, Projections, and
   eq_ind, whose first carrier is the [rewrite] in [no_pindisc_to_bool])
   left out.  [Set] occurs only as [Set < so], implied by [o < so], and no
   block carries an equation.
     - [PDiscT@{o so s}]: o < s is [Compose]'s own strict bound (hom level
       below its auxiliary level) at [PForget ◯ PDisc].  The level is named
       [s] and is the same [s] as the Eilenberg-Moore level below:
       [EM_Comparison] identifies the two.
     - [PDiscMonad@{o so s u u0}] and the monad constants, among them
       [PDiscMonad_fields]: o < u is [PDisc_PForget@{o so u u0}]'s.
     - [disc_id_iso@{o so s u u0 m1 m2}]: [Monads@{so o m1 m2}]'s bounds.
     - [PDiscK@{o so s u u0 e}] and the constants over the algebras,
       [PDiscK_alg], [PDiscKI_not_Full] and [PDiscKI_not_Equivalence]
       among them:
       so <= e, the objects of [Sets] below those of
       [EilenbergMoore@{e so s o}].  [PDiscK_forget_strict] adds [a] and
       [b], the levels of [Functor_StrictEq_Setoid] (o < b its own strict
       bound), with that setoid's transport caps (Logic.transport,
       Logic.transport_r, eq_rect, eq_rect_r and eq_sym_involutive, in
       its block alone).
     - [PDiscK_not_Cat_iso@{o so s u u0 c}] is stated at e := so, the one
       object level [Cat] allows for both ends; c is the object level of
       [Cat] itself, whence so < c.
     - [PForget_not_Monadic@{o so m m0 m1 m3 m6}] states [Monadic@{m m0
       m1 so m3 o so m6}] and carries exactly [Monadic]'s own block there
       with o < so from [PForget]: the refutation holds at every value of
       [Monadic]'s five levels that [PForget@{o so}] leaves free.
     - The witnesses [pbool_to_indisc], [no_pindisc_to_bool],
       [PForget_not_Full] and [PForget_not_ReflectsIsos]: [@{o so}], o < so.

   NOT DELIVERED.  Anything over the Type-valued [Top] but the negation of
   monadicity (Instance/Top/Monadicity/TypeValued.v).  The Leibniz forms
   above (refused).  K is shown not to be an isomorphism in [Cat], whose
   isomorphisms are the equivalences; an isomorphism in
   Instance/StrictCat.v is not considered.  Whether [PForget] meets the
   other hypotheses of the crude theorem, or creates the coequalizers of
   Monad/Monadicity/Beck.v's precise form, is not examined. *)

(** ** The induced monad *)

(* [s] is the strict level of [Compose] in [PForget ◯ PDisc]; it is the
   same [s] as the Eilenberg-Moore level below, which [EM_Comparison]
   identifies with it. *)
Definition PDiscT@{o so s | o < so, o < s +} :
  Sets@{o so} ⟶ Sets@{o so} :=
  PForget@{o so} ◯ PDisc@{o so}.

Definition PDiscMonad@{o so s u u0 | o < so, o < s, o < u +} :
  @Monad Sets@{o so} PDiscT@{o so s} :=
  @Adjunction_Induced_Monad _ _ _ _ PDisc_PForget@{o so u u0}.

Example PDiscT_fobj@{o so s | o < so, o < s +} (x : Sets@{o so}) :
  fobj[PDiscT@{o so s}] x = x := eq_refl.

Example PDiscT_fmap@{o so s | o < so, o < s +} (x y : Sets@{o so})
  (f : x ~> y) : fmap[PDiscT@{o so s}] f = f := eq_refl.

Example PDisc_PForget_unit@{o so u u0 | o < so, o < u +}
  (x : Sets@{o so}) :
  @unit _ _ _ _ PDisc_PForget@{o so u u0} x = id := eq_refl.

Example PDisc_PForget_counit@{o so u u0 | o < so, o < u +}
  (X : PTopCat@{o so}) :
  pmap (@counit _ _ _ _ PDisc_PForget@{o so u u0} X) = setoid_morphism_id
  := eq_refl.

Example PDiscMonad_ret@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) : @ret _ _ PDiscMonad@{o so s u u0} x = id := eq_refl.

Example PDiscMonad_join@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) : @join _ _ PDiscMonad@{o so s u u0} x = id := eq_refl.

(* The data fields of the functor and of the monad, as functions: I = ⟨I,
   1, 1⟩ on the nose. *)
Example PDiscT_fields@{o so s | o < so, o < s +} :
  (@fobj _ _ PDiscT@{o so s}, @fmap _ _ PDiscT@{o so s})
    = (@fobj _ _ Id[Sets@{o so}], @fmap _ _ Id[Sets@{o so}]) := eq_refl.

Example PDiscMonad_fields@{o so s u u0 | o < so, o < s, o < u +} :
  (@ret _ _ PDiscMonad@{o so s u u0}, @join _ _ PDiscMonad@{o so s u u0})
    = (@ret _ _ (IdMonad@{so o} Sets@{o so}),
       @join _ _ (IdMonad@{so o} Sets@{o so})) := eq_refl.

(** ** The isomorphism with the identity monad, in [Monads Sets] *)

Definition disc_to_id@{o so s | o < so, o < s +} :
  PDiscT@{o so s} ⟹ Id[Sets@{o so}].
Proof.
  unshelve refine (Build_Transform' (F:=PDiscT@{o so s})
                     (G:=Id[Sets@{o so}]) (fun x => id) _).
  intros x y f z; simpl. reflexivity.
Defined.

Definition id_to_disc@{o so s | o < so, o < s +} :
  Id[Sets@{o so}] ⟹ PDiscT@{o so s}.
Proof.
  unshelve refine (Build_Transform' (F:=Id[Sets@{o so}])
                     (G:=PDiscT@{o so s}) (fun x => id) _).
  intros x y f z; simpl. reflexivity.
Defined.

Definition disc_id_hom@{o so s u u0 | o < so, o < s, o < u +} :
  MonadHom@{so o} PDiscMonad@{o so s u u0} (IdMonad@{so o} Sets@{o so}).
Proof.
  unshelve refine {| mh_transform := disc_to_id@{o so s} |};
    intros x z; simpl; reflexivity.
Defined.

Definition id_disc_hom@{o so s u u0 | o < so, o < s, o < u +} :
  MonadHom@{so o} (IdMonad@{so o} Sets@{o so}) PDiscMonad@{o so s u u0}.
Proof.
  unshelve refine {| mh_transform := id_to_disc@{o so s} |};
    intros x z; simpl; reflexivity.
Defined.

Example disc_id_hom_component@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  transform[mh_transform disc_id_hom@{o so s u u0}] x = id := eq_refl.

Example id_disc_hom_component@{o so s u u0 | o < so, o < s, o < u +}
  (x : Sets@{o so}) :
  transform[mh_transform id_disc_hom@{o so s u u0}] x = id := eq_refl.

Definition disc_id_iso@{o so s u u0 m1 m2 |
  o < so, o < s, o < u, so <= m1, o <= m1, so <= m2, o <= m2 +} :
  @Isomorphism (Monads@{so o m1 m2} Sets@{o so})
    (existT _ PDiscT@{o so s} PDiscMonad@{o so s u u0})
    (existT _ Id[Sets@{o so}] (IdMonad@{so o} Sets@{o so})).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{so o m1 m2} Sets@{o so})
                     (existT _ PDiscT@{o so s} PDiscMonad@{o so s u u0})
                     (existT _ Id[Sets@{o so}] (IdMonad@{so o} Sets@{o so}))
                     disc_id_hom@{o so s u u0} id_disc_hom@{o so s u u0}
                     _ _);
    intros x z; simpl; reflexivity.
Defined.

(** ** The comparison functor is the forgetful functor *)

Definition PDiscK@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PTopCat@{o so} ⟶
    @EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
      PDiscMonad@{o so s u u0} :=
  EM_Comparison PDisc_PForget@{o so u u0}.

Example PDiscK_forget_obj@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  fobj[EM_Forget _ ◯ PDiscK@{o so s u u0 e}] X = fobj[PForget@{o so}] X
  := eq_refl.

Example PDiscK_forget_map@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X Y : PTopCat@{o so}) (f : X ~> Y) :
  fmap[EM_Forget _ ◯ PDiscK@{o so s u u0 e}] f = fmap[PForget@{o so}] f
  := eq_refl.

(* The structure map of K X is the identity setoid morphism itself. *)
Example PDiscK_alg@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) :
  t_alg[`2 (fobj[PDiscK@{o so s u u0 e}] X)] = setoid_morphism_id
  := eq_refl.

Definition PDiscK_forget_strict@{o so s u u0 e a b |
  o < so, o < s, o < u, so <= e, o < b, so <= a, o <= a +} :
  @equiv _ (@Functor_StrictEq_Setoid@{a a so so b o} PTopCat@{o so}
              Sets@{o so})
    (EM_Forget _ ◯ PDiscK@{o so s u u0 e}) PForget@{o so}.
Proof.
  exists (fun X => eq_refl).
  intros X Y f. reflexivity.
Defined.

Definition PDiscK_forget@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  EM_Forget _ ◯ PDiscK@{o so s u u0 e} ≈ PForget@{o so} :=
  EM_Comparison_Forget PDisc_PForget@{o so u u0}.

(** ** Set^I = Set *)

Lemma PDiscMonad_alg_id@{o so s u u0 | o < so, o < s, o < u +}
  (a : Sets@{o so})
  (ν : @TAlgebra Sets@{o so} PDiscT@{o so s} PDiscMonad@{o so s u u0} a)
  (x : a) : t_alg[ν] x ≈ x.
Proof. exact (@t_id _ _ _ _ ν x). Qed.

Definition EM_PDisc_counit@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s} PDiscMonad@{o so s u u0}
    ◯ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0}
    ≈ Id[Sets@{o so}].
Proof.
  exists (fun x => iso_id).
  intros x y f z; simpl. reflexivity.
Defined.

Definition EM_PDisc_unit_iso@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +}
  (X : @EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
         PDiscMonad@{o so s u u0}) :
  @Isomorphism (@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
                  PDiscMonad@{o so s u u0})
    X (fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
              PDiscMonad@{o so s u u0}
             ◯ @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
                 PDiscMonad@{o so s u u0}] X).
Proof.
  unshelve econstructor.
  - unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                       PDiscMonad@{o so s u u0} _ _ _ _ id _).
    intro x; simpl. exact (PDiscMonad_alg_id _ (`2 X) x).
  - unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                       PDiscMonad@{o so s u u0} _ _ _ _ id _).
    intro x; simpl. exact (symmetry (PDiscMonad_alg_id _ (`2 X) x)).
  - intro x; simpl. reflexivity.
  - intro x; simpl. reflexivity.
Defined.

Definition EM_PDisc_unit@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Id[@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
       PDiscMonad@{o so s u u0}]
    ≈ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0}
        ◯ @EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
            PDiscMonad@{o so s u u0}.
Proof.
  exists EM_PDisc_unit_iso.
  intros X Y f x; simpl. reflexivity.
Defined.

Definition EM_PDisc_equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories
    (@EM_Forget@{so o s e} Sets@{o so} PDiscT@{o so s}
       PDiscMonad@{o so s u u0}) :=
  @Build_EquivalenceOfCategories _ _ _ _
    EM_PDisc_counit@{o so s u u0 e} EM_PDisc_unit@{o so s u u0 e}.

Definition PDiscK_free_iso@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) :
  @Isomorphism (@EilenbergMoore@{e so s o} Sets@{o so} PDiscT@{o so s}
                  PDiscMonad@{o so s u u0})
    (fobj[PDiscK@{o so s u u0 e}] X)
    (fobj[@EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
            PDiscMonad@{o so s u u0} ◯ PForget@{o so}] X).
Proof.
  unshelve econstructor;
    [ unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                         PDiscMonad@{o so s u u0} _ _ _ _ id _)
    | unshelve refine (@Build_TAlgebraHom Sets@{o so} PDiscT@{o so s}
                         PDiscMonad@{o so s u u0} _ _ _ _ id _)
    | | ]; intro x; simpl; reflexivity.
Defined.

Definition PDiscK_free@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PDiscK@{o so s u u0 e}
    ≈ @EM_Free@{so o s e} Sets@{o so} PDiscT@{o so s}
        PDiscMonad@{o so s u u0} ◯ PForget@{o so}.
Proof.
  exists PDiscK_free_iso.
  intros X Y f x; simpl. reflexivity.
Defined.

(* The comparison into the algebras of [IdMonad Sets], through θ* of the
   morphism of monads [id_disc_hom]. *)
Definition PDiscKI@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  PTopCat@{o so} ⟶
    @EilenbergMoore@{e so s o} Sets@{o so} Id[Sets@{o so}]
      (IdMonad@{so o} Sets@{o so}) :=
  mh_EM@{so o e s} id_disc_hom@{o so s u u0} ◯ PDiscK@{o so s u u0 e}.

Example PDiscKI_forget_obj@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X : PTopCat@{o so}) :
  fobj[EM_Forget Id[Sets@{o so}] ◯ PDiscKI@{o so s u u0 e}] X
    = fobj[PForget@{o so}] X := eq_refl.

Example PDiscKI_forget_map@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} (X Y : PTopCat@{o so}) (f : X ~> Y) :
  fmap[EM_Forget Id[Sets@{o so}] ◯ PDiscKI@{o so s u u0 e}] f
    = fmap[PForget@{o so}] f := eq_refl.

Example PDiscKI_alg@{o so s u u0 e | o < so, o < s, o < u, so <= e +}
  (X : PTopCat@{o so}) (x : X) :
  t_alg[`2 (fobj[PDiscKI@{o so s u u0 e}] X)] x = x := eq_refl.

(** ** Not full, not an equivalence, not monadic *)

Definition pbool_to_indisc@{o so | o < so +} :
  PBool@{o} ~{PTopCat@{o so}}~> PTwoIndisc@{o} :=
  pindisc_mor _ PBool@{o} setoid_morphism_id.

Lemma no_pindisc_to_bool@{o so | o < so +}
  (g : PTwoIndisc@{o} ~{PTopCat@{o so}}~> PBool@{o}) :
  (∀ b : bool, pmap g b = b) → False.
Proof.
  intros Hg.
  assert (Hopen : POpen PTwoIndisc@{o} (fun b => pmap g b = true)).
  { apply (pcont g (fun b => b = true)).
    unfold pdisc_open. intros x y Hxy e. cbn in Hxy. destruct Hxy. exact e. }
  assert (H : pmap g false = true) by exact (Hopen true false (Hg true)).
  rewrite (Hg false) in H. discriminate H.
Qed.

Lemma PForget_not_Full@{o so | o < so +} : Full PForget@{o so} → False.
Proof.
  intros HF.
  apply (no_pindisc_to_bool
           (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} setoid_morphism_id)).
  intro b.
  exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} setoid_morphism_id b).
Qed.

(* Every monadic functor is conservative, and [PForget] is not: it sends
   [pbool_to_indisc] to an isomorphism of [Sets], and that is not one.
   Hypothesis 3 of Monad/Monadicity/Crude.v's crude monadicity theorem. *)
Lemma PForget_not_ReflectsIsos@{o so | o < so +} :
  ReflectsIsos PForget@{o so} → False.
Proof.
  intros R.
  assert (If : @IsIsomorphism Sets@{o so} _ _
                 (fmap[PForget@{o so}] pbool_to_indisc@{o so})).
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ R _ _ _ If) as [g Hr Hl].
  apply (no_pindisc_to_bool g).
  intro b. exact (Hr b).
Qed.

Lemma PDiscK_not_Full@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Full PDiscK@{o so s u u0 e} → False.
Proof.
  intros HF.
  unshelve epose (a := @Build_TAlgebraHom Sets@{o so} _ _ _ _
                    (`2 (fobj[PDiscK@{o so s u u0 e}] PTwoIndisc@{o}))
                    (`2 (fobj[PDiscK@{o so s u u0 e}] PBool@{o}))
                    setoid_morphism_id _).
  { intro b; reflexivity. }
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} a)).
  intro b. exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} a b).
Qed.

Lemma PDiscK_not_Equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories PDiscK@{o so s u u0 e} → False.
Proof. intros E. exact (PDiscK_not_Full (Equivalence_Full E)). Qed.

(* The comparison into the algebras of [IdMonad Sets] is not full either:
   the identity of [bool] is an algebra map KI PTwoIndisc → KI PBool. *)
Lemma PDiscKI_not_Full@{o so s u u0 e | o < so, o < s, o < u, so <= e +} :
  Full PDiscKI@{o so s u u0 e} → False.
Proof.
  intros HF.
  unshelve epose (a := @Build_TAlgebraHom Sets@{o so} _ _ _ _
                    (`2 (fobj[PDiscKI@{o so s u u0 e}] PTwoIndisc@{o}))
                    (`2 (fobj[PDiscKI@{o so s u u0 e}] PBool@{o}))
                    setoid_morphism_id _).
  { intro b; reflexivity. }
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} a)).
  intro b. exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} a b).
Qed.

Lemma PDiscKI_not_Equivalence@{o so s u u0 e |
  o < so, o < s, o < u, so <= e +} :
  EquivalenceOfCategories PDiscKI@{o so s u u0 e} → False.
Proof. intros E. exact (PDiscKI_not_Full (Equivalence_Full E)). Qed.

Lemma PDiscK_not_Cat_iso@{o so s u u0 c | o < so, o < s, o < u, so < c +} :
  @IsIsomorphism Cat _ _ PDiscK@{o so s u u0 so} → False.
Proof.
  intros I.
  apply PDiscK_not_Equivalence.
  exact (@Build_EquivalenceOfCategories _ _ _ (@two_sided_inverse _ _ _ _ I)
           (@is_right_inverse _ _ _ _ I)
           (symmetry (@is_left_inverse _ _ _ _ I))).
Qed.

Lemma PForget_not_Monadic@{o so m m0 m1 m3 m6 |
  o < so, o < m0, so <= m, so <= m1, so <= m3, m1 <= m, m3 <= m +} :
  Monadic@{m m0 m1 so m3 o so m6} PForget@{o so} → False.
Proof.
  intros [F [A E]].
  pose proof (Equivalence_Full E) as HF.
  lazymatch type of E with
  | @EquivalenceOfCategories _ ?EM ?K =>
    assert (If : @IsIsomorphism Sets@{o so} _ _
                   (fmap[EM_Forget _] (fmap[K] pbool_to_indisc@{o so})))
  end.
  { unshelve econstructor; [ exact setoid_morphism_id | intro b; reflexivity
                            | intro b; reflexivity ]. }
  destruct (@reflects_iso _ _ _ (em_forget_reflects_isos _) _ _ _ If)
    as [g Hr Hl].
  apply (no_pindisc_to_bool (@prefmap _ _ _ HF PTwoIndisc@{o} PBool@{o} g)).
  intro b. transitivity (t_alg_hom[g] b).
  - exact (@fmap_sur _ _ _ HF PTwoIndisc@{o} PBool@{o} g b).
  - exact (Hr b).
Qed.
