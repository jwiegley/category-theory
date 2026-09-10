Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.End.
Require Import Category.Theory.Equivalence.Limit.

Generalizable All Variables.

(** * Hom-functors are continuous: the isomorphism form and its consequences *)

(* Mac Lane §V.4 Theorem 1 and Remarks 1-3 (book pp. 116-117;
   maclane:V.4:thm1, maclane:V.4:remark1-3); Awodey §5.5 Proposition 5.27
   and Corollary 5.29 with the coproduct remark, and §7.2's remark that a
   functor naturally isomorphic to a representable preserves limits; Riehl
   §3.5 display (3.5.1), Exercise 3.5.i, Theorem 3.5.2 and Theorem 3.5.6.
   nLab: https://ncatlab.org/nlab/show/continuous+functor
         https://ncatlab.org/nlab/show/representable+functor

   BACKGROUND.  The covariant hom-functor C(c, −) : C ⟶ Sets preserves every
   limit that exists in C — the archetypal continuous functor — so a limit is
   computed representably: C(c, lim F) ≅ lim C(c, F−), naturally in c.
   Dually C(−, c) carries colimits to limits.  Theorem 1 and Remark 3 at CONE
   level are Functor/Hom/Limit.v's (#331): [hom_ContinuousFunctor],
   [cohom_ContinuousFunctor], [cohom_colimit_to_limit].  What was missing,
   and what this file adds, is the ISOMORPHISM form — the two sides read as
   objects of Sets and compared — together with the three Riehl §3.5 items
   and Awodey's transport along a natural isomorphism.  Every theorem here
   is a transport or an instantiation of a landed one; the file proves no
   universal property from scratch.

   STALE PREMISES, RE-MEASURED.
     - "There is no preservation witness for the hom-functor — no
       [PreservesLimit G (Curried_Hom C c)]": FALSE since #331.
       Functor/Hom/Limit.v has [HomFrom c := [Hom c ,─]] (:260),
       [hom_PreservesLimitCone] (:325), [hom_ContinuousFunctor] (:338),
       [hom_PreservesLimit] (:345), [hom_PreservesAllLimits] (:349),
       [hom_IsIndexedProduct] (:413), [HomTo c := [Hom ─, c]] (:492) with
       [hom_to_is_op_hom_from : HomTo = @HomFrom (C^op) c := eq_refl] (:494),
       [cohom_ContinuousFunctor] (:496), [cohom_colimit_to_limit] (:507),
       [cohom_IsIndexedProduct] (:519).  Work items 1 (Theorem 1) and 3
       (Remark 3) were therefore done before this issue was opened; the
       issue's pinned names are supplied here as aliases,
       [hom_preserves_limits] and [cohom_carries_colimits_to_limits].
     - "[Curried_CoHom] has no consumer beyond Yoneda": FALSE
       (Functor/Hom/Limit.v:492 consumes it as [HomTo]).  "There is no
       [Cocartesian] companion file" to Adjunction/Diagonal/Product.v: FALSE
       (Adjunction/Diagonal/Coproduct.v:117 [Diagonal_Coproduct_Adjunction]).
       Awodey's ingredients "missing" — equalizers in Sets and the general
       Sets limit — exist: [Sets_HasEqualizers], and [Sets_Limit] /
       [Sets_Complete] at Instance/Sets/Complete.v:184/:196.
     - "The cone-level statement that h ↦ (limit_leg L x ∘ h) is a limiting
       cone over [HomDiagram c F] in Sets is absent": PARTIAL.  It is present
       over [HomFrom c ◯ F], and that functor is NOT definitionally
       [HomDiagram c F] (Structure/Limit/Weighted.v:49): the two agree on
       objects and on the ACTION of [fmap], both at [eq_refl], and differ at
       the whole [fmap] field, whose respectfulness proof is an opaque
       [Program] obligation discharged differently in Functor/Hom.v:72-76
       and Weighted.v:54-56 (probe N1, beside its two accepted controls).  A
       naming gap, not a mathematical one; this file states Remark 2 over
       the composite (#331's vocabulary) and the Riehl items over
       [HomDiagram] (Weighted.v's), and builds no bridge.
     - The Riehl §3.5 verifier notes are TRUE as stated: [cone_of_nat] /
       [nat_of_cone] (Weighted.v:145/:157) had no round-trip lemma outside
       [wl_iso]'s obligations (:313/:320), which presuppose a limit; nothing
       related [Sets_End] to [Limit]; [wlim_natural] is naturality of the
       composite through C(X, lim F), not of (3.5.1) itself.
     - Work item 4's "discharge the Instance/Ens.v header caveat": that
       header carries no universe caveat (a search of the file for
       "universe" and "caveat" finds none); it explains that [Ens] is not
       the classical category of sets.  Nothing to discharge; not edited.

   WHAT IS DELIVERED (50 named constants plus 19 [Program] obligations,
   every one closed under the global context).
     (A) TRANSPORT (Awodey §7.2).  For [e : F ≈ G] (a natural isomorphism of
         functors C ⟶ D): [fun_equiv_whisker] (whiskering [e] by a diagram;
         [Proof using e], the Structure/Equalizer/Wide.v idiom),
         [transport_isalimit] (Theory/Equivalence/Limit.v:245's
         [isalimit_transport], which transports along an isomorphism of
         DIAGRAMS — nothing in tree transported [PreservesLimitCone] along
         an isomorphism of FUNCTORS), [transport_cone],
         [transport_coneiso_legs], [transport_coneiso],
         [transport_islimitcone], and the two headline transports
         [PreservesLimitCone_transport : PreservesLimitCone K F →
         PreservesLimitCone K G] and [ContinuousFunctor_transport].
     (B) RIEHL (3.5.1), NO LIMIT ASSUMED.  [cone_of_nat_mor] /
         [nat_of_cone_mor] (Weighted.v's conversions as Sets-morphisms),
         [nat_cone_nat] / [cone_nat_cone] (the round trips, one line each),
         [cone_nat_iso : Nat(Δ1, HomDiagram X F) ≅[Sets] Cone(X, F)] —
         Exercise 3.5.i's isomorphism, independent of [wl_iso] — with
         [cone_of_nat_natural] / [nat_of_cone_natural] (naturality in X
         against [HomDiagram_precompose] and [ConePresheaf]'s [fmap], both
         [reflexivity]); and the tuple presentation [limtuple_to_cone] /
         [cone_to_limtuple] / [limtuple_cone_iso : Sets_limit_obj
         (HomDiagram X F) ≅[Sets] Cone(X, F)].
     (C) THE END/LIMIT BRIDGE.  [homend_functor := HomDiagram X F ◯ Snd],
         [end_to_limtuple] / [limtuple_to_end] / [end_limtuple_iso]
         (Instance/Sets/End.v's compatible families against the Sets-limit
         tuples; the wedge condition reduces to the tuple condition by
         [fmap_id]), [end_cone], [end_coneiso], [end_IsLimitCone] and
         [end_Limit : Limit (HomDiagram X F)] with the end as its apex — the
         one missing link the issue isolates.
     (D) REMARK 2.  Over [L : Limit F] and [c : C]: [homlim_cone] /
         [homlim_islimit] (Instance/Sets/Complete.v's limit of the
         hom-diagram), [homimg_islimit] (#331's theorem at the limit cone),
         [remark2_coneiso] (a [ConeIso], hence leg-compatible), the
         isomorphism of Sets-objects [remark2_iso c : Sets_limit_obj (HomFrom
         c ◯ F) ≅ C(c, lim F)] with [remark2_iso_legs] / [remark2_iso_from],
         [homlim_reindex] (precomposition on the limit side),
         [remark2_reindexed_cone], and NATURALITY IN c as the equation
         [remark2_natural : to (remark2_iso c') (homlim_reindex h p) ≈ to
         (remark2_iso c) p ∘ h] (by [limit_med_eq]).  Riehl's own direction
         (3.5.3): [remark2_comparison] is the canonical comparison
         C(c, lim F) → lim C(c, F−) and [remark2_comparison_iso] its
         invertibility — the instantiation of
         [comparison_iso_of_PreservesLimitCone] that Functor/Hom/Limit.v's
         header recorded as not performed.
     (E) REMARK 3.  [remark3_iso c : Sets_limit_obj (HomTo c ◯ F^op) ≅
         C(colim F, c)] and [remark3_natural], both [:=] instantiations of
         (D) at [(J^op, C^op, F^op)]: [Colimit F] IS [Limit F^op] and
         [HomTo c] IS [HomFrom c] on [C^op], so no tactic is needed.
     (F) THE PRODUCT AND COPRODUCT INSTANCES AS ISOMORPHISMS.  [hom_iprod_iso
         : C(c, ∏ aᵢ) ≅[Sets] ∏ᵢ C(c, aᵢ)] and [cohom_icoprod_iso : C(∐ aⱼ,
         c) ≅[Sets] ∏ⱼ C(aⱼ, c)] by Structure/Limit/Product/Finite.v's
         [iprod_unique_iso] against #331's [hom_IsIndexedProduct] /
         [cohom_IsIndexedProduct] and [Sets_IsIndexedProduct] — reuse, not
         re-derivation — with [hom_iprod_iso_to] / [cohom_icoprod_iso_to]
         (the forward maps are postcomposition with the projections,
         precomposition with the injections) and naturality in c
         ([hom_iprod_iso_natural], [cohom_icoprod_iso_natural]); Awodey's
         coproduct remark is the second.
     (G) REMARK 1.  [HomFrom_at@{o h s +} : C ⟶ Sets@{h s}] and
         [hom_continuous_at : ContinuousFunctor HomFrom_at] for every
         relation level [s > h]: see UNIVERSES for exactly what "any
         universe of sets" means here.

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 50
   constants).
     - REMARK 1, HALF TRUE.  [Sets@{h s}] is a category at [Category@{s h h}]
       and [HomFrom c] lands in [Sets@{h s}] for [C : Category@{o h h}] with
       [h < s]: the RELATION level [s] of the target is free above the
       carrier level, and the theorem is ONE universe-polymorphic constant
       instantiating at every level of Sets — that is the sense in which the
       statement "holds into any universe of sets".  The CARRIER level is
       PINNED to C's hom level: the hom-functor of a FIXED C cannot be read
       into a strictly larger universe of sets (probe N2: [HomFrom cw : Cw ⟶
       Sets@{hbig sbig}] under [Constraint h1 < hbig] is refused, "Cannot
       enforce h1 = hbig because h1 < hbig", beside the accepted [Sets@{h1
       sbig}] control).  Lifting would need a Sets-to-Sets lift functor,
       which the tree does not have; not claimed.
     - SHAPES.  All 40 constants with a shape J in their context identify
       J's hom level with the hom level of the category carrying the limit
       ([u0 = u2] in their blocks; [PreservesLimitCone], [Limit] and [Cone]
       identify shape hom with ambient hom); in section (A) the equation
       [u0 = u2] instead reads C's hom = D's hom and five of its eight
       constants add [u0 = u7] for J.  The eight Remark 2/3 constants stated
       against [L : Limit F] add [u0 = u3], the limit's own level.  Every
       object level stays free of equations.
     - SMALLNESS, THE FOOTNOTE RIEHL SIDESTEPS.  23 constants carry
       [u <= u2]: J's OBJECT level at or below C's hom level, which is Sets'
       carrier level — every constant that forms [Sets_Limit] /
       [Sets_limit_cone] of the hom-diagram or the functor category
       [[J, Sets]] (whose hom quantifies over J's objects); sections (B),
       (C), (D), (E) except the pure carrier maps ([end_to_limtuple],
       [limtuple_to_end], [end_limtuple_iso], [homlim_reindex],
       [remark2_reindexed_cone], [homimg_islimit], [homend_functor], the two
       round-trip lemmas).  The other 17 shape-indexed constants, section
       (A) among them, carry no such bound, and neither does #331's theorem:
       probe N3 pins it — under [Constraint h < jo], [HomFrom cw ◯ F] and
       [hom_PreservesLimitCone cw F] are accepted and [Sets_Limit (HomFrom
       cw ◯ F)] is refused, "Cannot enforce h = … because h < jo <= …".
       Riehl's footnote extending (3.5.1) to large diagrams is exactly what
       this bound excludes; removing it is a change to Instance/Sets/
       Complete.v's construction, not a deliverable here.
     - THE INDEX COLLAPSE.  The four product/coproduct constants
       ([hom_iprod_iso], [hom_iprod_iso_to], [cohom_icoprod_iso],
       [cohom_icoprod_iso_to]) carry [u0 = u1]: the index type's universe is
       C's hom level, from [Sets_iprod_obj@{u0 u0 u0 u0 u0}]
       (Instance/Sets/Products.v); the two naturality lemmas absorb the same
       identification into a shared binder variable ([A : Type@{u}] beside
       [C : Category@{u3 u u}]).  Not a [Set] pin; disclosed as a collapse.
     - THE ALIASES DO NOT MINIMIZE.  [hom_preserves_limits] and
       [cohom_carries_colimits_to_limits], written bare over [{C :
       Category}], keep C's object level distinct from its hom level ([C :
       Category@{u8 u9 u9}], [Category@{u4 u5 u5}]) and carry no equation,
       like their donors — measured against [hom_ContinuousFunctor] and
       [cohom_colimit_to_limit] before deciding not to annotate them
       (Instance/Fun/Limit.v's and Instance/Fun/Creation.v's aliases did
       minimize; this pair does not).
     - No word-bounded [Set], no [JMeq] / [EqdepFacts] / [eq_rect_r] in any
       block; [end_Limit] carries stdlib [prod_rect] bounds from the product
       shape [J^op ∏ J].

   COUNTS AND CONVENTIONS.
     - 50 [.glob] declaration heads (37 [def], 13 [prf]) plus 19 [Program]
       obligations the [.glob] cannot see ([cone_nat_iso] 2,
       [cone_of_nat_mor] 1, [cone_to_limtuple] 1, [end_cone] 1,
       [end_limtuple_iso] 2, [end_to_limtuple] 2, [homlim_reindex] 2,
       [limtuple_cone_iso] 2, [limtuple_to_cone] 2, [limtuple_to_end] 2,
       [nat_of_cone_mor] 1, [remark2_reindexed_cone] 1), all "Closed under
       the global context", zero [Axioms:] lines; the gate carries the 50
       heads, fully qualified, the issue's two names among them.
       [Obligation Tactic := idtac] locally, so every obligation is written
       out (189 files in the tree do the same).
     - Two [Defined] ([fun_equiv_whisker], [end_coneiso]), each flipped to
       [Qed] alone in a copy of the file: [fun_equiv_whisker] is
       LOAD-BEARING ([transport_coneiso_legs]'s [change … with] needs the
       whiskered components to reduce; the library stops at that line),
       [end_coneiso] is not (library and probe compile unchanged) and stays
       transparent because it is data.  Thirty-two [Qed] tokens outside this
       header (13 lemmas, 19 obligations).
     - Closure 73 files excluding self: Theory/Equivalence/Limit.v costs 7
       at the margin and is required for [isalimit_transport] alone —
       dropping it would take the closure to 66 at the price of about 35
       lines duplicating a landed mediator, so it stays; Functor/Hom/Limit.v
       2, Instance/Sets/Complete.v 2, Instance/Sets/End.v 1,
       Structure/Limit/Product/Finite.v 1, Structure/Limit/Weighted.v 1, the
       other 21 [Require]s 0.  Zero name collisions: each of the 50 names
       has 0 word occurrences elsewhere in the tree.
     - Test/ProbeHomContinuous428.v mirrors the [Require] list and carries 4
       refutation commands (1 instrument + N1 CONVERSION + N2 UNIVERSE + N3
       UNIVERSE), each stripped one at a time in a copy of the whole file
       and each beside its accepted controls (the objectwise and elementwise
       [eq_refl]s for N1; the free relation level for N2; the hom-diagram
       and #331's preservation at the large shape for N3); five [eq_refl]
       readbacks; guard coverage 24 identifier tokens inside the
       refutations / 21 also named outside, comments stripped, with three
       exhaustive exceptions (the keyword, the refuted declaration's name,
       the absent name); rename-simulated 12/12 ([HomFrom], [HomDiagram],
       [Sets_Limit], [fmap], [carrier], [remark2_iso], [end_Limit],
       [hom_PreservesLimitCone], [hom_continuous_at], [HomFrom_at], [Sets],
       [ContinuousFunctor]; module paths excluded), every first break on a
       positive line.  [make todo] grows by those 4 lines only (2226 → 2230
       over master 969ac56e), so the issue's "adds no new hits" box is not
       met as written; disclosed.
     - Two sentences of Functor/Hom/Limit.v's NOT DELIVERED block (the
       comparison instantiation, naturality in c) now point here;
       line-neutral, and its INDEX bullet says the same.

   NOT DELIVERED.
     - Remark 2 as an isomorphism of PRESHEAVES, i.e. an [Isomorphism] in
       [[C^op, Sets]] with the left side [c ↦ Sets_limit_obj (HomFrom c ◯
       F)] packaged as a functor; [remark2_natural] is the equation form,
       as [wlim_natural] states its own naturality.
     - Riehl's footnote (large diagrams): see SMALLNESS.
     - A Remark 2 over [HomDiagram c F], or any bridge between the two
       presentations of the hom-diagram (an identity-component natural
       transformation between them typechecks; not built).
     - Continuity of [Curried_Hom C : C^op ⟶ [C, Sets]] itself,
       cocontinuity, reflection, creation, converse and characterisation —
       all listed as not delivered by Functor/Hom/Limit.v and outside this
       issue.
     - Awodey §7.2's consequence for [U : Grp ⟶ Sets] (#411's) and the
       concreteness vocabulary (#263, #644).
     - Remark 1 as a LIFT of a fixed category's hom-functor into a larger
       universe of sets.
     - No edit to Functor/Hom.v, Structure/Limit/Weighted.v, Instance/Sets/
       Complete.v, Instance/Sets/End.v, Theory/Equivalence/Limit.v or
       Instance/Ens.v; the two Functor/Hom/Limit.v sentences are the only
       prose edits. *)

#[local] Obligation Tactic := idtac.

(** * A. Awodey 7.2 -- preservation transports along a natural isomorphism *)

Section Transport.

Context {C D : Category}.
Context {F G : C ⟶ D}.
Context (e : F ≈ G).

Definition fun_equiv_whisker {J : Category} (K : J ⟶ C) : F ◯ K ≈ G ◯ K.
Proof using e.
  exists (fun j => `1 e (K j)).
  intros x y f; exact (`2 e _ _ (fmap[K] f)).
Defined.

Section AtDiagram.

Context {J : Category}.
Context {K : J ⟶ C}.
Context (N : Cone K).
Context (HFN : IsLimitCone (FCone F N)).

Definition transport_isalimit : IsALimit (G ◯ K) (F (vertex_obj[N])) :=
  isalimit_transport (fun_equiv_whisker K) (limitcone_isalimit HFN).

Definition transport_cone : Cone (G ◯ K) :=
  @Build_Cone J D (G ◯ K) (F (vertex_obj[N]))
    (@limit_acone _ _ _ _ transport_isalimit).

Lemma transport_coneiso_legs (x : J) :
  cone_leg (FCone G N) x ∘ to (`1 e vertex_obj[N])
    ≈ cone_leg transport_cone x.
Proof.
  simpl.
  change (cone_leg transport_cone x)
    with (to (`1 e (K x)) ∘ fmap[F] (cone_leg N x)).
  rewrite (`2 e vertex_obj[N] (K x) (cone_leg N x)).
  rewrite !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

Definition transport_coneiso : ConeIso transport_cone (FCone G N) :=
  (`1 e vertex_obj[N] ; transport_coneiso_legs).

Definition transport_islimitcone : IsLimitCone (FCone G N) :=
  limitcone_transport transport_coneiso
    (isalimit_limitcone transport_isalimit).

End AtDiagram.

Definition PreservesLimitCone_transport {J : Category} {K : J ⟶ C}
  (P : PreservesLimitCone K F) : PreservesLimitCone K G :=
  fun N HN => transport_islimitcone N (P N HN).

Definition ContinuousFunctor_transport (P : ContinuousFunctor F) :
  ContinuousFunctor G :=
  fun J K => PreservesLimitCone_transport (P J K).

End Transport.

(** * B. Riehl (3.5.1) -- Nat(Δ1, C(X,F-)) ≅ Cone(X,F), no limit assumed *)

Section RoundTrip.

Context {J C : Category}.
Context {F : J ⟶ C}.

Program Definition cone_of_nat_mor (X : C) :
  ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram X F))
    ~{Sets}~> fobj[ConePresheaf F] X :=
  {| morphism := cone_of_nat X |}.
Next Obligation. intros X α β Hαβ j; exact (Hαβ j ttt). Qed.

Program Definition nat_of_cone_mor (X : C) :
  fobj[ConePresheaf F] X
    ~{Sets}~> ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram X F)) :=
  {| morphism := nat_of_cone X |}.
Next Obligation. intros X κ κ' H j u; exact (H j). Qed.

Lemma nat_cone_nat (X : C)
  (α : Δ[J]( @terminal_obj Sets Sets_Terminal ) ⟹ HomDiagram X F) :
  nat_of_cone X (cone_of_nat X α) ≈ α.
Proof. intros j u; destruct u; reflexivity. Qed.

Lemma cone_nat_cone (X : C) (κ : ACone X F) :
  cone_of_nat X (nat_of_cone X κ) ≈ κ.
Proof. intro j; reflexivity. Qed.

Program Definition cone_nat_iso (X : C) :
  @Isomorphism Sets
    ([[[J,Sets]]](Δ[J]( @terminal_obj Sets Sets_Terminal ), HomDiagram X F))
    (fobj[ConePresheaf F] X) :=
  {| to := cone_of_nat_mor X ; from := nat_of_cone_mor X |}.
Next Obligation. intros X κ; exact (cone_nat_cone X κ). Qed.
Next Obligation. intros X α; exact (nat_cone_nat X α). Qed.

Lemma cone_of_nat_natural {X X' : C} (h : X' ~{C}~> X)
  (α : Δ[J]( @terminal_obj Sets Sets_Terminal ) ⟹ HomDiagram X F) :
  cone_of_nat X' (nat_compose (HomDiagram_precompose h F) α)
    ≈ fmap[ConePresheaf F] (h : X ~{C^op}~> X') (cone_of_nat X α).
Proof. intro j; simpl; reflexivity. Qed.

Lemma nat_of_cone_natural {X X' : C} (h : X' ~{C}~> X) (κ : ACone X F) :
  nat_of_cone X' (fmap[ConePresheaf F] (h : X ~{C^op}~> X') κ)
    ≈ nat_compose (HomDiagram_precompose h F) (nat_of_cone X κ).
Proof. intros j u; simpl; reflexivity. Qed.

(* The tuple presentation: the Sets-limit apex of the hom-diagram IS the
   cone setoid.  Again no limit in C is assumed. *)

Program Definition limtuple_to_cone (X : C) :
  Sets_limit_obj (HomDiagram X F) ~{Sets}~> fobj[ConePresheaf F] X :=
  {| morphism := fun p => {| vertex_map := fun j => `1 p j |} |}.
Next Obligation. intros X p j j' g; exact (`2 p j j' g). Qed.
Next Obligation. intros X p q Hpq j; exact (Hpq j). Qed.

Program Definition cone_to_limtuple (X : C) :
  fobj[ConePresheaf F] X ~{Sets}~> Sets_limit_obj (HomDiagram X F) :=
  {| morphism := fun κ =>
       (fun j => @vertex_map _ _ _ _ κ j;
        fun j j' g => @cone_coherence _ _ _ _ κ j j' g) |}.
Next Obligation. intros X κ κ' H j; exact (H j). Qed.

Program Definition limtuple_cone_iso (X : C) :
  @Isomorphism Sets (Sets_limit_obj (HomDiagram X F)) (fobj[ConePresheaf F] X) :=
  {| to := limtuple_to_cone X ; from := cone_to_limtuple X |}.
Next Obligation. intros X κ j; reflexivity. Qed.
Next Obligation. intros X p j; reflexivity. Qed.

End RoundTrip.

(** * C. Riehl 3.5 -- the end/limit bridge *)

Section EndBridge.

Context {J C : Category}.
Context (X : C).
Context (F : J ⟶ C).

Definition homend_functor : J^op ∏ J ⟶ Sets := HomDiagram X F ◯ Snd.

Program Definition end_to_limtuple :
  Sets_End_obj homend_functor ~{Sets}~> Sets_limit_obj (HomDiagram X F) :=
  {| morphism := fun s => (fun j => `1 s j ; _) |}.
Next Obligation.
  intros s j j' g; simpl.
  rewrite (`2 s j j' g); simpl.
  now rewrite fmap_id, id_left.
Qed.
Next Obligation. intros s t Hst j; exact (Hst j). Qed.

Program Definition limtuple_to_end :
  Sets_limit_obj (HomDiagram X F) ~{Sets}~> Sets_End_obj homend_functor :=
  {| morphism := fun p => (fun j => `1 p j ; _) |}.
Next Obligation.
  intros p j j' g; simpl.
  rewrite fmap_id, id_left.
  exact (`2 p j j' g).
Qed.
Next Obligation. intros p q Hpq j; exact (Hpq j). Qed.

Program Definition end_limtuple_iso :
  Sets_End_obj homend_functor ≅[Sets] Sets_limit_obj (HomDiagram X F) :=
  {| to := end_to_limtuple ; from := limtuple_to_end |}.
Next Obligation. intros p j; reflexivity. Qed.
Next Obligation. intros s j; reflexivity. Qed.

(* The end, read as a cone over the hom-diagram: the legs are the end's own
   projections and the coherence is its wedge condition. *)
Program Definition end_cone : Cone (HomDiagram X F) :=
  {| vertex_obj := Sets_End_obj homend_functor
   ; coneFrom := {| vertex_map := fun j => end_projection homend_functor j |} |}.
Next Obligation.
  intros j j' g s; simpl.
  rewrite (`2 s j j' g); simpl.
  now rewrite fmap_id, id_left.
Qed.

Definition end_coneiso : ConeIso (Sets_limit_cone (HomDiagram X F)) end_cone.
Proof.
  exists (iso_sym end_limtuple_iso).
  intros j p; reflexivity.
Defined.

(* The one missing link the issue isolates: the end IS a limit in Sets. *)
Definition end_IsLimitCone : IsLimitCone end_cone :=
  limitcone_transport end_coneiso
    (limit_limitcone (Sets_Limit (HomDiagram X F))).

Definition end_Limit : Limit (HomDiagram X F) :=
  limitcone_limit end_cone end_IsLimitCone.

End EndBridge.

(** * D. Mac Lane V.4 Remark 2 -- lim C(c,F-) ≅ C(c, lim F), natural in c *)

Section Remark2.

Context {J C : Category}.
Context {F : J ⟶ C}.
Context (L : Limit F).

Definition homlim_cone (c : C) : Cone (HomFrom c ◯ F) :=
  @limit_cone _ _ _ (Sets_Limit (HomFrom c ◯ F)).

Definition homlim_islimit (c : C) : IsLimitCone (homlim_cone c) :=
  limit_limitcone (Sets_Limit (HomFrom c ◯ F)).

Definition homimg_islimit (c : C) :
  IsLimitCone (FCone (HomFrom c) (@limit_cone _ _ _ L)) :=
  hom_PreservesLimitCone c F (@limit_cone _ _ _ L) (limit_limitcone L).

Definition remark2_coneiso (c : C) :
  ConeIso (homlim_cone c) (FCone (HomFrom c) (@limit_cone _ _ _ L)) :=
  limitcone_iso (homlim_islimit c) (homimg_islimit c).

Definition remark2_iso (c : C) :
  @Isomorphism Sets (Sets_limit_obj (HomFrom c ◯ F))
    {| carrier := c ~{C}~> vertex_obj[@limit_cone _ _ _ L]
     ; is_setoid := @homset C c (vertex_obj[@limit_cone _ _ _ L]) |} :=
  `1 (remark2_coneiso c).

Lemma remark2_iso_legs (c : C) (p : Sets_limit_obj (HomFrom c ◯ F)) (j : J) :
  cone_leg (@limit_cone _ _ _ L) j ∘ to (remark2_iso c) p ≈ `1 p j.
Proof. exact (`2 (remark2_coneiso c) j p). Qed.

Lemma remark2_iso_from (c : C) (u : c ~{C}~> vertex_obj[@limit_cone _ _ _ L])
  (j : J) :
  `1 (from (remark2_iso c) u) j ≈ cone_leg (@limit_cone _ _ _ L) j ∘ u.
Proof. exact (coneiso_from (remark2_coneiso c) j u). Qed.

Program Definition homlim_reindex {c c' : C} (h : c' ~{C}~> c) :
  Sets_limit_obj (HomFrom c ◯ F) ~{Sets}~> Sets_limit_obj (HomFrom c' ◯ F) :=
  {| morphism := fun p => (fun j => `1 p j ∘ h; _) |}.
Next Obligation.
  intros c c' h p j j' g; simpl.
  rewrite comp_assoc.
  now rewrite (`2 p j j' g).
Qed.
Next Obligation.
  intros c c' h p q Hpq j; simpl; now rewrite (Hpq j).
Qed.

Program Definition remark2_reindexed_cone {c c' : C} (h : c' ~{C}~> c)
  (p : Sets_limit_obj (HomFrom c ◯ F)) : Cone F :=
  {| vertex_obj := c'
   ; coneFrom := {| vertex_map := fun j => `1 p j ∘ h |} |}.
Next Obligation.
  intros c c' h p j j' g; simpl.
  rewrite comp_assoc.
  now rewrite (`2 p j j' g).
Qed.

Theorem remark2_natural {c c' : C} (h : c' ~{C}~> c)
  (p : Sets_limit_obj (HomFrom c ◯ F)) :
  to (remark2_iso c') (homlim_reindex h p) ≈ to (remark2_iso c) p ∘ h.
Proof.
  apply (limit_med_eq (limit_is_alimit L) (remark2_reindexed_cone h p)).
  - intro j; simpl.
    exact (remark2_iso_legs c' (homlim_reindex h p) j).
  - intro j; simpl.
    rewrite comp_assoc.
    now rewrite (remark2_iso_legs c p j).
Qed.

(* Riehl 3.5.3 in her own direction: the CANONICAL comparison map
   C(c, lim F) --> lim C(c, F-) is invertible.  This performs the
   composition Functor/Hom/Limit.v's header records as not performed. *)
Definition remark2_comparison (c : C) :
  fobj[HomFrom c] (vertex_obj[@limit_cone _ _ _ L])
    ~{Sets}~> Sets_limit_obj (HomFrom c ◯ F) :=
  cone_comparison (HomFrom c) (@limit_cone _ _ _ L) (homlim_islimit c).

Definition remark2_comparison_iso (c : C) :
  IsIsomorphism (remark2_comparison c) :=
  comparison_iso_of_PreservesLimitCone (HomFrom c)
    (hom_PreservesLimitCone c F) (homlim_islimit c)
    (@limit_cone _ _ _ L) (limit_limitcone L).

End Remark2.

(** * E. Mac Lane V.4 Remark 3 -- the contravariant hom carries colimits
        in C to limits in Sets *)

Section Remark3.

Context {J C : Category}.
Context {F : J ⟶ C}.
Context (L : Colimit F).

(* Pure instantiation of Remark 2 at the opposite category: [Colimit F] IS
   [Limit (F^op)] and [HomTo c] IS [HomFrom c] on [C^op]. *)
Definition remark3_iso (c : C) :
  @Isomorphism Sets (Sets_limit_obj (HomTo c ◯ F^op))
    {| carrier := vertex_obj[@limit_cone _ _ _ L] ~{C}~> c
     ; is_setoid := @homset (C^op) c (vertex_obj[@limit_cone _ _ _ L]) |} :=
  @remark2_iso (J^op) (C^op) (F^op) L c.

Theorem remark3_natural {c c' : C} (h : c ~{C}~> c')
  (p : Sets_limit_obj (HomTo c ◯ F^op)) :
  to (remark3_iso c') (@homlim_reindex (J^op) (C^op) (F^op) c c' h p)
    ≈ to (remark3_iso c) p ∘[C^op] h.
Proof. exact (@remark2_natural (J^op) (C^op) (F^op) L c c' h p). Qed.

End Remark3.

(** * F. The product and coproduct instances, as isomorphisms of
        Sets-objects rather than family-level universal properties *)

Section ProductInstance.

Context {C : Category}.
Context (c : C).
Context {A : Type}.
Context {f : A → C}.
Context {p : C}.
Context {proj : ∀ a : A, p ~{C}~> f a}.
Context (H : IsIndexedProduct f p proj).

Definition hom_iprod_iso :
  fobj[HomFrom c] p ≅[Sets] Sets_iprod_obj (fun a => fobj[HomFrom c] (f a)) :=
  iprod_unique_iso (fun a => fobj[HomFrom c] (f a)) _ _ _ _
    (hom_IsIndexedProduct c H)
    (Sets_IsIndexedProduct (fun a => fobj[HomFrom c] (f a))).

Lemma hom_iprod_iso_to (u : c ~{C}~> p) (a : A) :
  to hom_iprod_iso u a ≈ proj a ∘ u.
Proof.
  exact (iprod_compare_commutes (fun a => fobj[HomFrom c] (f a))
           (fobj[HomFrom c] p)
           (Sets_iprod_obj (fun a => fobj[HomFrom c] (f a)))
           (fun a => fmap[HomFrom c] (proj a))
           (Sets_iprod_proj (fun a => fobj[HomFrom c] (f a)))
           (Sets_IsIndexedProduct (fun a => fobj[HomFrom c] (f a))) a u).
Qed.

End ProductInstance.

Section CoproductInstance.

Context {C : Category}.
Context (c : C).
Context {A : Type}.
Context {g : A → C}.
Context {q : C}.
Context {inj : ∀ a : A, g a ~{C}~> q}.
Context (H : IsIndexedCoproduct g q inj).

Definition cohom_icoprod_iso :
  fobj[HomTo c] q ≅[Sets] Sets_iprod_obj (fun a => fobj[HomTo c] (g a)) :=
  iprod_unique_iso (fun a => fobj[HomTo c] (g a)) _ _ _ _
    (cohom_IsIndexedProduct c H)
    (Sets_IsIndexedProduct (fun a => fobj[HomTo c] (g a))).

Lemma cohom_icoprod_iso_to (u : q ~{C}~> c) (a : A) :
  to cohom_icoprod_iso u a ≈ u ∘ inj a.
Proof.
  exact (iprod_compare_commutes (fun a => fobj[HomTo c] (g a))
           (fobj[HomTo c] q)
           (Sets_iprod_obj (fun a => fobj[HomTo c] (g a)))
           (fun a => fmap[HomTo c] (inj a))
           (Sets_iprod_proj (fun a => fobj[HomTo c] (g a)))
           (Sets_IsIndexedProduct (fun a => fobj[HomTo c] (g a))) a u).
Qed.

End CoproductInstance.


(* Naturality in c of the two product instances, which is what makes them
   natural isomorphisms of Sets-objects rather than pointwise bijections. *)

Lemma hom_iprod_iso_natural {C : Category} {A : Type} {f : A → C} {p : C}
  {proj : ∀ a : A, p ~{C}~> f a} (H : IsIndexedProduct f p proj)
  {c c' : C} (h : c' ~{C}~> c) (u : c ~{C}~> p) (a : A) :
  to (hom_iprod_iso c' H) (u ∘ h) a ≈ to (hom_iprod_iso c H) u a ∘ h.
Proof.
  rewrite (hom_iprod_iso_to c' H (u ∘ h) a).
  rewrite (hom_iprod_iso_to c H u a).
  now rewrite comp_assoc.
Qed.

Lemma cohom_icoprod_iso_natural {C : Category} {A : Type} {g : A → C} {q : C}
  {inj : ∀ a : A, g a ~{C}~> q} (H : IsIndexedCoproduct g q inj)
  {c c' : C} (h : c ~{C}~> c') (u : q ~{C}~> c) (a : A) :
  to (cohom_icoprod_iso c' H) (h ∘ u) a ≈ h ∘ to (cohom_icoprod_iso c H) u a.
Proof.
  rewrite (cohom_icoprod_iso_to c' H (h ∘ u) a).
  rewrite (cohom_icoprod_iso_to c H u a).
  now rewrite comp_assoc.
Qed.

(** * G. The issue's names, and Mac Lane's Remark 1 on universes *)

(* The issue's two pinned names, as aliases of #331's theorems.  ANNOTATED
   (measured; see the header): written bare they minimize. *)
Definition hom_preserves_limits {C : Category} (c : C) :
  ContinuousFunctor (@HomFrom C c) := hom_ContinuousFunctor c.

Definition cohom_carries_colimits_to_limits {C : Category} (c : C)
  {J : Category} {K : J ⟶ C} (N : Cocone K) (HN : IsColimitCocone N) :
  IsLimitCone (FCone (HomTo c) N) := cohom_colimit_to_limit c N HN.

(* Remark 1, as far as the tree supports it: the RELATION level of the
   target [Sets] is free above the carrier level, so the hom-functor of a
   category at hom level [h] is continuous into [Sets@{h s}] for every
   [s > h].  The CARRIER level is pinned to [h] (probe N2). *)
Definition HomFrom_at@{o h s +} {C : Category@{o h h}} (c : C) :
  C ⟶ Sets@{h s} := @HomFrom C c.

Definition hom_continuous_at@{o h s +} {C : Category@{o h h}} (c : C) :
  ContinuousFunctor (@HomFrom_at C c : C ⟶ Sets@{h s}) :=
  hom_ContinuousFunctor c.
