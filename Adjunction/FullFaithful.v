Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Transfer.
Require Import Category.Adjunction.Fullness.

Generalizable All Variables.

(** * Mac Lane §IV.3 Theorem 1: fullness and faithfulness through ε *)

(* SOURCES.

   Mac Lane, CWM 2nd ed., §IV.3, printed p. 90, read from the page image
   p367-099.png.  The paragraph opening the section:

     "For many of the forgetful functors U : A → X listed in §2, the
      counit ε : F U ⇸ I_A of the adjunction assigns to each a ∈ A the
      epimorphism ε_a : F(U a) → a which gives the standard
      representation of a as a quotient of a free object.  This is a
      general fact: Whenever a right adjoint G is faithful, every counit
      ε_a of the adjunction is epi."

   and the theorem itself, same image:

     "Theorem 1.  For an adjunction ⟨F, G, η, ε⟩ : X ⇀ A: (i) G is
      faithful if and only if every component ε_a of the counit ε is
      epi, (ii) G is full if and only if every ε_a is a split monic.
      Hence G is full and faithful if and only if each ε_a is an
      isomorphism F G a ≅ a."

   followed by "The proof depends on a lemma."  That lemma is
   maclane:IV.3:lem1, delivered in Functor/Hom/Transfer.v; its statement
   and proof are quoted in that file's header from p367-100.png.

   The proof of the theorem, printed p. 91 (image p367-100.png):

     "Now we prove the theorem.  Apply the Yoneda Lemma to the natural
      transformation (arrow function of G followed by the adjunction)

          A(a, c) --G_{a,c}--> X(G a, G c) --φ⁻¹--> A(F G a, c).

      It is determined (set c = a) by the image of 1 : a → a, which is
      exactly the definition of the counit ε_a : F G a → a.  But φ⁻¹ is
      an isomorphism, hence this natural transformation is monic or epi,
      respectively, when every G_{a,c} is injective or surjective,
      respectively; that is, when G is faithful or full, respectively.
      The result now follows by the lemma."

   Exercise 5, printed p. 92 (image p367-101.png):

     "Given an adjunction ⟨F, G, φ⟩ : X ⇀ A, prove that G is faithful if
      and only if φ⁻¹ carries epis to epis."

   Riehl, Category Theory in Context, 2nd ed., §4.6, printed p. 169, read
   from the page image r367-189.png.  Lemma 4.6.11, for an adjunction
   with F : C → D on top and G : D → C below and counit ε : FG ⇒ id_D:

     "(i) G is faithful if and only if each component of ε is an
      epimorphism.  (ii) G is full if and only if each component of ε is
      a split monomorphism.  (iii) G is full and faithful if and only if
      ε is an isomorphism.
      Dually, writing η : id_C ⇒ GF for the unit:
      (i) F is faithful if and only if each component of η is a
      monomorphism.  (ii) F is full if and only if each component of η is
      a split epimorphism.  (iii) F is full and faithful if and only if
      η is an isomorphism."

   Its proof is deferred to Exercise 4.6.ix, printed p. 172 (image
   r367-192.png), whose entire text is "Prove Lemma 4.6.11."

   Catalog ids: maclane:IV.3:thm1, maclane:IV.3:lem1, maclane:IV.3:ex5,
   riehl:4.6:lem11, riehl:4.6:exix.

   CONVENTION MAP.  This library writes an adjunction `A : F ⊣ U` with
   `F : D ⟶ C` the LEFT adjoint and `U : C ⟶ D` the RIGHT adjoint
   (Theory/Adjunction.v:133).  So Mac Lane's G is this file's U, his F is
   F, his A is C and his X is D; Riehl's G is likewise U and her C is D.
   The transposes are ⌊−⌋ (Mac Lane's φ) and ⌈−⌉ (his φ⁻¹); the unit is
   `unit x = ⌊id⌋ : x ~> U (F x)` (:217) and the counit is
   `counit a = ⌈id⌉ : F (U a) ~> a` (:218).  Both notations, and ⌊−⌋/⌈−⌉,
   are SECTION-LOCAL in Theory/Adjunction.v and do not export, so they are
   re-declared here; as #368 measured, `Notation "'ε'"` with no argument
   re-inserts the implicit object and is rejected with "Illegal
   application", which is why the two notations below take the object
   explicitly.

   WHAT IS DELIVERED AND AT WHAT STRENGTH.

   Over an ARBITRARY adjunction `A : F ⊣ U` between arbitrary categories
   — not over a subcategory inclusion, which is this issue's reviewer
   check — all six clauses of Riehl's lemma, each as a genuine
   biconditional with both directions proved (the two (iii)'s in their
   COMPONENTWISE reading, ε and η an isomorphism at every component —
   Mac Lane's own phrasing; ε as an isomorphism IN the functor category
   is NOT DELIVERED, see below), and all of them [Defined]
   rather than [Qed] because every one of them carries data in at least
   one direction:

   (i)   [right_adjoint_faithful_iff_counit_epic]
             : Faithful U ↔ (∀ a, Epic (ε a))
   (ii)  [right_adjoint_full_iff_counit_split_monic]
             : Full U ↔ (∀ a, Section (ε a))
   (iii) [right_adjoint_fully_faithful_iff_counit_iso]
             : (Full U * Faithful U) ↔ (∀ a, IsIsomorphism (ε a))
   (iv)  [left_adjoint_faithful_iff_unit_monic]
             : Faithful F ↔ (∀ x, Monic (η x))
         [left_adjoint_full_iff_unit_split_epic]
             : Full F ↔ (∀ x, Retraction (η x))
         [left_adjoint_fully_faithful_iff_unit_iso]
             : (Full F * Faithful F) ↔ (∀ x, IsIsomorphism (η x))

   plus Mac Lane's Exercise 5 in the book's orientation,
   [right_adjoint_faithful_iff_from_adj_epic].

   "Split monic" is the library's [Section] (Theory/Morphisms.v:56,
   aliased [SplitMono] at :130) — a chosen LEFT inverse carried as data —
   and NOT [Monic]; "split epi" is [Retraction] (:70, aliased [SplitEpi]
   at :129).  The three dual clauses are stated COVARIANTLY: no `^op`
   occurs in any of their types, so a consumer holding a left adjoint
   uses them directly.

   ROUTE.  Mac Lane's, and the transfer lemma is genuinely consumed
   rather than cited.  The bridge is [fmap_to_adj_counit]
   (Theory/Adjunction.v:306), `fmap[U] f ≈ ⌊f ∘ ε⌋`, which says that
   Mac Lane's displayed composite

       A(a, c) --U--> D(U a, U c) --φ⁻¹--> C(F U a, c)

   IS precomposition with ε_a: applying ⌈−⌉ to both sides and cancelling
   with [to_adj_comp_law] gives [counit_precomp_is_from_adj_fmap_U],
   `g ∘ ε a ≈ ⌈fmap[U] g⌉`, and that composite is on the nose the
   component of [hom_transfer (ε a)] at c
   ([transfer_at_counit_is_precomp], an [eq_refl] Example).  Since ⌈−⌉ is
   a bijection ("But φ⁻¹ is an isomorphism"), U's arrow map is injective
   at every (a, c) exactly when that component is, and surjective exactly
   when it is.  So:

     Faithful U  ⟺  every [hom_transfer (ε a)] is monic in [C, Sets]
                 ⟺  every ε_a is [Epic]                      (lemma)
     Full U      ⟺  every [hom_transfer (ε a)] is epic in [C, Sets]
                 ⟺  every ε_a is a [Section]                 (lemma)

   Both directions of (i) and the backward direction of (ii) are proved
   exactly that way: [epic_of_hom_transfer_monic],
   [hom_transfer_monic_of_epic], [hom_transfer_epic_of_section] appear
   literally in the scripts.  The FORWARD direction of (ii) does not
   route through the lemma in the shipped biconditional — it CONSUMES
   #368's [counit_split_mono_of_full_right] (Adjunction/Fullness.v:347),
   which is that half already proved by a shorter argument (naturality of
   ε at the chosen preimage plus one triangle identity).  The transfer
   route for it is nevertheless built and shipped, as
   [counit_transfer_epic_of_full] and [counit_section_via_transfer], so
   Mac Lane's proof is present in all four directions; what is NOT
   claimed is that the two forward routes produce the same left inverse.
   They need not: two left inverses of a non-epi arrow are unrelated, and
   no comparison between them is proved (see NOT DELIVERED).

   PRIOR ART, and what is consumed versus restated.

   - Adjunction/Fullness.v (#368) supplies
     [counit_split_mono_of_full_right] (:347) and
     [unit_split_epi_of_full_left] (:370), the forward halves of (ii) and
     of its dual, and [unit_iso_of_full_monic] (:603), "split epi +
     monic ⟹ invertible" packaged for the unit.  All three are CONSUMED.
     Its [reflective_fmap_counit_IsIsomorphism] (:682) and
     [equiv_fmap_counit_IsIsomorphism] (:709) are SIBLINGS, not
     duplicates: they are about `U ε`, the WHISKERED counit, which is
     invertible under fullness of EITHER adjoint, where (iii) here is
     about ε itself and needs fullness and faithfulness of the right one.
   - Instance/Coq/Monoid/Free.v:476 [adjunction_counit_epic] already
     proves the forward half of (i), for an ARBITRARY adjunction, inside
     `Section AdjunctionCounit` (:456-462); :465
     [adjunction_counit_underlying_retraction] is `U ε` split by the
     unit.  Both predate this file.  The forward half of (i) is RESTATED
     here rather than consumed, and the reason is closure, not novelty:
     that constant lives in the `Instance/Coq` layer, and its proof is a
     different one (it transports the cancellation through U using the
     triangle identity, where the proof here goes through the transfer
     lemma).  The identity of the two STATEMENTS is machine-checked in
     Test/ProbeFullFaithful367.v, which [Check]s both at one type.
     The issue's claim that "a whole-tree inspection of every [Epic]
     occurrence finds none touching a counit" is therefore FALSE at
     commit 418e970a; see CORRECTIONS.
   - Theory/Adjunction.v:314 [adj_monic] is the only meeting of
     faithfulness with an adjunction in Theory/Adjunction.v itself (its
     sole [Faithful] mention is :315); other files meet the two as well
     (Monad/Lifting.v:508, Theory/Equivalence/Adjoint.v:128 among them),
     and none of those is consumed here.  [adj_monic] IS consumed, at the
     opposite adjunction, to give the forward half of Exercise 5 — which
     is the issue's request that the two be "visibly the same fact".
   - Functor/Hom/Induced.v:144/:161 ([hom_action_faithful_iff],
     [hom_action_full_iff]) say faithfulness and fullness are injectivity
     and surjectivity of the arrow map, packaged as one natural
     transformation.  That is the first step of Mac Lane's proof, and it
     is cited rather than consumed: the [Faithful] and [Full] classes are
     already stated as injectivity and as a section of [fmap]
     (Theory/Functor.v:343/:332), so nothing is gained by the detour and
     one module of closure is saved.
   - Construction/Reflective.v:92 [reflective_counit_iso] and
     Construction/Reflective/Idempotent.v:175 [reflective_counit_IsIso]
     are the special case the issue names.  Section (E) below re-derives
     the conclusion from (iii); the comparison with the existing lemma is
     BLOCKED and the obstruction is measured, see DONOR DEFECT.

   CORRECTIONS to the issue text (each checked at commit 418e970a).

   - "a whole-tree inspection of every [Epic] occurrence finds none
     touching a counit" is false: `rg -n 'Epic' Instance/Coq/Monoid/Free.v`
     returns [adjunction_counit_epic] at :476, whose conclusion is
     `Epic (counit x)`.
   - Its line numbers for the donors are off by one or two throughout,
     because they point at the comment or the [Proof] line rather than at
     the declaration: [adj_monic] is Theory/Adjunction.v:314, not :311
     (:311 is inside the preceding proof); the [Full] and [Faithful]
     classes are Theory/Functor.v:332 and :343, not :331/:342 (those are
     comment lines); [Yoneda_Lemma], [Covariant_Yoneda_Lemma] and
     [Yoneda_Embedding] are Functor/Hom/Yoneda.v:157, :206 and :255, not
     :133/:182/:231/:253; and [Section], [Retraction], [Epic], [Monic]
     are Theory/Morphisms.v:56, :70, :107 and :119 with the aliases
     [SplitEpi]/[SplitMono] at :129/:130, not :104/:126/:127.
   - "there are no [Monic]/[Epic] occurrences in Functor/Hom.v, ...,
     Instance/Fun.v" was true of Instance/Fun.v but is now beside the
     point: Instance/Fun/Morphisms.v (#369) is exactly that development
     and this file consumes it through the transfer lemma.

   DONOR DEFECT.  [reflective_counit_iso] (Construction/Reflective.v:92)
   produces DATA — an [Isomorphism] — and is closed with [Qed] (:115).
   The whole term is therefore opaque, so `to (reflective_counit_iso R x)`
   does not reduce to the counit even though the proof script supplies it
   as exactly that, and no equation naming any of its four fields is
   available by conversion.  Both the [eq_refl] and the [≈] comparison
   with section (E)'s derivation are consequently unavailable; the
   [eq_refl] one is pinned as a CONVERSION negative in the probe.  The
   donor is NOT modified here.

   ENGINEERING FINDINGS.

   - Requiring Category.Adjunction.Opposite installs
     `Notation "N ^op" := (@Opposite_Adjunction _ _ _ _ N)` and OPENS
     [adjunction_scope] globally, so after that point a bare `X^op` on a
     CATEGORY can elaborate as an opposite ADJUNCTION.  That Require is
     therefore deferred to just before section (D), and every opposite is
     written by name — [Opposite C], [Opposite_Functor F],
     [Opposite_Adjunction F U A] — throughout.
   - Construction/Subcategory.v exports its own [Full] (first argument a
     [Category]), which shadows [Theory/Functor.v]'s.  Sections (A)-(D)
     therefore say [Full] meaning the functor class, and section (E),
     which needs both, says [Functor.Full] and
     [Construction.Subcategory.Full] — the idiom Adjunction/Fullness.v
     uses at its own :661.
   - [Epic_Section_Iso] (Theory/Isomorphism.v:418) yields an
     object-level [Isomorphism], not the predicate [IsIsomorphism] that
     (iii) is stated with.  The repackaging [Epic_Section_IsIsomorphism]
     below CONSUMES it for the one law that is not already a field of
     [Section], so no cancellation argument is repeated.

   NOT DELIVERED.

   - No comparison between the two forward routes for (ii): the section
     produced by [counit_section_via_transfer] and the one produced by
     [counit_split_mono_of_full_right] are not claimed equal at any
     grade, and in general they cannot be — two left inverses of an arrow
     that is not epi need not agree.
   - No generalization of Construction/Localization.v:184
     [unit_at_local_iso].  The issue's appended note observes that it
     never uses W-locality; that observation is neither used nor acted on
     here, and that file is not required.
   - No naturality statement: the counit is treated componentwise
     throughout, and nothing says that ε being a componentwise
     isomorphism makes it an isomorphism in the functor category (that
     would be Instance/Fun/Morphisms.v's [nat_iso_iff_pointwise] applied
     to `F ◯ U ⟹ Id`, which is not built here).
   - No statement about when U REFLECTS or CREATES anything, no
     [AdjointEquivalence] corollary, and no relation to
     Theory/Equivalence/Adjoint.v:73 ([adj_equiv_counit_iso], where an
     adjoint equivalence carries its counit isomorphism as a FIELD; (iii)
     here DERIVES such an isomorphism from fullness and faithfulness, and
     the two are not connected).
   - Nothing is registered as an [Instance]; every result is a plain
     [Definition], [Lemma] or [Example].
   - No witness in this file: the non-vacuity witnesses for both
     quadrants live in Test/ProbeFullFaithful367.v, so that the two
     library files stay lean (measured: adding the witnesses would pull
     Instance/Sets/Pointed.v and its closure into every consumer of the
     theorem). *)

(* ------------------------------------------------------------------ *)
(** ** A packaging lemma: split monic + epi ⟹ invertible *)

(* Theory/Isomorphism.v:418's [Epic_Section_Iso] already runs the
   cancellation argument, but it concludes with the object-level
   [Isomorphism].  This repackages it as the predicate [IsIsomorphism]
   that Theorem 1(iii) is stated with, reusing that instance for the one
   law ([f ∘ section ≈ id]) that [Section] does not carry as a field;
   the other law IS [section_comp]. *)

Definition Epic_Section_IsIsomorphism {E : Category} {x y : E}
           {f : x ~> y} (s : Section f) (e : Epic f) : IsIsomorphism f :=
  {| two_sided_inverse := @section E x y f s
   ; is_right_inverse  := iso_to_from (@Epic_Section_Iso E x y f s e)
   ; is_left_inverse   := @section_comp E x y f s |}.

Section FullFaithful.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Notation "'η' x" := (@unit C D F U A x)
  (at level 9, only parsing).
Notation "'ε' x" := (@counit C D F U A x)
  (at level 9, only parsing).
Notation "⌊ f ⌋" := (to (@adj C D F U A _ _) f) (only parsing).
Notation "⌈ f ⌉" := (from (@adj C D F U A _ _) f) (only parsing).

(* ------------------------------------------------------------------ *)
(** ** (A) The bridge: Mac Lane's composite is precomposition with ε *)

(* "Apply the Yoneda Lemma to the natural transformation (arrow function
   of G followed by the adjunction) A(a,c) → X(Ga,Gc) → A(FGa,c)."  Read
   in this library's vocabulary that composite is
   `g ↦ ⌈fmap[U] g⌉`, and the identification below says it is
   precomposition with ε_a.  It is one rewrite of [fmap_to_adj_counit]
   followed by one cancellation. *)

Lemma counit_precomp_is_from_adj_fmap_U {a c : C} (g : a ~> c) :
  g ∘ ε a ≈ ⌈ fmap[U] g ⌉.
Proof.
  rewrite (@fmap_to_adj_counit C D F U A a c g).
  symmetry.
  exact (@to_adj_comp_law C D F U A (U a) c (g ∘ ε a)).
Qed.

(* ... and the composite IS the component of the transfer transformation
   at ε_a, on the nose.  Deliberate strictness: this is what makes the
   transfer lemma applicable without a comparison map. *)

Example transfer_at_counit_is_precomp {a c : C} (g : a ~> c) :
  transform[hom_transfer (ε a)] c g = g ∘ ε a := eq_refl.

(* The other orientation, for readers who prefer Mac Lane's arrow: U's
   arrow map is the transfer followed by the forward transpose. *)

Lemma fmap_U_is_transfer_then_transpose {a c : C} (g : a ~> c) :
  fmap[U] g ≈ ⌊ transform[hom_transfer (ε a)] c g ⌋.
Proof. exact (@fmap_to_adj_counit C D F U A a c g). Qed.

(* ------------------------------------------------------------------ *)
(** ** (B) Theorem 1 (i): faithful ⟺ every counit component is epi *)

(* Faithfulness makes every component of the transfer at ε_a injective:
   two arrows out of a agreeing after ε_a have the same U-image, by the
   bridge, hence are equal. *)

Definition counit_transfer_monic_of_faithful (HU : Faithful U) (a : C) :
  @Monic ([C, Sets]) _ _ (hom_transfer (ε a)).
Proof.
  apply pointwise_monic_is_monic; intro c.
  apply (fst (injectivity_is_monic (transform[hom_transfer (ε a)] c))).
  intros g1 g2 Heq.
  assert (Heq' : g1 ∘ ε a ≈ g2 ∘ ε a) by exact Heq.
  apply (@fmap_inj C D U HU a c).
  rewrite (@fmap_to_adj_counit C D F U A a c g1).
  rewrite (@fmap_to_adj_counit C D F U A a c g2).
  now rewrite Heq'.
Defined.

(* ... and the lemma turns that into epicness of ε_a. *)

Definition counit_epic_of_faithful (HU : Faithful U) (a : C) :
  Epic (ε a) :=
  epic_of_hom_transfer_monic (ε a)
    (counit_transfer_monic_of_faithful HU a).

(* Conversely, epicness of every ε_a makes U faithful: the lemma turns it
   into monicity of the transfer, hence injectivity of each component,
   and the bridge carries `fmap[U] f ≈ fmap[U] g` to
   `f ∘ ε ≈ g ∘ ε`. *)

Definition faithful_of_counit_epic (H : ∀ a : C, Epic (ε a)) :
  Faithful U.
Proof.
  constructor; intros x y f g Hfg.
  apply (snd (injectivity_is_monic (transform[hom_transfer (ε x)] y))
             (sets_functor_monic_pointwise (hom_transfer (ε x))
                (hom_transfer_monic_of_epic (ε x) (H x)) y) f g).
  change (f ∘ ε x ≈ g ∘ ε x).
  rewrite (counit_precomp_is_from_adj_fmap_U f).
  rewrite (counit_precomp_is_from_adj_fmap_U g).
  now rewrite Hfg.
Defined.

Definition right_adjoint_faithful_iff_counit_epic :
  Faithful U ↔ (∀ a : C, Epic (ε a)).
Proof.
  split.
  - exact counit_epic_of_faithful.
  - exact faithful_of_counit_epic.
Defined.

(* ------------------------------------------------------------------ *)
(** ** (C) Theorem 1 (ii): full ⟺ every counit component is split monic *)

(* Mac Lane's route for the forward direction: fullness makes every
   component of the transfer SURJECTIVE, the preimage of k being the
   U-preimage of its transpose.  Shipped even though the headline's
   forward half consumes the cheaper #368 donor, so that the book's proof
   is present in all four directions. *)

Definition counit_transfer_epic_of_full (HU : Full U) (a : C) :
  @Epic ([C, Sets]) _ _ (hom_transfer (ε a)).
Proof.
  apply pointwise_epic_is_epic; intro c.
  apply (fst (surjectivity_is_epic (transform[hom_transfer (ε a)] c))).
  intro k.
  exists (@prefmap C D U HU a c ⌊k⌋).
  change (@prefmap C D U HU a c ⌊k⌋ ∘ ε a ≈ k).
  rewrite (counit_precomp_is_from_adj_fmap_U
             (@prefmap C D U HU a c ⌊k⌋)).
  rewrite (@fmap_sur C D U HU a c ⌊k⌋).
  exact (@to_adj_comp_law C D F U A (U a) c k).
Defined.

Definition counit_section_via_transfer (HU : Full U) (a : C) :
  Section (ε a) :=
  section_of_hom_transfer_epic (ε a) (counit_transfer_epic_of_full HU a).

(* The backward direction, through the lemma: a left inverse of ε_a makes
   the transfer epic, hence every component surjective, and the preimage
   of ⌈g⌉ is a U-preimage of g. *)

Definition full_data_of_counit_section (H : ∀ a : C, Section (ε a))
           {x y : C} (g : U x ~> U y) : { h : x ~> y & fmap[U] h ≈ g }.
Proof.
  destruct (epic_implies_surjective
              (transform[hom_transfer (ε x)] y)
              (sets_functor_epic_pointwise (hom_transfer (ε x))
                 (hom_transfer_epic_of_section (ε x) (H x)) y)
              ⌈g⌉) as [h Hh].
  exists h.
  assert (Hh' : h ∘ ε x ≈ ⌈g⌉) by exact Hh.
  rewrite (@fmap_to_adj_counit C D F U A x y h).
  rewrite Hh'.
  exact (@from_adj_comp_law C D F U A (U x) y g).
Defined.

Definition full_of_counit_section (H : ∀ a : C, Section (ε a)) : Full U :=
  {| prefmap := fun x y g => `1 (full_data_of_counit_section H g)
   ; fmap_sur := fun x y g => `2 (full_data_of_counit_section H g) |}.

Definition right_adjoint_full_iff_counit_split_monic :
  Full U ↔ (∀ a : C, Section (ε a)).
Proof.
  split.
  - exact (fun HU a => @counit_split_mono_of_full_right C D F U A HU a).
  - exact full_of_counit_section.
Defined.

(* ------------------------------------------------------------------ *)
(** ** (D) Theorem 1, conclusion: fully faithful ⟺ ε invertible *)

Definition right_adjoint_fully_faithful_iff_counit_iso :
  (Full U * Faithful U)%type ↔ (∀ a : C, IsIsomorphism (ε a)).
Proof.
  split.
  - intros [HFull HFaith] a.
    exact (Epic_Section_IsIsomorphism
             (@counit_split_mono_of_full_right C D F U A HFull a)
             (counit_epic_of_faithful HFaith a)).
  - intros H.
    split.
    + apply full_of_counit_section; intro a.
      exact {| section      := @two_sided_inverse C _ _ _ (H a)
             ; section_comp := @is_left_inverse C _ _ _ (H a) |}.
    + apply faithful_of_counit_epic; intro a.
      constructor; intros z g1 g2 Heq.
      rewrite <- (id_right g1), <- (id_right g2).
      rewrite <- (@is_right_inverse C _ _ _ (H a)).
      rewrite !comp_assoc.
      now rewrite Heq.
Defined.

(* ------------------------------------------------------------------ *)
(** ** (E) Mac Lane §IV.3 Exercise 5: the pin and a direct control *)

(* "prove that G is faithful if and only if φ⁻¹ carries epis to epis."
   φ⁻¹ is ⌈−⌉.  The BACKWARD direction is the cheap one: id is epi, and
   ⌈id⌉ IS the counit by definition (Theory/Adjunction.v:218), so (i)
   applies.  The identity `⌈id⌉ = ε a` is pinned as an [eq_refl] Example
   below.

   The exercise's biconditional [right_adjoint_faithful_iff_from_adj_epic]
   and the FORWARD half it rests on are NOT here but in section (F): the
   derivation the issue asks for reads [adj_monic] at the opposite
   adjunction, and [Opposite_Adjunction] is not in scope until the Require
   that opens (F).  What section (E) supplies is the definitional pin and
   a direct proof of the forward half, shipped as a control so that the
   opposite-adjunction derivation is not the only route in the file.  The
   two forward proofs are NOT compared: [Epic] is a one-field record whose
   field is a proof, so an [eq_refl] between them is refuted for the
   uninformative reason that the two proof terms differ, and there is no
   setoid on [Epic] in which to state anything weaker. *)

Example from_adj_id_is_counit (a : C) : ⌈ id[U a] ⌉ = ε a := eq_refl.

(* A direct proof of the forward direction, shipped as a control for the
   derivation that follows: transpose the cancellation hypothesis with
   [to_adj_nat_r], cancel the epi f, and finish with faithfulness. *)

Definition from_adj_epic_of_epic_direct (HU : Faithful U)
           {x : D} {a : C} (f : x ~> U a) (Hf : Epic f) : Epic ⌈f⌉.
Proof.
  constructor; intros c g h Heq.
  apply (@fmap_inj C D U HU a c).
  apply (@epic D x (U a) f Hf (U c)).
  assert (Hg : fmap[U] g ∘ f ≈ ⌊ g ∘ ⌈f⌉ ⌋).
  { rewrite (@to_adj_nat_r C D F U A x a c g ⌈f⌉).
    now rewrite (@from_adj_comp_law C D F U A x a f). }
  assert (Hh : fmap[U] h ∘ f ≈ ⌊ h ∘ ⌈f⌉ ⌋).
  { rewrite (@to_adj_nat_r C D F U A x a c h ⌈f⌉).
    now rewrite (@from_adj_comp_law C D F U A x a f). }
  rewrite Hg, Hh.
  exact (@to_adj_respects C D F U A x c _ _ Heq).
Defined.

End FullFaithful.

(* ------------------------------------------------------------------ *)
(** ** (F) Riehl's dual clauses, and Exercise 5's biconditional *)

(* Everything below the Require needs [Opposite_Adjunction]: Riehl's three
   dual clauses instantiate (i)-(iii) at it, and Mac Lane's Exercise 5
   reads [adj_monic] at it.  The three dual clauses are obtained by
   instantiating (i)-(iii) at the opposite adjunction.  Two definitional
   coincidences make that free, and both are recorded below at [eq_refl]:

       counit (Opposite_Adjunction F U A) x  =  unit A x
       unit   (Opposite_Adjunction F U A) a  =  counit A a

   — because `unit := ⌊id⌋` and `counit := ⌈id⌉` while the opposite
   adjunction is built by swapping [to] and [from] of the very same
   isomorphism (Adjunction/Opposite.v:34).  #368 measured this out of
   tree and pinned it nowhere; it is pinned here, and again in the probe.

   The remaining transport is the Monic/Epic and Section/Retraction
   quartets of Theory/Morphisms/Duality.v (:44-:56 and :142-:166), and
   [Full_op]/[Faithful_op]/[Full_of_op]/[Faithful_of_op] of
   Functor/Opposite.v (:68-:87).  Six of those twelve are record literals
   with no proof content — the Monic/Epic quartet, which is what
   Duality.v:38's "one constructor application" sentence covers, and the
   two [Faithful] passages; the other six ([op_Retraction_of_Section]
   and its three siblings, [Full_op], [Full_of_op]) are [Program
   Definition]s whose single obligation is an [exact] of the other
   side's law at the swapped indices (Functor/Opposite.v:63-64 says so
   of its own two).  None runs an argument of its own, so the dual
   clauses cost no argument here: no direct proof is cheaper and none is
   shipped.

   NOTATION HAZARD.  This Require is deferred to here on purpose; see
   ENGINEERING FINDINGS in the header. *)

Require Import Category.Adjunction.Opposite.

Section Duals.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Notation "'η' x" := (@unit C D F U A x)
  (at level 9, only parsing).
Notation "'ε' x" := (@counit C D F U A x)
  (at level 9, only parsing).
Notation "⌊ f ⌋" := (to (@adj C D F U A _ _) f) (only parsing).
Notation "⌈ f ⌉" := (from (@adj C D F U A _ _) f) (only parsing).

(* The two definitional coincidences, at Leibniz equality. *)

Example op_counit_is_unit (x : D) :
  @counit (Opposite D) (Opposite C) (Opposite_Functor U)
          (Opposite_Functor F) (Opposite_Adjunction F U A) x
  = η x := eq_refl.

Example op_unit_is_counit (a : C) :
  @unit (Opposite D) (Opposite C) (Opposite_Functor U)
        (Opposite_Functor F) (Opposite_Adjunction F U A) a
  = ε a := eq_refl.

(* Riehl 4.6.11 dual (i): F faithful ⟺ every unit component is monic. *)

Definition left_adjoint_faithful_iff_unit_monic :
  Faithful F ↔ (∀ x : D, Monic (η x)).
Proof.
  pose proof (@right_adjoint_faithful_iff_counit_epic
                (Opposite D) (Opposite C) (Opposite_Functor U)
                (Opposite_Functor F) (Opposite_Adjunction F U A)) as H.
  split.
  - intros HF x.
    exact (Monic_of_op_Epic (η x) (fst H (Faithful_op HF) x)).
  - intros Hm.
    apply (@Faithful_of_op D C F).
    apply (snd H); intro x.
    exact (op_Epic_of_Monic (η x) (Hm x)).
Defined.

(* Riehl 4.6.11 dual (ii): F full ⟺ every unit component is a split epi.
   The forward half is #368's [unit_split_epi_of_full_left] read through
   the opposite adjunction; the two are compared below. *)

Definition left_adjoint_full_iff_unit_split_epic :
  Full F ↔ (∀ x : D, Retraction (η x)).
Proof.
  pose proof (@right_adjoint_full_iff_counit_split_monic
                (Opposite D) (Opposite C) (Opposite_Functor U)
                (Opposite_Functor F) (Opposite_Adjunction F U A)) as H.
  split.
  - intros HF x.
    exact (Retraction_of_op_Section (η x) (fst H (Full_op HF) x)).
  - intros Hr.
    apply (@Full_of_op D C F).
    apply (snd H); intro x.
    exact (op_Section_of_Retraction (η x) (Hr x)).
Defined.

(* The op route's right inverse for η_x IS #368's, on the nose: the
   opposite adjunction's counit at x is η x, [Full_op]'s [prefmap] is the
   original's at swapped indices, and [Opposite_Functor U] applied to F x
   is U (F x) — so both sides reduce to
   `prefmap F HF (U (F x)) x (ε (F x))`. *)

Example unit_retract_agrees (HF : Full F) (x : D) :
  @retract D x (U (F x)) (η x)
    (fst left_adjoint_full_iff_unit_split_epic HF x)
  = @retract D x (U (F x)) (η x)
    (@unit_split_epi_of_full_left C D F U A HF x) := eq_refl.

(* Riehl 4.6.11 dual (iii): F fully faithful ⟺ η is an isomorphism.  The
   forward half CONSUMES #368's [unit_iso_of_full_monic] (:603) rather
   than re-running the split-plus-cancellation argument. *)

Definition left_adjoint_fully_faithful_iff_unit_iso :
  (Full F * Faithful F)%type ↔ (∀ x : D, IsIsomorphism (η x)).
Proof.
  split.
  - intros [HFull HFaith] x.
    exact (@unit_iso_of_full_monic C D F U A HFull
             (fst left_adjoint_faithful_iff_unit_monic HFaith) x).
  - intros H.
    split.
    + apply (snd left_adjoint_full_iff_unit_split_epic); intro x.
      exact {| retract      := @two_sided_inverse D _ _ _ (H x)
             ; retract_comp := @is_right_inverse D _ _ _ (H x) |}.
    + apply (snd left_adjoint_faithful_iff_unit_monic); intro x.
      constructor; intros z g1 g2 Heq.
      rewrite <- (id_left g1), <- (id_left g2).
      rewrite <- (@is_left_inverse D _ _ _ (H x)).
      rewrite <- !comp_assoc.
      now rewrite Heq.
Defined.

(* ... and the derivation the issue asks for: the SAME fact is
   [adj_monic] (Theory/Adjunction.v:314) read at the opposite adjunction.
   At `Opposite_Adjunction F U A` the left adjoint is [Opposite_Functor U],
   so `Faithful F` there is `Faithful U` here (through [Faithful_op]),
   `Monic f` there is `Epic f` here (through [op_Monic_of_Epic]), the
   forward transpose ⌊−⌋ there is ⌈−⌉ here, and composition is reversed —
   so the conclusion `⌊f⌋ ∘ g ≈ ⌊f⌋ ∘ h → g ≈ h` reads, in C, as
   `g ∘ ⌈f⌉ ≈ h ∘ ⌈f⌉ → g ≈ h`, which is [Epic ⌈f⌉].  Every OTHER step
   is a conversion: the script is `constructor; intros` and one [exact],
   whose only non-conversion content is those two transports. *)

Definition from_adj_epic_of_epic (HU : Faithful U)
           {x : D} {a : C} (f : x ~> U a) (Hf : Epic f) : Epic ⌈f⌉.
Proof.
  constructor; intros c g h Heq.
  exact (@adj_monic (Opposite D) (Opposite C) (Opposite_Functor U)
           (Opposite_Functor F) (Opposite_Adjunction F U A)
           a x f c g h (Faithful_op HU) (op_Monic_of_Epic f Hf) Heq).
Defined.

Definition right_adjoint_faithful_iff_from_adj_epic :
  Faithful U
    ↔ (∀ (x : D) (a : C) (f : x ~> U a), Epic f → Epic ⌈f⌉).
Proof.
  split.
  - intros HU x a f Hf. exact (from_adj_epic_of_epic HU f Hf).
  - intros H.
    apply (@faithful_of_counit_epic C D F U A); intro a.
    exact (H (U a) a id (@id_epic D (U a))).
Defined.

End Duals.

(* ------------------------------------------------------------------ *)
(** ** (G) The reflective special case, as a corollary *)

(* Mac Lane, printed p. 91 (image p367-100.png), immediately after the
   proof of Theorem 1:

     "A subcategory A of B is called reflective in B when the inclusion
      functor K : A → B has a left adjoint F : B → A. ...  Since the
      inclusion functor K is always faithful, the counit ε of a
      reflection is always epi. ...  If a full subcategory A ⊂ B is
      reflective in B, then by Theorem 1 each object a ∈ A is isomorphic
      to F K a, and hence R a ≅ a for all a."

   That is exactly Construction/Reflective.v:92's [reflective_counit_iso],
   and here it becomes a corollary: the inclusion is faithful
   ([Incl_Faithful], Construction/Subcategory.v:89) and full as a functor
   whenever the subcategory is full ([Full_Implies_Full_Functor], :104),
   so (iii) applies.

   Two facts about the inclusion are used and nothing else; in
   particular no property of the reflector, and no subcategory-specific
   argument.  See DONOR DEFECT in the header for why the result cannot be
   compared field-by-field with the existing lemma. *)

Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

Definition reflective_incl_Full {C : Category} {S : Subcategory C}
           (R : Reflective S) : Functor.Full (Incl C S) :=
  @Full_Implies_Full_Functor C S (reflective_full R).

Definition reflective_incl_Faithful {C : Category} {S : Subcategory C}
           (R : Reflective S) : Functor.Faithful (Incl C S) :=
  @Incl_Faithful C S.

(* The general theorem, instantiated.  [Incl C S] is the RIGHT adjoint of
   the reflection, so this is (iii) verbatim. *)

Definition reflective_counit_IsIsomorphism_general {C : Category}
           {S : Subcategory C} (R : Reflective S) (x : Sub C S) :
  IsIsomorphism (@counit (Sub C S) C (reflector R) (Incl C S)
                   (reflective_adj R) x) :=
  fst (@right_adjoint_fully_faithful_iff_counit_iso
         (Sub C S) C (reflector R) (Incl C S) (reflective_adj R))
      (reflective_incl_Full R, reflective_incl_Faithful R) x.

(* The object-level reading, which is Mac Lane's own sentence "each
   object a ∈ A is isomorphic to F K a". *)

Definition reflective_counit_Isomorphism_general {C : Category}
           {S : Subcategory C} (R : Reflective S) (x : Sub C S) :
  reflector R (Incl C S x) ≅[Sub C S] x :=
  IsIsoToIso _ (reflective_counit_IsIsomorphism_general R x).

(* Faithfulness alone already gives Mac Lane's weaker sentence "the
   counit of a reflection is always epi", with no fullness hypothesis. *)

Definition reflection_counit_Epic {C : Category} {S : Subcategory C}
           (R : Reflective S) (x : Sub C S) :
  Epic (@counit (Sub C S) C (reflector R) (Incl C S)
          (reflective_adj R) x) :=
  counit_epic_of_faithful (reflective_incl_Faithful R) x.
