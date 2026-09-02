Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Two.

Generalizable All Variables.

(** * Pointwise monos and epis in a functor category *)

(* SOURCES

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.3,
   printed p. 91 (p. 100 of the PDF scan), the remark between the Lemma
   on representable transformations and its proof.  Read off a 300-dpi
   render of that page and quoted here verbatim, subscripts and all:

     "Observe, also, that for functors S, T : C→B, a natural
      transformation τ : S ⇸ T is epi (respectively, monic) in B^C if
      and only if every component τ_c : S_c → T_c is epi (respectively,
      monic) in B for B = Set; this follows by Exercise III.4.4,
      computing the pushout pointwise as in Exercise III.5.5."

   Catalog item maclane:IV.3:remark1.  Also covered: Awodey, "Category
   Theory", 1st ed. (Carnegie Mellon pre-print, September 2005), §7.10
   Exercise 6, printed p. 187 (PDF p. 196), item awodey:7:ex6 — show
   that a natural transformation is an isomorphism in the functor
   category exactly when each component is, and decide whether the
   analogous statement holds for monomorphisms.  That page is NOT in the
   Mac Lane scan, so the exercise is taken from the issue's own
   paraphrase rather than from the book, and this header says so rather
   than presenting it as a quotation.

   nLab: https://ncatlab.org/nlab/show/functor+category
   nLab: https://ncatlab.org/nlab/show/monomorphism
   nLab: https://ncatlab.org/nlab/show/epimorphism
   nLab: https://ncatlab.org/nlab/show/kernel+pair
   nLab: https://ncatlab.org/nlab/show/category+of+presheaves

   READ THE PRINTED SENTENCE PRECISELY.  Mac Lane states the
   BICONDITIONAL for B = Set and for no other target; the clause "for
   B = Set" governs the whole "if and only if".  So the split this file
   takes — an implication for an arbitrary target, a biconditional at
   Sets — is the print's own, not a hedge.  His stated route is the
   pointwise (co)limit computation, and that is the route taken here.

   WHAT IS DELIVERED, AND AT WHAT STRENGTH

   (A) For an ARBITRARY target D: [pointwise_monic_is_monic] and
       [pointwise_epic_is_epic].  Nothing in that section mentions Sets;
       the section binds only two categories, two functors and a
       transformation, and the two proofs consume exactly two in-tree
       facts about `[C, D]` — that its composition is componentwise
       ([nat_compose], Theory/Natural/Transformation.v:231, whose
       component at x is `f x ∘ g x`) and that its hom-setoid compares
       components pointwise ([Transform_Setoid], :139).  Both are
       definitional, so `Heq x` is already the equation in D that the
       component's cancellation property consumes, and neither proof
       rewrites anything.

   (B) For D = Sets: [sets_functor_monic_iff_pointwise] and
       [sets_functor_epic_iff_pointwise], genuine biconditionals, with
       the converse halves [sets_functor_monic_pointwise] and
       [sets_functor_epic_pointwise] available separately.  Section B
       binds D := Sets and nothing else; A and B are lexically separate
       so that no reader has to check whether the general statement
       leaked a Sets hypothesis.

   (C) Awodey's isomorphism half as a predicate on a GIVEN θ:
       [nat_iso_iff_pointwise], both directions [Defined], with
       [componentwise_iso] naming the backward construction and
       [nat_iso_pointwise] the forward one.

   (D) The presheaf corollaries: [presheaf_monic_iff_pointwise] and
       [presheaf_epic_iff_pointwise] are `:=` of (B) at C^op with no
       tactic, and [presheaf_monic_iff_injective] /
       [presheaf_epic_iff_surjective] spell out the [Instance/Sets]
       reading — monic in `[C^op, Sets]` exactly when every component is
       injective, epic exactly when every component is surjective.  These
       are the statements the subobject-classifier work wants to cite.

   THE MONOMORPHISM DECISION (Awodey's "decide whether the analogous
   statement holds").  Componentwise monic implies monic for EVERY
   target D — that is (A), with no hypothesis on D at all.  The converse
   is delivered at Sets, by (B), and the argument shows what it needs:
   it holds wherever the kernel pair of θ can be computed pointwise, and
   over Sets it can.  For an arbitrary D the converse is NOT proved
   here, and NO separating example is built, so nothing in this file
   licenses the sentence "the converse is false in general" — the honest
   report is that it is not established in general and that this file
   offers no countermodel.

   HOW THE Sets CONVERSE IS PROVED, AND WHAT HAD TO BE BUILT

   Mac Lane's route is the pointwise computation, and the two functors
   it needs did not exist.  Measured at bbddaee2, before this file was
   added: searches for `HasPullbacks (\[`, `HasPushouts (\[` and
   `kernel.?pair.*pointwise` over every `.v` file returned nothing (the
   third now matches this header's own prose and nothing else), and a
   wider sweep of every file that mentions both a functor category and
   a pullback, pushout or kernel-pair token finds only limits of a
   DIAGRAM into a category — Adjunction/Diagonal/Finite.v's
   [PullbackFunctor] : [Roof^op, C] ⟶ C — and the arrow-category
   [CokernelPairFunctor] : Arrow C ⟶ [Parallel, C] of
   Adjunction/CokernelPair.v, neither of them a (co)limit IN a functor
   category.  So no pullback, pushout or kernel pair at a functor
   category was declared, and the two are built here as named
   [Definition]s with their functor laws proved, since they, not the
   two biconditionals, are the reusable part:

     [KerPair θ] : C ⟶ Sets, object action x ↦ [sets_ker (θ x)] —
     Instance/Sets/Pullback.v:406's agreement sub-setoid
     {(a,b) | θ x a ≈ θ x b}, which is [sets_pb_obj (θ x) (θ x)] (:340)
     — with arrow action `(a, b) ↦ (fmap[F] f a, fmap[F] f b)`, and its
     two projection transformations [KerFst], [KerSnd].  Naturality of θ
     is exactly what makes the arrow action land back in the kernel
     pair: [ker_map_ok] is one use of [theta_nat] on each side of the
     given agreement.  [ker_agree] says θ ∙ KerFst ≈ θ ∙ KerSnd, whose
     proof is the second projection of the sigma; left cancellation then
     equates the two projections, which at the pair ((a,b); H) IS
     injectivity of θ x, and [injectivity_is_monic]
     (Instance/Sets.v:374) closes.

     [CokerPair θ] : C ⟶ Sets, object action x ↦ [CKSetoid (θ x)]
     (Instance/Sets.v:485), two copies of G x glued along the image of
     θ x, with arrow action the image of `fmap[G] f` in each copy, and
     its two injections [CkLeft], [CkRight].  Here naturality is what
     carries an image witness forward ([ck_Im_map]).  [ck_agree_nat] is
     [ck_agree] (:500) at each component; right cancellation equates the
     two injections, and reading the resulting relation at b gives the
     preimage, exactly as [epic_implies_surjective] (:532) does one
     level down; [surjectivity_is_epic] (:509) closes.

   Note what is NOT consumed: [sets_ck_IsCokernelPair]
   (Instance/Sets/CokernelPair.v:197) is the universal property of that
   cokernel pair, and the argument here needs only the commuting square
   [ck_agree], so that module is not required and the file's transitive
   closure stays at 39 modules.  The construction remains a cokernel
   pair pointwise; it is simply not the part being spent.

   A Yoneda/representable route (probe θ with [Curried_Hom C c],
   Functor/Hom.v:60) was NOT taken.  The reviewer check on this issue
   demands the pointwise-(co)limit computation, and that is what is
   delivered; the alternative was not measured either, so this file
   makes no claim about its cost.

   PRIOR ART, AND HOW (C) DIFFERS FROM IT

   [Functor_Setoid_Nat_Iso] (Instance/Fun.v:255) states
   `F ≅[Fun] G ↔ F ≈ G`.  That is the EXISTENTIAL form: it says the two
   functors are isomorphic, and the isomorphism it produces in the
   backward direction is the one it builds out of the given family.  It
   does not let a reader ask whether a PARTICULAR θ already in hand is
   invertible, which is what Awodey's exercise is about and what
   [nat_iso_iff_pointwise] supplies.  The two are related here rather
   than merely contrasted: [nat_iso_family] turns a componentwise family
   of inverses into the `F ≈ G` that theorem consumes, and both legs of
   the isomorphism it then builds agree with ours on their `transform`
   FIELDS at Leibniz equality — [equiv_iso_to_is_theta] and
   [equiv_iso_from_is_nat_inverse] are [eq_refl] pointwise, and the probe
   restates both as equalities of the whole transform functions — so the
   inverse [componentwise_iso] builds IS the inverse [equiv_iso] builds,
   as a function.  Neither whole LEG is the same record as ours, and
   neither is the whole isomorphism, and Test/ProbeMorphisms369.v pins
   all three: the donor builds both legs with `abstract`ed naturality
   proofs (Instance/Fun.v:272-293), so each leg carries its own opaque
   law fields, and the two isomorphism records then carry their own
   inverse law fields on top.  The difference is therefore confined to
   opaque LAW fields — the legs' naturality fields and the record's
   inverse laws — and touches no data.  This file's first draft located
   it in the inverse law fields alone; an audit measured the legs.

   CORRECTIONS

   To the issue.  Its "Current state" is right on the absence — at
   bbddaee2, before this file was added, the command
   `rg -c 'Monic|Epic'` over Instance/Fun.v, Instance/Fun/ and
   Theory/Natural/ returned no hits at all (it now matches this file and
   nothing else in those locations) — but two of its donor
   line numbers are stale: [injectivity_is_monic] is at
   Instance/Sets.v:374, not :369, and [surjectivity_is_epic] is at :509,
   not :429.  Both were re-checked here.

   To the OCR.  A plain `pdftotext -f 100 -l 100` of the scan mangles
   the sentence badly — it renders τ as "I", the superscript C of B^C as
   "e", both subscripts as "e" ("Ie: Se----> Te"), and both Roman
   numerals as "111" — so it is not usable as a quotation.  The text
   above is read from the page image instead.  Even a cleaned-up OCR
   renders the subscripted S_c and T_c as "S c" and "T c"; the printed
   page sets them as subscripts, and the quotation above keeps them.

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK

   Every constant of sections A-D was read with `Set Printing Universes`
   and its whole (wrapped) constraint block flattened before counting.

   The general theorems are
   `pointwise_monic_is_monic@{u u0 u1 u2 u3 u4 u5}` over
   `C : Category@{u u0 u0}` and `D : Category@{u1 u2 u2}` — hom
   identified with proof in BOTH binders, expressed by reusing the level
   variable — with the block carrying the equation `u0 = u2`, which
   identifies C's hom-and-proof level with D's.  Both OBJECT universes
   stay free: `u` and `u1` occur in bounds only, in no equation.  So a
   reader who checks only the block sees one identification and misses
   two; both must be read.

   The identifications are INHERITED and are attributed by isolating
   experiments in the probe, not by assertion.  Under a declared
   `Constraint ch < dh` the functor category `@Fun Cu Du` is rejected
   with "Cannot enforce dh = ch" while `x ~{Cu}~> y` and `a ~{Du}~> b`
   are both accepted at those very levels: [Fun] takes both categories
   at ONE hom-and-proof level, which is the source of `u0 = u2` and of
   half of each binder's hom=proof.  Independently, under
   `Constraint mh < mp` both `@Monic Du a b g` and `@Epic Du a b g` are
   rejected with "Cannot enforce mp = mh" against the same two accepted
   controls, so the classes of Theory/Morphisms.v identify hom with
   proof on their own.  Neither identification is introduced here and
   neither is claimed unavoidable.

   At Sets the picture is the same one level in:
   `sets_functor_monic_iff_pointwise` is over `C : Category@{u u0 u0}`
   with the two functors landing in `Sets@{u0 u1}` and `Sets@{u0 u2}`,
   and the block adds `u0 < u1`, `u0 < u2` and `u1 = u2` — the two
   occurrences of Sets are forced to be ONE instance, which is what
   `[C, Sets]` means, and Sets' carrier level is C's hom level, which is
   `Sets@{o so} : Category@{so o o}` meeting [Fun].

   THE WITNESS SECTION CARRIES A `Set` PIN AND THE GENERAL RESULTS DO
   NOT.  Sweeping all 74 constants for the literal token `Set` in binder
   or block, exactly 20 carry it: the 16 named constants of the witness
   section (TwoOne, TwoBool, TwoTwoX, TwoTwoY, two_pick_nat,
   two_collapse, two_arrow, pick_true_Monic, collapse_Epic and the seven
   results about them) together with four of their obligations
   (two_pick_nat_obligation_1/2, two_collapse_obligation_1/2).  The
   cause is [_2] itself: `_2@{u u0} : Category@{u Set Set}`, because
   Instance/Two.v declares `TwoHom : TwoObj → TwoObj → Set`, and [Fun]
   then forces the target's hom-and-proof level to match, so `[_2, Sets]`
   is `Sets@{Set _}`.  Sections A-D are free of it.  This is inherited,
   is the price of using the cheapest non-trivial shape in the tree, and
   is not claimed unavoidable.

   ENGINEERING FINDINGS

   1.  A [Program Definition] of a Sets-morphism that leaves
       `proper_morphism` to instance resolution can pin the carrier
       universe to `Set`.  Both new functors therefore supply their
       arrow action's respectfulness certificate BY HAND —
       [ker_fun_proper] and [ck_fun_proper] are ordinary lemmas and
       [ker_map]/[ck_map] are record literals — and the measurement
       above confirms sections A-D acquired no `Set`.

   2.  `Set Transparent Obligations` was tried at the top of this file
       and is NOT needed: both [eq_refl] comparisons with
       [Functor_Setoid_Nat_Iso] hold with the repo's ordinary opaque
       obligations, because [nat_inverse] supplies its `transform` field
       directly and only its two naturality fields become obligations.
       The line was removed after measuring that.

   3.  [Constant_Functor] already exists (Instance/Fun/Terminal.v:342)
       and is not reused: requiring that module would take this file's
       transitive closure from 39 modules to 74 (measured by following
       every Require line to a fixed point), which is a heavy price on
       every downstream consumer of a file whose whole purpose is to be
       cited.  A five-line witness-local [const_fun] is declared
       instead, with the duplication recorded here rather than hidden.

   4.  Applying [fmap_respects], [fmap_id] and [fmap_comp] inside Sets
       needs the pointwise reading: `fmap[F] f ≈ fmap[F] g` unfolds to
       `∀ a, ...`, so `apply fmap_id` does not match and the field must
       be applied as a term (`exact (@fmap_id _ _ F _ _)`).

   5.  The identity of `[C, D]` has component `fmap[G] id`, not `id`
       (Theory/Natural/Transformation.v:220), so the two inverse laws of
       [componentwise_iso] and [nat_iso_pointwise] each cost one
       `fmap_id` step; that residue is the only friction in section (C).

   6.  A name collision was found by sweeping every name this file
       introduces and was renamed away before landing: [two_pick] is
       taken by Instance/Fun/Terminal.v:692, and since the
       print-assumptions target loads many modules into one scope a
       shared name would have audited the wrong constant.  The witness
       here is [two_pick_nat].  Over all 95 names introduced by this
       file and its probe — 52 declaration heads, 22 [Program]
       obligations, and the probe's 12 declared and 9 rejected names —
       zero collisions remain; the sweep was instrument-checked on
       [Monic] and [Full], which must collide and do.

   NON-VACUITY

   [two_pick_nat] is monic in `[_2, Sets]` and provably not epic there,
   and [two_collapse] is epic and provably not monic — each refutation
   routed through the CONVERSE half, so section (B) is exercised and not
   merely stated, with the pointwise obstruction exhibited at the named
   component [TwoX]: [two_pick_component_not_surjective] discharges by
   `discriminate` on `true = false` in the two-element setoid.  The
   general direction is exercised at a target that is NOT Sets by
   [two_arrow_Monic] and [two_arrow_Epic] over `[_2, _2]`, on
   Instance/Two.v's [TwoXY_monic]/[TwoXY_epic].  DEGENERACY, labelled:
   all three witness transformations ([two_pick_nat], [two_collapse],
   [two_arrow]) run between CONSTANT functors, so
   their naturality squares reduce to `θ_x ≈ θ_y` and the witnesses
   exercise the hom-setoids and the cancellation arguments rather than
   naturality; and `[_2, _2]` has thin hom-setoids.  What they are for
   is the cancellation content, and that they do carry.

   NOT DELIVERED

   No converse at a general target, and no separating example refuting
   one — see THE MONOMORPHISM DECISION above.  No functor-category
   pullback, pushout, [HasPullbacks] or [HasPushouts] instance: the two
   functors here are the pointwise (co)limit OBJECTS with their legs,
   and no universal property is claimed for either in `[C, Sets]`.  No
   identification of [KerPair] with [Structure/Regular.v]'s generic
   [kernel_pair] one level up, and none with [CokerPair] and
   [Theory/Morphisms/CokernelPair.v]'s [cokernel_pair].  No statement
   that [KerPair] or [CokerPair] is functorial in θ.  No Yoneda or
   representability route and no comparison with one.  No subobject
   classifier and no subobject lattice for presheaves — (D) is the input
   that work will cite, not that work.  Nothing about split monos,
   split epis, regular or effective epis, or balancedness of `[C, D]`.
   No witness at a shape other than [_2], and no witness with a
   non-constant functor. *)

(* ------------------------------------------------------------------ *)
(** ** (A) An arbitrary target: componentwise monic/epic suffices *)

Section General.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Theorem pointwise_monic_is_monic :
  (∀ x : C, Monic (transform[θ] x)) → @Monic ([C, D]) F G θ.
Proof.
  intros H.
  constructor; intros K g1 g2 Heq x.
  apply (@monic _ _ _ _ (H x) (K x)).
  exact (Heq x).
Defined.

Theorem pointwise_epic_is_epic :
  (∀ x : C, Epic (transform[θ] x)) → @Epic ([C, D]) F G θ.
Proof.
  intros H.
  constructor; intros K g1 g2 Heq x.
  apply (@epic _ _ _ _ (H x) (K x)).
  exact (Heq x).
Defined.

End General.

(* ------------------------------------------------------------------ *)
(** ** (B) The target Sets: the biconditionals, by pointwise (co)limits *)

Section SetsConverse.

Context {C : Category}.
Context {F : C ⟶ Sets}.
Context {G : C ⟶ Sets}.
Context (θ : F ⟹ G).

(** ** The pointwise kernel-pair functor *)

Lemma theta_nat {x y : C} (f : x ~{C}~> y) (a : carrier (F x)) :
  transform[θ] y (fmap[F] f a) ≈ fmap[G] f (transform[θ] x a).
Proof. exact (naturality_sym θ x y f a). Qed.

Lemma ker_map_ok {x y : C} (f : x ~{C}~> y)
      (u : carrier (sets_ker (transform[θ] x))) :
  transform[θ] y (fmap[F] f (fst `1 u))
    ≈ transform[θ] y (fmap[F] f (snd `1 u)).
Proof.
  transitivity (fmap[G] f (transform[θ] x (fst `1 u))).
  - apply theta_nat.
  - transitivity (fmap[G] f (transform[θ] x (snd `1 u))).
    + apply proper_morphism; exact (`2 u).
    + symmetry; apply theta_nat.
Qed.

Definition ker_fun {x y : C} (f : x ~{C}~> y)
  (u : carrier (sets_ker (transform[θ] x))) :
  carrier (sets_ker (transform[θ] y)) :=
  ((fmap[F] f (fst `1 u), fmap[F] f (snd `1 u)); ker_map_ok f u).

Lemma ker_fun_proper {x y : C} (f : x ~{C}~> y) :
  Proper (equiv ==> equiv) (ker_fun f).
Proof.
  intros u v H; destruct H as [H1 H2].
  split; simpl; now apply proper_morphism.
Qed.

Definition ker_map {x y : C} (f : x ~{C}~> y) :
  sets_ker (transform[θ] x) ~{Sets}~> sets_ker (transform[θ] y) :=
  {| morphism := ker_fun f; proper_morphism := ker_fun_proper f |}.

Program Definition KerPair : C ⟶ Sets := {|
  fobj := fun x => sets_ker (transform[θ] x);
  fmap := fun x y f => ker_map f
|}.
Next Obligation.
  proper; split; simpl;
    exact (@fmap_respects _ _ F _ _ _ _ X _).
Qed.
Next Obligation. split; simpl; exact (@fmap_id _ _ F _ _). Qed.
Next Obligation. split; simpl; exact (@fmap_comp _ _ F _ _ _ _ _ _). Qed.

Program Definition KerFst : KerPair ⟹ F := {|
  transform := fun x => sets_ker_fst (transform[θ] x)
|}.

Program Definition KerSnd : KerPair ⟹ F := {|
  transform := fun x => sets_ker_snd (transform[θ] x)
|}.

Lemma ker_agree : θ ∙ KerFst ≈[Fun] θ ∙ KerSnd.
Proof. intros x u; exact (`2 u). Qed.

Theorem sets_functor_monic_pointwise :
  @Monic ([C, Sets]) F G θ → ∀ x : C, Monic (transform[θ] x).
Proof.
  intros Hm x.
  apply (fst (injectivity_is_monic (transform[θ] x))).
  intros a b Hab.
  exact (@monic _ _ _ _ Hm KerPair KerFst KerSnd ker_agree x
                (sets_ker_pair (transform[θ] x) a b Hab)).
Defined.

Theorem sets_functor_monic_iff_pointwise :
  @Monic ([C, Sets]) F G θ  ↔  (∀ x : C, Monic (transform[θ] x)).
Proof.
  split.
  - exact sets_functor_monic_pointwise.
  - exact (pointwise_monic_is_monic θ).
Defined.

(** ** The pointwise cokernel-pair functor *)

Lemma ck_Im_map {x y : C} (f : x ~{C}~> y) (b : carrier (G x)) :
  Im (transform[θ] x) b → Im (transform[θ] y) (fmap[G] f b).
Proof.
  intros [z Hz]; exists (fmap[F] f z).
  transitivity (fmap[G] f (transform[θ] x z)).
  - apply theta_nat.
  - now apply proper_morphism.
Defined.

Definition ck_fun {x y : C} (f : x ~{C}~> y)
  (u : carrier (CKSetoid (transform[θ] x))) :
  carrier (CKSetoid (transform[θ] y)) :=
  match u with
  | Datatypes.inl b => Datatypes.inl (fmap[G] f b)
  | Datatypes.inr b => Datatypes.inr (fmap[G] f b)
  end.

Lemma ck_fun_proper {x y : C} (f : x ~{C}~> y) :
  Proper (equiv ==> equiv) (ck_fun f).
Proof.
  intros u v H; destruct u, v; simpl in *;
    try (now apply proper_morphism);
    destruct H as [H1 H2]; split;
    [ now apply proper_morphism | now apply ck_Im_map
    | now apply proper_morphism | now apply ck_Im_map ].
Qed.

Definition ck_map {x y : C} (f : x ~{C}~> y) :
  CKSetoid (transform[θ] x) ~{Sets}~> CKSetoid (transform[θ] y) :=
  {| morphism := ck_fun f; proper_morphism := ck_fun_proper f |}.

Program Definition CokerPair : C ⟶ Sets := {|
  fobj := fun x => CKSetoid (transform[θ] x);
  fmap := fun x y f => ck_map f
|}.
Next Obligation.
  proper; destruct x1; simpl;
    exact (@fmap_respects _ _ G _ _ _ _ X _).
Qed.
Next Obligation.
  destruct x0; simpl; exact (@fmap_id _ _ G _ _).
Qed.
Next Obligation.
  destruct x0; simpl; exact (@fmap_comp _ _ G _ _ _ _ _ _).
Qed.

Program Definition CkLeft : G ⟹ CokerPair := {|
  transform := fun x => ck_left (transform[θ] x)
|}.

Program Definition CkRight : G ⟹ CokerPair := {|
  transform := fun x => ck_right (transform[θ] x)
|}.

Lemma ck_agree_nat : CkLeft ∙ θ ≈[Fun] CkRight ∙ θ.
Proof. intros x a; exact (ck_agree (transform[θ] x) a). Qed.

Theorem sets_functor_epic_pointwise :
  @Epic ([C, Sets]) F G θ → ∀ x : C, Epic (transform[θ] x).
Proof.
  intros He x.
  apply (fst (surjectivity_is_epic (transform[θ] x))).
  intros b.
  exact (snd (@epic _ _ _ _ He CokerPair CkLeft CkRight ck_agree_nat x b)).
Defined.

Theorem sets_functor_epic_iff_pointwise :
  @Epic ([C, Sets]) F G θ  ↔  (∀ x : C, Epic (transform[θ] x)).
Proof.
  split.
  - exact sets_functor_epic_pointwise.
  - exact (pointwise_epic_is_epic θ).
Defined.

End SetsConverse.

(* ------------------------------------------------------------------ *)
(** ** (C) Awodey §7.10 Ex 6: invertibility of a GIVEN transformation *)

Section Invertibility.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Lemma nat_inv_natural (H : ∀ x : C, IsIsomorphism (transform[θ] x))
      {x y : C} (f : x ~{C}~> y) :
  fmap[F] f ∘ @two_sided_inverse _ _ _ _ (H x)
    ≈ @two_sided_inverse _ _ _ _ (H y) ∘ fmap[G] f.
Proof.
  rewrite <- (id_left (fmap[F] f ∘ _)).
  rewrite <- (@is_left_inverse _ _ _ _ (H y)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite comp_assoc.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  rewrite (@is_right_inverse _ _ _ _ (H x)).
  now rewrite id_right.
Qed.

Program Definition nat_inverse
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) : G ⟹ F := {|
  transform := fun x => @two_sided_inverse _ _ _ _ (H x)
|}.
Next Obligation. now rewrite nat_inv_natural. Qed.
Next Obligation. now rewrite nat_inv_natural. Qed.

Definition componentwise_iso
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) :
  @IsIsomorphism ([C, D]) F G θ.
Proof.
  refine (@Build_IsIsomorphism ([C, D]) F G θ (nat_inverse H) _ _);
    intro x; simpl.
  - rewrite (@is_right_inverse _ _ _ _ (H x)).
    now rewrite fmap_id.
  - rewrite (@is_left_inverse _ _ _ _ (H x)).
    now rewrite fmap_id.
Defined.

Definition nat_iso_pointwise (H : @IsIsomorphism ([C, D]) F G θ) (x : C) :
  IsIsomorphism (transform[θ] x).
Proof.
  refine {| two_sided_inverse :=
              transform[@two_sided_inverse _ _ _ _ H] x |}.
  - etransitivity; [ exact (@is_right_inverse _ _ _ _ H x) | ].
    simpl; apply fmap_id.
  - etransitivity; [ exact (@is_left_inverse _ _ _ _ H x) | ].
    simpl; apply fmap_id.
Defined.

Theorem nat_iso_iff_pointwise :
  @IsIsomorphism ([C, D]) F G θ  ↔  (∀ x : C, IsIsomorphism (transform[θ] x)).
Proof.
  split.
  - exact nat_iso_pointwise.
  - exact componentwise_iso.
Defined.

End Invertibility.

(* ------------------------------------------------------------------ *)
(** ** (C, continued) Comparison with [Functor_Setoid_Nat_Iso] *)

Section EquivComparison.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.
Context (θ : F ⟹ G).

Definition nat_iso_family
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) : F ≈ G.
Proof.
  simpl.
  exists (fun x => @IsIsoToIso D (F x) (G x) (transform[θ] x) (H x)).
  intros x y f; simpl.
  symmetry.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  rewrite (@is_left_inverse _ _ _ _ (H y)).
  now rewrite id_left.
Defined.

Example equiv_iso_to_is_theta
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) (x : C) :
  transform[to (equiv_iso (nat_iso_family H))] x = transform[θ] x
  := eq_refl.

Example equiv_iso_from_is_nat_inverse
  (H : ∀ x : C, IsIsomorphism (transform[θ] x)) (x : C) :
  transform[from (equiv_iso (nat_iso_family H))] x
    = transform[nat_inverse θ H] x := eq_refl.

End EquivComparison.

(* ------------------------------------------------------------------ *)
(** ** (D) Presheaves: monos are the pointwise injections *)

Section Presheaf.

Context {C : Category}.
Context {P : C^op ⟶ Sets}.
Context {Q : C^op ⟶ Sets}.
Context (θ : P ⟹ Q).

Definition presheaf_monic_iff_pointwise :
  @Monic ([C^op, Sets]) P Q θ  ↔  (∀ x : C^op, Monic (transform[θ] x))
  := sets_functor_monic_iff_pointwise θ.

Definition presheaf_epic_iff_pointwise :
  @Epic ([C^op, Sets]) P Q θ  ↔  (∀ x : C^op, Epic (transform[θ] x))
  := sets_functor_epic_iff_pointwise θ.

Theorem presheaf_monic_iff_injective :
  @Monic ([C^op, Sets]) P Q θ  ↔
  (∀ (x : C^op) (a b : carrier (P x)),
      transform[θ] x a ≈ transform[θ] x b → a ≈ b).
Proof.
  split.
  - intros Hm x.
    exact (snd (injectivity_is_monic (transform[θ] x))
               (sets_functor_monic_pointwise θ Hm x)).
  - intros Hi.
    apply (pointwise_monic_is_monic θ); intros x.
    exact (fst (injectivity_is_monic (transform[θ] x)) (Hi x)).
Defined.

Theorem presheaf_epic_iff_surjective :
  @Epic ([C^op, Sets]) P Q θ  ↔
  (∀ (x : C^op) (b : carrier (Q x)), ∃ a, transform[θ] x a ≈ b)%type.
Proof.
  split.
  - intros He x.
    exact (epic_implies_surjective (transform[θ] x)
             (sets_functor_epic_pointwise θ He x)).
  - intros Hs.
    apply (pointwise_epic_is_epic θ); intros x.
    exact (surjective_implies_epic (transform[θ] x) (Hs x)).
Defined.

End Presheaf.

(* ------------------------------------------------------------------ *)
(** ** Non-vacuity *)

Section Witnesses.

Definition const_fun@{co ch cp dro dh dp}
  {C : Category@{co ch cp}} {D : Category@{dro dh dp}} (d : D) : C ⟶ D :=
  {| fobj          := fun _ => d
   ; fmap          := fun _ _ _ => id
   ; fmap_respects := fun _ _ _ _ _ => reflexivity _
   ; fmap_id       := fun _ => reflexivity _
   ; fmap_comp     := fun _ _ _ _ _ => symmetry (id_left id) |}.

Definition TwoOne : _2 ⟶ Sets :=
  @const_fun _2 Sets unit_setoid_object.
Definition TwoBool : _2 ⟶ Sets :=
  @const_fun _2 Sets bool_setoid_object.

Program Definition two_pick_nat : TwoOne ⟹ TwoBool := {|
  transform := fun _ => pick_true
|}.

Program Definition two_collapse : TwoBool ⟹ TwoOne := {|
  transform := fun _ => collapse
|}.

Lemma pick_true_Monic : @Monic Sets _ _ pick_true.
Proof.
  apply (fst (injectivity_is_monic pick_true)).
  intros a b _; destruct a, b; reflexivity.
Defined.

Lemma collapse_Epic : @Epic Sets _ _ collapse.
Proof.
  apply (fst (surjectivity_is_epic collapse)).
  intros b; exists true; destruct b; reflexivity.
Defined.

Definition two_pick_Monic : @Monic ([_2, Sets]) TwoOne TwoBool two_pick_nat :=
  pointwise_monic_is_monic two_pick_nat (fun _ => pick_true_Monic).

Definition two_collapse_Epic :
  @Epic ([_2, Sets]) TwoBool TwoOne two_collapse :=
  pointwise_epic_is_epic two_collapse (fun _ => collapse_Epic).

Lemma two_pick_component_not_surjective :
  (∀ b : carrier bool_setoid_object,
      ∃ a, transform[two_pick_nat] TwoX a ≈ b)%type → False.
Proof.
  intros Hs; destruct (Hs false) as [a Ha]; simpl in Ha; discriminate.
Qed.

Lemma two_pick_not_Epic :
  @Epic ([_2, Sets]) TwoOne TwoBool two_pick_nat → False.
Proof.
  intros He.
  apply two_pick_component_not_surjective.
  exact (epic_implies_surjective (transform[two_pick_nat] TwoX)
           (sets_functor_epic_pointwise two_pick_nat He TwoX)).
Qed.

Lemma two_collapse_not_Monic :
  @Monic ([_2, Sets]) TwoBool TwoOne two_collapse → False.
Proof.
  intros Hm.
  apply collapse_not_monic.
  exact (sets_functor_monic_pointwise two_collapse Hm TwoX).
Qed.

Definition TwoTwoX : _2 ⟶ _2 := @const_fun _2 _2 TwoX.
Definition TwoTwoY : _2 ⟶ _2 := @const_fun _2 _2 TwoY.

Program Definition two_arrow : TwoTwoX ⟹ TwoTwoY := {|
  transform := fun _ => TwoXY
|}.

Definition two_arrow_Monic :
  @Monic ([_2, _2]) TwoTwoX TwoTwoY two_arrow :=
  pointwise_monic_is_monic two_arrow (fun _ => TwoXY_monic).

Definition two_arrow_Epic :
  @Epic ([_2, _2]) TwoTwoX TwoTwoY two_arrow :=
  pointwise_epic_is_epic two_arrow (fun _ => TwoXY_epic).

End Witnesses.
