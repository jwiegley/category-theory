Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(** * Mac Lane §IV.3's transfer lemma: representable transformations *)

(* SOURCES.

   Mac Lane, CWM 2nd ed., §IV.3, printed p. 91 (read from the page image
   p367-100.png):

     "Lemma.  Let f* : A(a, −) ⇸ A(b, −) be the natural transformation
      induced by an arrow f : b → a of A.  Then f* is monic if and only
      if f is epi, while f* is epi if and only if f is a split monic
      (i.e., if and only if f has a left inverse)."

   and, immediately below it on the same page (same image):

     "Note that f* ↦ f is the bijection Nat(A(a, −), A(b, −)) ≅ A(b, a)
      given by the Yoneda lemma."

   and

     "Observe, also, that for functors S, T : C → B, a natural
      transformation τ : S ⇸ T is epi (respectively, monic) in B^C if and
      only if every component τ_c : S_c → T_c is epi (respectively, monic)
      in B for B = Set; this follows by Exercise III.4.4, computing the
      pushout pointwise as in Exercise III.5.5."

   and the proof itself (same image):

     "Proof.  For h ∈ A(a, c), f*h = hf.  Hence the first result is just
      the definition of an epi f.  If f* is epi, there is an h_0 : a → b
      with f*h_0 = h_0 f = 1 : b → b, so f has a left inverse.  The
      converse is immediate."

   Catalog id: maclane:IV.3:lem1.  The theorem the lemma serves is
   maclane:IV.3:thm1, in Adjunction/FullFaithful.v.

   NAMING.  Mac Lane writes the induced transformation f*.  That spelling
   is not used here: `*` is multiplication notation in several scopes of
   this library, and a bare `f*` would be a parsing hazard.  The
   transformation is [hom_transfer f].

   WHAT IS DELIVERED AND AT WHAT STRENGTH.

   Over an ARBITRARY category A and an ARBITRARY arrow f : b ~> a:

   - [hom_transfer f : [Hom a,─] ⟹ [Hom b,─]], component at c the
     precomposition h ↦ h ∘ f.  It is built by hand rather than taken to
     be [fmap[Curried_Hom A] f]; the relation between the two is
     MEASURED rather than assumed, see MEASUREMENTS below.
   - [hom_transfer_monic_iff_epic] : monic in [A, Sets] ⟺ f is [Epic].
   - [hom_transfer_epic_iff_section] : epic in [A, Sets] ⟺ f is
     [Section].  The library's split monomorphism is [Section]
     (Theory/Morphisms.v:56, aliased [SplitMono] at :130): a chosen LEFT
     inverse, carried as data.  It is deliberately NOT [Monic]: a monic
     need not split, and the reviewer check for this issue asks for the
     split notion.
   - Both biconditionals are [Defined], not [Qed], because both carry
     data in both directions: the forward half of the second EXTRACTS a
     left inverse from the surjectivity of the component at b.

   ROUTE.  Mac Lane's, in three steps, exactly as his proof runs:

   (1) The pointwise characterisation of monos and epis in a functor
       category valued in Set.  This is Mac Lane's "Observe, also"
       paragraph above, which is the catalog item maclane:IV.3:remark1
       and is IN TREE as Instance/Fun/Morphisms.v.  The scripts below
       consume its four one-directional halves by name — the two
       target-agnostic ones [pointwise_monic_is_monic] (:341) and
       [pointwise_epic_is_epic] (:350) for the backward directions, and
       the two [Sets]-specific converses [sets_functor_monic_pointwise]
       (:427) and [sets_functor_epic_pointwise] (:504) for the forward
       ones — rather than the packaged biconditionals
       [sets_functor_monic_iff_pointwise] (:437) and
       [sets_functor_epic_iff_pointwise] (:513), which are those same
       halves paired.  Nothing here is restated.
   (2) The characterisation of monos and epis in Sets as the injections
       and the surjections: Instance/Sets.v's [injectivity_is_monic]
       (:374) and [surjectivity_is_epic] (:509), the second's backward
       leg exposed as [epic_implies_surjective] (:532).  Also consumed.
   (3) The two elementary observations Mac Lane's proof then makes:
       injectivity of h ↦ h ∘ f at every c IS right-cancellability of f,
       and surjectivity at c := b applied to id[b] produces the left
       inverse, while a left inverse s makes every component surjective
       by k ↦ k ∘ s.

   THE YONEDA BIJECTION IS CITED, NOT ROUTED THROUGH.  Mac Lane's
   remark that f ↦ f* is the Yoneda bijection is true here as well —
   [Yoneda_Full]/[Yoneda_Faithful] (Functor/Hom.v:96/:85) and
   [Yoneda_Embedding'] (:109) are exactly that — but no statement below
   consumes them, and that is a deliberate universe decision, not an
   oversight: [Yoneda_Embedding'] is stated over a category whose
   object, hom and proof universes are IDENTIFIED, and routing the
   transfer lemma through it would inherit that identification for no
   gain.  What is recorded instead is the definitional identification
   [hom_transfer_is_fmap] below, from which the Yoneda reading follows
   by citation.

   MEASUREMENTS (strict first).

   - [hom_transfer_component] : the component's value at h is h ∘ f, at
     Leibniz [=], by [eq_refl].  Deliberate strictness, labelled.
   - The comparison with [fmap[Curried_Hom A] f] was measured on a
     three-rung ladder and the answer is NOT uniform, so the header does
     not say "it is [fmap]" without qualification.  VALUES agree at
     Leibniz [=] ([hom_transfer_is_fmap_value], [eq_refl]): both sides
     compute h ∘ f, because [Curried_Hom]'s arrow action is
     `fun g => g ∘ op f` and [op] moves no data
     (Construction/Opposite.v:137).  The COMPONENT record does NOT
     ([SetoidMorphism] carries a [proper_morphism] certificate, and the
     two are separately elaborated obligations), and neither does the
     whole [Transform] record, which additionally rebuilds [naturality]
     and [naturality_sym].  What holds at record level is [≈] in the
     functor category, [hom_transfer_is_fmap], whose proof is
     `intros c h; reflexivity` — that is, the [≈] is carried entirely by
     the value-level [eq_refl].  Both refutations are pinned as
     CONVERSION negatives in Test/ProbeFullFaithful367.v.
   - [hom_transfer_at_id] : the Yoneda-side readback
     `transform[hom_transfer f] a id ≈ f` holds only up to [≈], not at
     [eq_refl]: the value is `id ∘ f`, and [id_left] is a law field of
     [Category], so conversion does not remove it.  The strict form is
     pinned as a CONVERSION negative in
     Test/ProbeFullFaithful367.v.
   - [hom_transfer] is a [Program Definition] with ZERO remaining
     obligations: the library's obligation tactic (Lib/Tactics.v,
     installed by Lib.v) discharges respectfulness of `h ↦ h ∘ f` and
     both naturality fields, each of which is one [comp_assoc].

   ENGINEERING FINDINGS.

   - `[Hom a,─]` is the notation of Functor/Hom.v:80 for
     `@Curried_Hom _ a`, which parses as the OBJECT action of
     [Curried_Hom] at a — the [Curried_Hom : Category >-> Functor]
     coercion (Functor/Hom.v:78) is what makes `a` land in the object
     slot.  So `[Hom a,─] : A ⟶ Sets`, not a functor out of A^op.
   - An arrow `f : b ~{A}~> a` IS an arrow `a ~{Opposite A}~> b` on the
     nose, so [fmap[Curried_Hom A] f] typechecks with no coercion; the
     ascription in [hom_transfer_is_fmap] is for the reader.
   - DISPLAY HAZARD.  Because of the [Curried_Hom : Category >-> Functor]
     coercion, an error message about `fmap[Curried_Hom A] f` prints as
     `fmap[A] f` — the functor is displayed by the CATEGORY it was
     coerced from.  Both refuted [eq_refl]s above read that way, and a
     reader who does not know the coercion will look for a functor named
     A.
   - The two biconditionals are stated with the ambient category written
     out, `@Monic ([A, Sets]) _ _ (hom_transfer f)`.  Left implicit, the
     elaborator has no way to choose between the functor category and
     [Sets] for a transformation whose components are [Sets]-morphisms.

   NOT DELIVERED.  No statement about the CONTRAVARIANT induced
   transformation `A(−,b) ⟹ A(−,a)` and no dual pair of biconditionals
   for it; no naturality of [hom_transfer] in f (that it is [fmap] of a
   functor is recorded, but no consequence is drawn); no [Monic]/[Epic]
   statement for a transformation between representables at a target
   other than [Sets]; no identification of [hom_transfer] with anything
   in Functor/Hom/Yoneda.v beyond the citation above; and no
   representability or [Full]/[Faithful] corollary. *)

Section Transfer.

Context {A : Category}.

(* ** The induced transformation *)

(* Mac Lane's f*: precomposition with f, natural in the second variable
   because composition is associative. *)

Program Definition hom_transfer {a b : A} (f : b ~> a) :
  [Hom a ,─] ⟹ [Hom b ,─] := {|
  transform := fun c => {| morphism := fun h => h ∘ f |}
|}.

(* The component's value, at Leibniz equality.  Deliberate strictness:
   this is one of the file's two uses of [=] on morphisms, and it is an
   acceptance test rather than a mathematical claim. *)

Example hom_transfer_component {a b : A} (f : b ~> a) (c : A)
        (h : a ~> c) : transform[hom_transfer f] c h = h ∘ f := eq_refl.

(* [hom_transfer f] and the arrow action of the curried hom-functor at f,
   read as an arrow of the opposite category.  Measured strict first: the
   VALUES agree at Leibniz [=] (below), the whole [Transform] record does
   NOT, and the transformations agree at [≈] in the functor category.  See
   MEASUREMENTS in the header. *)

Example hom_transfer_is_fmap_value {a b : A} (f : b ~> a) (c : A)
        (h : a ~> c) :
  transform[hom_transfer f] c h
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c h
  := eq_refl.

Lemma hom_transfer_is_fmap {a b : A} (f : b ~> a) :
  hom_transfer f
    ≈[[A, Sets]] fmap[Curried_Hom A] (f : a ~{Opposite A}~> b).
Proof. intros c h; reflexivity. Qed.

(* The Yoneda-side readback reaches [≈] and no further: the value is
   `id ∘ f`.  The strict form is refuted, and pinned in the probe. *)

Lemma hom_transfer_at_id {a b : A} (f : b ~> a) :
  transform[hom_transfer f] a id ≈ f.
Proof. exact (id_left f). Qed.

(* ** Mac Lane's lemma, first half: monic ⟺ epi *)

(* "For h ∈ A(a, c), f*h = hf.  Hence the first result is just the
   definition of an epi f."  In this setoid setting the sentence becomes
   three steps: monic in the functor category is componentwise monic
   (Instance/Fun/Morphisms.v), componentwise monic in Sets is
   componentwise injective (Instance/Sets.v), and componentwise
   injectivity of h ↦ h ∘ f IS right-cancellability of f. *)

Theorem hom_transfer_monic_iff_epic {a b : A} (f : b ~> a) :
  @Monic ([A, Sets]) _ _ (hom_transfer f) ↔ Epic f.
Proof.
  split.
  - intros Hm.
    constructor; intros c g1 g2 Heq.
    exact (snd (injectivity_is_monic (transform[hom_transfer f] c))
               (sets_functor_monic_pointwise (hom_transfer f) Hm c)
               g1 g2 Heq).
  - intros He.
    apply pointwise_monic_is_monic; intro c.
    apply (fst (injectivity_is_monic (transform[hom_transfer f] c))).
    intros g1 g2 Heq.
    exact (@epic A _ _ f He c g1 g2 Heq).
Defined.

(* ** Mac Lane's lemma, second half: epi ⟺ split monic *)

(* "If f* is epi, there is an h_0 : a → b with f*h_0 = h_0 f = 1 : b → b,
   so f has a left inverse.  The converse is immediate."  The witness
   h_0 is obtained by evaluating surjectivity of the component at c := b
   on id[b]; it is DATA, [∃] being [sigT] here, which is why the
   biconditional is [Defined]. *)

Theorem hom_transfer_epic_iff_section {a b : A} (f : b ~> a) :
  @Epic ([A, Sets]) _ _ (hom_transfer f) ↔ Section f.
Proof.
  split.
  - intros He.
    destruct (epic_implies_surjective
                (transform[hom_transfer f] b)
                (sets_functor_epic_pointwise (hom_transfer f) He b)
                (id[b])) as [s Hs].
    exact {| section := s ; section_comp := Hs |}.
  - intros Hs.
    apply pointwise_epic_is_epic; intro c.
    apply (fst (surjectivity_is_epic (transform[hom_transfer f] c))).
    intro k.
    exists (k ∘ @section A b a f Hs).
    change ((k ∘ @section A b a f Hs) ∘ f ≈ k).
    rewrite <- comp_assoc.
    rewrite (@section_comp A b a f Hs).
    exact (id_right k).
Defined.

(* The two halves under their own names, for callers that want just one.
   Each is a projection of the biconditional, so no proof text is
   repeated and the identity of the statements is by conversion. *)

Definition epic_of_hom_transfer_monic {a b : A} (f : b ~> a) :
  @Monic ([A, Sets]) _ _ (hom_transfer f) → Epic f :=
  fst (hom_transfer_monic_iff_epic f).

Definition hom_transfer_monic_of_epic {a b : A} (f : b ~> a) :
  Epic f → @Monic ([A, Sets]) _ _ (hom_transfer f) :=
  snd (hom_transfer_monic_iff_epic f).

Definition section_of_hom_transfer_epic {a b : A} (f : b ~> a) :
  @Epic ([A, Sets]) _ _ (hom_transfer f) → Section f :=
  fst (hom_transfer_epic_iff_section f).

Definition hom_transfer_epic_of_section {a b : A} (f : b ~> a) :
  Section f → @Epic ([A, Sets]) _ _ (hom_transfer f) :=
  snd (hom_transfer_epic_iff_section f).

(* A by-product, recorded because it is the shape the theorem file needs
   and because it makes the pointwise reading of each side visible: the
   component at c is injective exactly when f cancels on the right into
   c, and surjective exactly when every arrow out of b factors through
   f. *)

Lemma hom_transfer_component_injective_iff {a b : A} (f : b ~> a)
      (c : A) :
  (∀ g1 g2 : a ~> c, g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2)
    ↔ Monic (transform[hom_transfer f] c).
Proof. exact (injectivity_is_monic (transform[hom_transfer f] c)). Defined.

Lemma hom_transfer_component_surjective_iff {a b : A} (f : b ~> a)
      (c : A) :
  (∀ k : b ~> c, ∃ g : a ~> c, g ∘ f ≈ k)%type
    ↔ Epic (transform[hom_transfer f] c).
Proof. exact (surjectivity_is_epic (transform[hom_transfer f] c)). Defined.

End Transfer.
