Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.

Generalizable All Variables.

(** * Fullness of an adjoint: Mac Lane §IV.3 Exercises 3 and 6. *)

(* Sources.

   Mac Lane, *Categories for the Working Mathematician*, 2nd ed., §IV.3,
   printed page 92 (PDF page 101 of the scan this repository calibrates
   against in doc/plan/books/maclane/pagemap.md).  The two exercises are
   quoted here as PRINTED, read off the page image rather than the OCR
   layer, because the order of the letters in Exercise 3's triple decides
   which adjoint its hypothesis is about (see "The two readings of
   Exercise 3" below).

     Exercise 3.  "If ⟨G, F, φ⟩ : X ⇀ A is an adjunction with G full and
     every unit η_x a monic, then every η_x is also epi."

     Exercise 6.  "Given an adjunction ⟨F, G, η, ε⟩ with either F or G
     full, prove that Gε : GFG → G is invertible with inverse ηG :
     G → GFG."

   Note the triple: Exercise 3 writes ⟨G, F, φ⟩ where the table's left
   column and Exercise 5 write ⟨F, G, φ⟩, and Theorem 1 and Exercise 6
   ⟨F, G, η, ε⟩ -- F first.  Under §IV.1's convention ⟨F, G, φ⟩ : X ⇀ A has
   F : X ⟶ A the LEFT adjoint and G : A ⟶ X the RIGHT adjoint.  This
   library's convention (Theory/Adjunction.v) writes F ⊣ U with
   F : D ⟶ C left and U : C ⟶ D right, so for the ⟨F, G, φ⟩ exercises
   the dictionary is

       Mac Lane's G  =  this file's U,      Mac Lane's F  =  this file's F,
       Mac Lane's X  =  this file's D,      Mac Lane's A  =  this file's C.

   Throughout, "the right adjoint is full" means [Full U] and "the left
   adjoint is full" means [Full F].  Every name below carries the suffix
   [_right] or [_left] accordingly; the suffix names WHICH ADJOINT IS
   ASSUMED FULL, never a handedness of the conclusion.  nLab background:
   https://ncatlab.org/nlab/show/adjoint+functor and
   https://ncatlab.org/nlab/show/fully+faithful+functor . *)

(* ** What is delivered, at what strength

   (A) The reusable core, two split-morphism lemmas that are the real
   content of both exercises:

     - [counit_split_mono_of_full_right] : [Full U] makes every counit
       component a [Section] (a split monomorphism), with the left inverse
       exhibited as the named [counit_inv_of_full_right].
     - [unit_split_epi_of_full_left] : [Full F] makes every unit component
       a [Retraction] (a split epimorphism), with the right inverse
       exhibited as [unit_inv_of_full_left].

   Both are proved from NATURALITY of the counit resp. the unit at the
   chosen preimage, together with one triangle identity.  This is shorter
   than the transpose-comparison route (compute ⌊s ∘ ε⌋ and ⌊id⌋, then use
   injectivity of the transpose), and it needs no injectivity lemma at
   all; see "Corrections to the commissioning brief" below.

   (B) Exercise 6.  The law the library did not have is
   [unit_fmap_counit], `η_{Ua} ∘ Uε_a ≈ id`; the other law is the
   pre-existing triangle [fmap_counit_unit].  It is PROVED TWICE, by two
   genuinely different arguments:

     - [unit_fmap_counit_of_full_right] uses (A)'s left inverse s, whose
       U-image IS η_{Ua}, so `η_{Ua} ∘ Uε_a ≈ U(s ∘ ε_a) ≈ U id ≈ id`;
     - [unit_fmap_counit_of_full_left] uses (A)'s right inverse r for
       η_{Ua}: a morphism with a left inverse and a right inverse has them
       coincide ([split_inverses_agree]), so `Uε_a ≈ r` and the law
       follows.

   Packaged componentwise as [fmap_counit_IsIsomorphism_of_full], and AS
   NATURAL TRANSFORMATIONS as

       [whiskered_counit_iso_of_full]
         : Full F + Full U → @Isomorphism ([C, D]) (U ◯ F ◯ U) U

   with forward leg [whiskered_counit] (component `fmap[U] (counit a)`)
   and backward leg [whiskered_unit] (component `unit (U a)`).  The sum
   type is the faithful rendering of Mac Lane's "either F or G full"; the
   two one-hypothesis readings [whiskered_counit_iso_of_full_left] and
   [_right] are `:=` at [inl] and [inr], so both directions are reachable
   by conversion.

   The other handedness is delivered too, at the same strength:
   [fmap_unit_counit_of_full_left]/[_right], the componentwise
   [counit_at_F_IsIsomorphism_of_full], and

       [whiskered_unit_iso_of_full]
         : Full F + Full U → @Isomorphism ([D, C]) (F ◯ U ◯ F) F.

   Note the ROLE SWAP, which is not an accident of presentation: on the
   [U ◯ F ◯ U] side the cheap hypothesis is [Full U] and on the
   [F ◯ U ◯ F] side it is [Full F].

   (C) Exercise 3, in BOTH readings of its printed triple.  With the
   full functor the RIGHT adjoint ([Full U]): [unit_epic_of_full_monic],
   whose engine is [unit_at_UF_of_full_right], `η_{U(F x)} ≈ UF η_x`,
   exactly what (B) buys -- `Uε_{F x}` is invertible and both sides are
   its inverse -- and whose monic hypothesis is genuinely consumed.  With
   the full functor the LEFT adjoint ([Full F]): [unit_epic_of_full_left],
   where the monic hypothesis is idle, and the sharpening it then
   licenses, [unit_iso_of_full_monic] (split epi + monic = iso).

   (D) The two in-tree instances item 3 of the issue asks for, both as a
   [:=] of (B) with no tactic: [reflective_fmap_counit_IsIsomorphism] over
   Construction/Reflective.v and [equiv_fmap_counit_IsIsomorphism] over
   Theory/Equivalence/Adjoint.v.  In both the inverse this file produces
   is read back at [eq_refl] as the unit component; the comparison with
   the DONORS' own inverses is graded in the "Strengths" note below (one
   is `≈`, the other is refuted, and the cause of the refutation is donor
   opacity).

   (E) Non-vacuity: a generic witness separating this file's hypothesis
   from the stronger "full and faithful" under which the reflective case
   was already known, together with its instantiation at [PointedSets].
   Labelled degenerate where it is degenerate.

   Universes, measured on the printed constants with [Set Printing
   Universes] and read off BOTH the binder and the constraint block, since
   here they disagree.  Every headline is over [C : Category@{u u0 u0}]
   and [D : Category@{u1 u2 u2}] -- hom identified with proof in each, and
   expressed by REUSING THE LEVEL VARIABLE IN THE BINDER, so a reader who
   checks only the block concludes "no identification" and is wrong.  The
   blocks carry one equation, [u0 = u2], collapsing the two categories'
   hom-and-proof levels, plus bounds.  No [Set] occurs in any binder or
   block of sections (A)-(D).  In (E), [Full_Erase_of_ZeroObject] carries
   EXPLICIT universe binders because written unannotated it minimizes to
   [C : Category@{u Set Set}] -- a pin, and one that
   [zero_erase_adjunction] over the same [Erase C] does not acquire, so
   it was that definition's own -- while the two [PointedSets] lemmas
   carry the bound [Set < u] that instance's declaration brings with it.
   The one constant that escapes both identifications in its BLOCK is
   [split_inverses_agree@{u u0}], whose public block is EMPTY (its binder
   still reuses the level, being over [Category@{u u0 u0}]).

   Attribution, probed rather than assumed (Test/ProbeFullness368.v).
   For hom = proof there are THREE donors, each rejected ALONE under a
   declared [Constraint ch < cp] while a hom and an identity at those very
   levels are accepted: [Section], [Retraction] and [Monic].  [Functor] is
   NOT among them -- a functor type elaborates at those levels -- so
   attributing the identification to the functor vocabulary would be
   wrong.  For [u0 = u2] the donor is weaker than one might guess: it is
   not [Compose], not [Adjunction] and not [Full], but the mere presence
   of functors in BOTH directions, [Functor] forcing source-hom <=
   target-hom; under a declared [Constraint dh < ch] the type [Cu ⟶ Du] is
   rejected while [Du ⟶ Cu] is accepted.  Neither identification is
   introduced here and neither is claimed unavoidable. *)

(* ** The two readings of Exercise 3

   The page prints ⟨G, F, φ⟩ : X ⇀ A, and issue #368 paraphrases the
   hypothesis faithfully as "the left-listed functor is full".  Read by
   the §IV.1 convention that the first-listed functor of a triple X ⇀ A
   is the left adjoint X ⟶ A, that is fullness of the LEFT adjoint, and
   then the monic hypothesis is idle: [Full F] already makes every η_x a
   split epi ([unit_split_epi_of_full_left]), hence epi with no further
   assumption ([unit_epic_of_full_left]), and what the monic hypothesis
   adds is invertibility ([unit_iso_of_full_monic]).  Read with G the
   RIGHT adjoint -- its role in Theorem 1 and Exercises 5 and 6, though
   not "everywhere" on the page, the dual column of the table listing G
   FIRST as the left adjoint of the opposite adjunction A ⇀ X -- and
   under which the printed hypothesis is not idle, it is
   [unit_epic_of_full_monic]: the monic hypothesis is consumed
   at the CODOMAIN of the two test arrows, not at x, which is why it
   must be assumed at every object, and no splitting of η_x is
   available.

   Whether ⟨G, F, φ⟩ is a misprint for ⟨F, G, φ⟩ is not decidable from
   the page and is not decided here.  Both readings are delivered and
   both are named in Test/ProbeFullness368.v's controls; the
   right-adjoint one is where the content is, the left-adjoint one is
   the literal print.  An earlier draft of this header transcribed the
   triple as ⟨F, G, φ⟩ and on that basis called the issue's paraphrase
   wrong; the page image refutes the transcription, not the issue. *)

(* ** Corrections to the commissioning brief

   1. The brief prescribes a transpose-comparison proof for (A): compute
      ⌊s ∘ ε_a⌋ and ⌊id⌋, find both equal to η_{Ua}, and close by
      injectivity of ⌊-⌋.  That derivation is correct but longer than
      necessary.  Naturality of ε at s does it in three steps -- two
      rewrites and one [exact] -- and uses no injectivity lemma; the same
      remark applies to the dual.  This file takes the naturality route.

   2. The brief prescribes, for [unit_fmap_counit_of_full_left], a
      transpose computation showing that `F(Uε_a)` and `ε_{F(Ua)}` are
      both left inverses of `F η_{Ua}`, which is epi because η_{Ua}
      splits.  That is also correct, and also longer than necessary: with
      η_{Ua} split on both sides, its two inverses coincide and the law is
      immediate.  This file takes the short route and never forms `F η`.

   3. The brief allows two files; the hard rules of the commission allow
      only [Adjunction/Fullness.v] and [Test/ProbeFullness368.v], so items
      (D) and (E) are appended to this file behind mid-file [Require]s
      rather than placed in a satellite.

   4. The brief calls the whiskering mismatch a "PACKAGING HAZARD ...
      measure before choosing".  Measured, it is real and it is a TYPING
      rejection, not a universe one: [Transform] is a class applied to two
      FUNCTOR RECORDS, and `U ◯ (F ◯ U)` and `(U ◯ F) ◯ U`, while they
      agree on [fobj] and on [fmap], differ in their three law fields
      (distinct [Compose_obligation_*] instances), so the two [Transform]
      types are not convertible.  Likewise `U ◯ Id` is not `U` and
      `Id ◯ U` is not `U`.  Hence [whisker_left U counit] lands at
      `U ◯ (F ◯ U) ⟹ U ◯ Id` and [whisker_right unit U] at
      `Id ◯ U ⟹ (U ◯ F) ◯ U`, and NEITHER can be ascribed at the type
      this file's isomorphism needs.  The transformations are therefore
      hand-built at the single parenthesization `U ◯ F ◯ U` (which is
      `(U ◯ F) ◯ U`, [Compose] being left-associative), and the
      identification with the whiskered forms is recorded COMPONENTWISE by
      [eq_refl] ([whiskered_counit_is_whisker_left],
      [whiskered_unit_is_whisker_right]) rather than at record level.  The
      two ascriptions are pinned in Test/ProbeFullness368.v as TYPING
      negatives and the three Leibniz refutations as CONVERSION ones.

   5. The brief asks whether [Adjunction/Opposite.v]'s
      [Opposite_Adjunction] makes (A.2) a [:=] instance of (A.1) at the
      opposite categories.  Measured, and the answer is "available but
      not cheaper".  The component identification IS definitional: with
      [Aop := Opposite_Adjunction A], the term
      `@unit (Opposite D) (Opposite C) U^op F^op Aop x` and
      `@counit C D F U A x` are equal by [eq_refl].  But the passage is
      not a bare [:=]: it needs [Full_op] (Functor/Opposite.v) to turn
      [Full F] into [Full (F^op)], and [Retraction_of_op_Section]
      (Theory/Morphisms/Duality.v) to turn the [Section] in [D^op] that
      (A.1) produces into the [Retraction] in [D] that (A.2) asserts --
      [Section] and [Retraction] are distinct records, so that step is a
      construction and not a conversion.  Since the direct proof is three
      steps and mirrors (A.1) line for line, the direct route is taken.
      The [eq_refl] identification above was measured out of tree and is
      NOT pinned in this file or in the probe; nothing below depends on
      it.  Note in passing the notation hazard it exposes: with
      [Adjunction.Opposite] required, `D^op` on a CATEGORY parses in
      [adjunction_scope] and elaborates as [Opposite_Adjunction D], so
      the measurement had to spell [Opposite D] by name.

   6. The brief's file path for the scanned book is stale; the copy this
      file was read against lives under the user's iCloud Desktop, not
      under ~/dl.  The page is the one the brief names: PDF 101 = printed
      92, and the calibration in doc/plan/books/maclane/pagemap.md is
      correct.

   7. The brief cites `Theory/Adjunction.v:283` for [counit_fmap_unit] and
      `:291` for [fmap_counit_unit]; both are right at the revision this
      file was built on, and the issue's own ":288" is a line of the
      first corollary's proof script.  An earlier draft of this note
      "corrected" the brief to :281 and :289, which are `Qed.` lines.
      Line numbers are not relied on below. *)

(* ** Not delivered

   - Mac Lane §IV.3 Theorem 1 (G faithful ⟺ every ε_a epi; G full ⟺
     every ε_a split monic, whose forward half IS (A) here; hence full and
     faithful ⟺ ε an isomorphism) is Adjunction/FullFaithful.v's (#367).
     Nothing here states or uses a faithfulness characterisation; the one
     [Faithful] stated here is refuted ([Erase_PointedSets_not_Faithful]).
   - No CONVERSE: it is not shown that invertibility of Uε forces either
     adjoint to be full, and no separating example is offered.
   - No claim that [unit_iso_of_full_monic]'s hypotheses are independent,
     and no example of an adjunction with monic non-epi unit components.
   - The [Opposite_Adjunction] identification of correction 5 is measured
     but not pinned: no [Example] in this file or in the probe records it,
     so a later change to [Opposite_Adjunction] would not be caught here.
   - No `≈`-level comparison between this file's inverse and the one
     inside [reflective_counit_iso]: that lemma is closed with [Qed], so
     neither leg of the isomorphism it produces reduces, and no equation
     naming either leg's VALUE is available by conversion (the iso laws
     themselves of course still hold).  The [eq_refl] form is refuted and
     pinned in Test/ProbeFullness368.v; the `≈` form is not attempted and
     is NOT claimed impossible -- what is claimed is that this file does
     not deliver it.  The donor is not modified.
   - No adjunction in which NEITHER adjoint is full and the new law is
     refuted, so the theorem is shown to have satisfiable hypotheses and
     a non-faithful witness, but is not shown to exclude a named
     adjunction.
   - Nothing is registered as an [Instance]; every result here is a plain
     [Definition]/[Lemma], so typeclass resolution is unperturbed.
   - No statement in [StrictCat], and no Leibniz equality between the
     hand-built transformations and the whiskered ones. *)

(* ** A general splitting lemma

   If f has a left inverse s and a right inverse t then s ≈ t, so f ∘ s ≈
   id as well: a two-sided splitting is unique.  Stated over an arbitrary
   category because both handednesses below need it, in C and in D.  This
   is elementary and folklore, and it is IN TREE already: it is
   Theory/Isomorphism.v:307's [comp_inverse_unique] with the arguments
   reordered, which the one-line proof below cites (an earlier draft
   mislocated that donor under Structure/Groupoid.v, which only uses it). *)

Lemma split_inverses_agree {E : Category} {x y : E} (f : x ~> y)
      (s t : y ~> x) : s ∘ f ≈ id → f ∘ t ≈ id → s ≈ t.
Proof. intros Hs Ht. symmetry. exact (comp_inverse_unique f t s Ht Hs). Qed.

Section Fullness.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

Notation "'η' x" := (@unit C D F U A x)
  (at level 9, only parsing).
Notation "'ε' x" := (@counit C D F U A x)
  (at level 9, only parsing).

(* ** (A) The split-morphism core *)

(* The left inverse of ε_a supplied by fullness of the right adjoint: the
   chosen U-preimage of the unit at U a.  [Full]'s [prefmap] is a bare
   section of [fmap] -- no functoriality and no respectfulness is demanded
   of it (Theory/Functor.v) -- so nothing below may rewrite under it; all
   that is used is [fmap_sur]. *)

Definition counit_inv_of_full_right (HU : Full U) (a : C) : a ~> F (U a) :=
  @prefmap C D U HU a (F (U a)) (η (U a)).

Lemma counit_inv_of_full_right_fmap (HU : Full U) (a : C) :
  fmap[U] (counit_inv_of_full_right HU a) ≈ η (U a).
Proof. exact (@fmap_sur C D U HU a (F (U a)) (η (U a))). Qed.

(* Mac Lane §IV.3: G full makes every counit component a split mono.  The
   argument is naturality of ε at s, whose U-image is η, followed by one
   triangle identity. *)

Lemma counit_inv_of_full_right_comp (HU : Full U) (a : C) :
  counit_inv_of_full_right HU a ∘ ε a ≈ id.
Proof.
  rewrite <- (adj_counit_naturality A (counit_inv_of_full_right HU a)).
  rewrite counit_inv_of_full_right_fmap.
  exact (@counit_fmap_unit C D F U A (U a)).
Qed.

Definition counit_split_mono_of_full_right (HU : Full U) (a : C) :
  Section (ε a) :=
  {| section      := counit_inv_of_full_right HU a
   ; section_comp := counit_inv_of_full_right_comp HU a |}.

(* The dual, for the left adjoint: the chosen F-preimage of the counit at
   F x is a right inverse for η_x, so η_x is a split epi. *)

Definition unit_inv_of_full_left (HF : Full F) (x : D) : U (F x) ~> x :=
  @prefmap D C F HF (U (F x)) x (ε (F x)).

Lemma unit_inv_of_full_left_fmap (HF : Full F) (x : D) :
  fmap[F] (unit_inv_of_full_left HF x) ≈ ε (F x).
Proof. exact (@fmap_sur D C F HF (U (F x)) x (ε (F x))). Qed.

Lemma unit_inv_of_full_left_comp (HF : Full F) (x : D) :
  η x ∘ unit_inv_of_full_left HF x ≈ id.
Proof.
  rewrite <- (adj_unit_naturality A (unit_inv_of_full_left HF x)).
  rewrite unit_inv_of_full_left_fmap.
  exact (@fmap_counit_unit C D F U A (F x)).
Qed.

Definition unit_split_epi_of_full_left (HF : Full F) (x : D) :
  Retraction (η x) :=
  {| retract      := unit_inv_of_full_left HF x
   ; retract_comp := unit_inv_of_full_left_comp HF x |}.

(* ** (B) Exercise 6, componentwise *)

(* The law the library did not have.  First proof, from fullness of the
   RIGHT adjoint: η_{Ua} is literally the U-image of the left inverse of
   ε_a, so the composite is the U-image of a composite that is already
   known to be the identity. *)

Lemma unit_fmap_counit_of_full_right (HU : Full U) (a : C) :
  η (U a) ∘ fmap[U] (ε a) ≈ id.
Proof.
  rewrite <- (counit_inv_of_full_right_fmap HU a).
  rewrite <- fmap_comp.
  rewrite counit_inv_of_full_right_comp.
  apply fmap_id.
Qed.

(* Second proof, from fullness of the LEFT adjoint, by a route sharing no
   step with the first: η_{Ua} has a right inverse by (A) and a left
   inverse by the triangle identity, so the two coincide. *)

Lemma unit_fmap_counit_of_full_left (HF : Full F) (a : C) :
  η (U a) ∘ fmap[U] (ε a) ≈ id.
Proof.
  rewrite (split_inverses_agree (η (U a)) (fmap[U] (ε a))
             (unit_inv_of_full_left HF (U a))
             (@fmap_counit_unit C D F U A a)
             (unit_inv_of_full_left_comp HF (U a))).
  exact (unit_inv_of_full_left_comp HF (U a)).
Qed.

Definition unit_fmap_counit (H : Full F + Full U) (a : C) :
  η (U a) ∘ fmap[U] (ε a) ≈ id :=
  match H with
  | inl HF => unit_fmap_counit_of_full_left HF a
  | inr HU => unit_fmap_counit_of_full_right HU a
  end.

(* Exercise 6, componentwise: Uε_a is invertible with inverse η_{Ua}. *)

Definition fmap_counit_IsIsomorphism_of_full (H : Full F + Full U) (a : C) :
  IsIsomorphism (fmap[U] (ε a)) :=
  {| two_sided_inverse := η (U a)
   ; is_right_inverse  := @fmap_counit_unit C D F U A a
   ; is_left_inverse   := unit_fmap_counit H a |}.

(* ** (B) Exercise 6, other handedness, componentwise *)

(* Here the roles of the two hypotheses swap: the cheap one is [Full F],
   because F η_x is then the F-image of a composite already known to be
   the identity. *)

Lemma fmap_unit_counit_of_full_left (HF : Full F) (x : D) :
  fmap[F] (η x) ∘ ε (F x) ≈ id.
Proof.
  rewrite <- (unit_inv_of_full_left_fmap HF x).
  rewrite <- fmap_comp.
  rewrite unit_inv_of_full_left_comp.
  apply fmap_id.
Qed.

Lemma fmap_unit_counit_of_full_right (HU : Full U) (x : D) :
  fmap[F] (η x) ∘ ε (F x) ≈ id.
Proof.
  rewrite <- (split_inverses_agree (ε (F x))
                (counit_inv_of_full_right HU (F x)) (fmap[F] (η x))
                (counit_inv_of_full_right_comp HU (F x))
                (@counit_fmap_unit C D F U A x)).
  exact (counit_inv_of_full_right_comp HU (F x)).
Qed.

Definition fmap_unit_counit (H : Full F + Full U) (x : D) :
  fmap[F] (η x) ∘ ε (F x) ≈ id :=
  match H with
  | inl HF => fmap_unit_counit_of_full_left HF x
  | inr HU => fmap_unit_counit_of_full_right HU x
  end.

Definition counit_at_F_IsIsomorphism_of_full (H : Full F + Full U) (x : D) :
  IsIsomorphism (ε (F x)) :=
  {| two_sided_inverse := fmap[F] (η x)
   ; is_right_inverse  := @counit_fmap_unit C D F U A x
   ; is_left_inverse   := fmap_unit_counit H x |}.

(* ** (B) Exercise 6 as natural transformations

   [Compose] is left-associative, so `U ◯ F ◯ U` denotes `(U ◯ F) ◯ U`,
   and both transformations below are typed at that one parenthesization.
   See correction 4 in the header for why the whiskered forms cannot be
   used directly. *)

Program Definition whiskered_counit : U ◯ F ◯ U ⟹ U := {|
  transform := fun a => fmap[U] (ε a)
|}.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (adj_counit_naturality A f).
Qed.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (adj_counit_naturality A f).
Qed.

Program Definition whiskered_unit : U ⟹ U ◯ F ◯ U := {|
  transform := fun a => η (U a)
|}.
Next Obligation. now rewrite (adj_unit_naturality A (fmap[U] f)). Qed.
Next Obligation. now rewrite (adj_unit_naturality A (fmap[U] f)). Qed.

(* The headline of Exercise 6.  The hypothesis is a sum, which is the
   faithful rendering of "either F or G full"; the two single-hypothesis
   readings below are [inl]/[inr] applications, hence reachable by
   conversion. *)

Program Definition whiskered_counit_iso_of_full (H : Full F + Full U) :
  @Isomorphism ([C, D]) (U ◯ F ◯ U) U := {|
  to   := whiskered_counit
; from := whiskered_unit
|}.
Next Obligation.
  rewrite fmap_id.
  exact (@fmap_counit_unit C D F U A x).
Qed.
Next Obligation.
  rewrite !fmap_id.
  exact (unit_fmap_counit H x).
Qed.

Definition whiskered_counit_iso_of_full_left (HF : Full F) :
  @Isomorphism ([C, D]) (U ◯ F ◯ U) U :=
  whiskered_counit_iso_of_full (inl HF).

Definition whiskered_counit_iso_of_full_right (HU : Full U) :
  @Isomorphism ([C, D]) (U ◯ F ◯ U) U :=
  whiskered_counit_iso_of_full (inr HU).

(* The other handedness, in [D, C]. *)

Program Definition whiskered_unit_F : F ◯ U ◯ F ⟹ F := {|
  transform := fun x => ε (F x)
|}.
Next Obligation. now rewrite (adj_counit_naturality A (fmap[F] f)). Qed.
Next Obligation. now rewrite (adj_counit_naturality A (fmap[F] f)). Qed.

Program Definition whiskered_counit_F : F ⟹ F ◯ U ◯ F := {|
  transform := fun x => fmap[F] (η x)
|}.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (adj_unit_naturality A f).
Qed.
Next Obligation.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (adj_unit_naturality A f).
Qed.

Program Definition whiskered_unit_iso_of_full (H : Full F + Full U) :
  @Isomorphism ([D, C]) (F ◯ U ◯ F) F := {|
  to   := whiskered_unit_F
; from := whiskered_counit_F
|}.
Next Obligation.
  rewrite fmap_id.
  exact (@counit_fmap_unit C D F U A x).
Qed.
Next Obligation.
  rewrite !fmap_id.
  exact (fmap_unit_counit H x).
Qed.

Definition whiskered_unit_iso_of_full_left (HF : Full F) :
  @Isomorphism ([D, C]) (F ◯ U ◯ F) F :=
  whiskered_unit_iso_of_full (inl HF).

Definition whiskered_unit_iso_of_full_right (HU : Full U) :
  @Isomorphism ([D, C]) (F ◯ U ◯ F) F :=
  whiskered_unit_iso_of_full (inr HU).

(* ** (C) Exercise 3, with the RIGHT adjoint full

   The engine.  Under [Full U] the arrow Uε_{F x} is invertible by (B),
   and both η_{U(F x)} and UF η_x are its inverse on the left, so the two
   agree.  Only associativity and the two facts are used. *)

Lemma unit_at_UF_of_full_right (HU : Full U) (x : D) :
  η (U (F x)) ≈ fmap[U] (fmap[F] (η x)).
Proof.
  assert (Hr : fmap[U] (ε (F x)) ∘ fmap[U] (fmap[F] (η x)) ≈ id).
  { rewrite <- fmap_comp.
    rewrite (@counit_fmap_unit C D F U A x).
    apply fmap_id. }
  rewrite <- (id_right (η (U (F x)))).
  rewrite <- Hr.
  rewrite comp_assoc.
  rewrite (unit_fmap_counit_of_full_right HU (F x)).
  now rewrite id_left.
Qed.

(* Exercise 3 read with G the right adjoint: U full, every unit component
   monic, conclusion every unit component epi.  The monic hypothesis is used
   at the CODOMAIN z of the two test arrows, never at x -- which is why it
   must be assumed for every object and not merely at x. *)

Lemma unit_epic_of_full_monic (HU : Full U)
      (Hm : ∀ y : D, Monic (η y)) (x : D) : Epic (η x).
Proof.
  construct.
  apply (@monic D _ _ (η z) (Hm z)).
  rewrite <- !(adj_unit_naturality A).
  rewrite (unit_at_UF_of_full_right HU x).
  rewrite <- !fmap_comp.
  now rewrite X.
Qed.

(* ** (C) Exercise 3, with the LEFT adjoint full (the literal print)

   With the LEFT adjoint full the conclusion needs no monic hypothesis at
   all, η_x being a split epi outright. *)

Lemma unit_epic_of_full_left (HF : Full F) (x : D) : Epic (η x).
Proof. now apply retractions_are_epic, unit_split_epi_of_full_left. Qed.

(* ... and the monic hypothesis then upgrades the conclusion from epi to
   invertible, which is the sharpest statement that reading supports. *)

Definition unit_iso_of_full_monic (HF : Full F)
           (Hm : ∀ y : D, Monic (η y)) (x : D) : IsIsomorphism (η x).
Proof.
  unshelve econstructor.
  - exact (unit_inv_of_full_left HF x).
  - exact (unit_inv_of_full_left_comp HF x).
  - apply (@monic D _ _ (η x) (Hm x)).
    rewrite comp_assoc.
    rewrite unit_inv_of_full_left_comp.
    now rewrite id_left, id_right.
Defined.

(* ** A by-product

   Under fullness of either adjoint the unit is invertible at every object
   in the image of U -- which is (B) read backwards, the inverse being
   Uε_a. *)

Definition unit_at_U_IsIsomorphism_of_full (H : Full F + Full U) (a : C) :
  IsIsomorphism (η (U a)) :=
  {| two_sided_inverse := fmap[U] (ε a)
   ; is_right_inverse  := unit_fmap_counit H a
   ; is_left_inverse   := @fmap_counit_unit C D F U A a |}.

End Fullness.

(* ** Componentwise identification with the whiskered transformations

   Recorded at Leibniz equality, which is the strongest grade available:
   the record-level identifications do not typecheck (correction 4), and
   are refuted in Test/ProbeFullness368.v.  These two [Example]s, and the
   two inverse readbacks in section (D) below, are the file's only four
   uses of [=] on morphisms, and all four are deliberately strict. *)

Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.

Example whiskered_counit_is_whisker_left
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (a : C) :
  transform[@whiskered_counit C D F U A] a
    = transform[U ⊳ (@counit _ _ _ _ (@Adjunction_to_Transform C D F U A))] a.
Proof. reflexivity. Qed.

Example whiskered_unit_is_whisker_right
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (a : C) :
  transform[@whiskered_unit C D F U A] a
    = transform[(@unit _ _ _ _ (@Adjunction_to_Transform C D F U A)) ⊲ U] a.
Proof. reflexivity. Qed.

(* ** (D) The two in-tree instances the issue asks for

   From here on [Construction/Subcategory.v] is in scope, and it exports
   its OWN [Full] (a predicate on a [Subcategory], first argument a
   [Category]).  That name therefore shadows Theory/Functor.v's from this
   point down; the mid-file [Require] idiom of Functor/Diagonal.v keeps
   the development above untouched, and the one place the functor notion
   is still needed is spelled [Functor.Full] in full. *)

Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

(* [Adjunction.Natural.Transformation] is in scope from the [Example]s
   above and exports its own [unit]/[counit] (fields of the unit-counit
   class), so the hom-set-form [unit]/[counit] must be named through this
   alias from here down.  The alias is [HomSetAdj] rather than the
   obvious [Adj] because [Instance/Adj.v] already declares a constant
   [Adj], and a module of that name in scope beside it is a collision
   waiting to mis-resolve. *)

Module HomSetAdj := Category.Theory.Adjunction.

(* A full reflective subcategory: the inclusion is full, so the RIGHT
   adjoint is full and the [inr] branch applies.  [Construction/
   Reflective.v]'s [reflective_counit_iso] concludes something STRONGER --
   that the counit itself is invertible, not merely its U-image -- from
   something stronger, since that inclusion is faithful as well as full.
   What is recorded here is that the weaker conclusion is an instance of
   this file's theorem: the passage is a [:=] with no tactic. *)

Definition reflective_fmap_counit_IsIsomorphism {C : Category}
  {S : Subcategory C} (R : Reflective S) (x : Sub C S) :
  IsIsomorphism
    (fmap[Incl C S]
       (@HomSetAdj.counit (Sub C S) C (reflector R) (Incl C S)
                (reflective_adj R) x)) :=
  @fmap_counit_IsIsomorphism_of_full (Sub C S) C (reflector R) (Incl C S)
    (reflective_adj R)
    (inr (Full_Implies_Full_Functor C S (reflective_full R))) x.

(* The inverse this file produces is the unit at [Incl x], on the nose. *)

Example reflective_fmap_counit_inverse {C : Category}
  {S : Subcategory C} (R : Reflective S) (x : Sub C S) :
  two_sided_inverse
    (IsIsomorphism := reflective_fmap_counit_IsIsomorphism R x)
    = @HomSetAdj.unit (Sub C S) C (reflector R) (Incl C S)
        (reflective_adj R) (Incl C S x)
  := eq_refl.

(* An adjoint equivalence: the LEFT adjoint is the one the tree proves
   full ([Equivalence_Full]), so the [inl] branch is taken -- no in-tree
   [Full] of the quasi-inverse was found, so [inr] is not exercised --
   and the instance is again a [:=]. *)

Require Import Category.Theory.Equivalence.

Definition equiv_fmap_counit_IsIsomorphism {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (d : D) :
  IsIsomorphism
    (fmap[@quasi_inverse C D F E]
       (@HomSetAdj.counit D C F (@quasi_inverse C D F E)
          (equiv_adjunction E) d)) :=
  @fmap_counit_IsIsomorphism_of_full D C F (@quasi_inverse C D F E)
    (equiv_adjunction E) (inl (Equivalence_Full E)) d.

Example equiv_fmap_counit_inverse {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (d : D) :
  two_sided_inverse
    (IsIsomorphism := equiv_fmap_counit_IsIsomorphism E d)
    = @HomSetAdj.unit D C F (@quasi_inverse C D F E) (equiv_adjunction E)
        (@quasi_inverse C D F E d)
  := eq_refl.

(* The donor's own counit isomorphism is about the counit itself; its
   inverse, pushed through [quasi_inverse], agrees with this file's up to
   `≈` -- both are inverse to the same arrow. *)

Lemma equiv_fmap_counit_inverse_agrees {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (d : D) :
  @HomSetAdj.unit D C F (@quasi_inverse C D F E) (equiv_adjunction E)
      (@quasi_inverse C D F E d)
    ≈ fmap[@quasi_inverse C D F E]
        (two_sided_inverse
           (IsIsomorphism := equiv_adjunction_counit_iso E d)).
Proof.
  pose proof (@HomSetAdj.fmap_counit_unit D C F
                (@quasi_inverse C D F E) (equiv_adjunction E) d) as Ht.
  pose proof (@is_left_inverse D _ _ _
                (equiv_adjunction_counit_iso E d)) as Hk.
  rewrite <- (id_left (@HomSetAdj.unit D C F
                         (@quasi_inverse C D F E) (equiv_adjunction E)
                         (@quasi_inverse C D F E d))).
  rewrite <- fmap_id.
  rewrite <- Hk.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite Ht.
  now rewrite id_right.
Qed.

(* ** (E) Non-vacuity, and what the hypothesis does NOT force

   The two instances of (D) both have a right adjoint that is full AND
   faithful, so neither separates this file's hypothesis from the
   stronger one under which [reflective_counit_iso] already worked.  The
   witness below does separate them, and it is generic: whenever C has a
   ZERO object, the erasing functor [Erase C : C ⟶ 1] is FULL -- every
   hom-set of C is inhabited, by the zero morphism -- and it acquires a
   left adjoint, the constant functor at the initial object
   ([Initial_Erase_Adjunction], consumed here, not rebuilt).  Argued, not
   proved here: it is not faithful as soon as C has two distinct parallel
   arrows, and its counit components are invertible only at objects
   isomorphic to the zero object -- what IS proved is the [PointedSets]
   instance below -- while their U-images are, this file's theorem
   applying.

   The witness is DEGENERATE in one specific and disclosed respect: the
   target category of U is 1, where every arrow is invertible, so the
   CONCLUSION of Exercise 6 is true there for a reason that has nothing to
   do with the theorem.  What the witness genuinely exhibits is that the
   HYPOTHESIS [Full U] is satisfiable by a functor that is not faithful
   and whose counit is not invertible, which is exactly the gap between
   this file and Construction/Reflective.v. *)

Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.One.
Require Import Category.Functor.Diagonal.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Sets.Pointed.

Definition Full_Erase_of_ZeroObject@{o h +} {C : Category@{o h h}}
  (Z : ZeroObject C) : Functor.Full (Erase C).
Proof.
  unshelve econstructor.
  - exact (fun x y _ => @zero_mor C Z x y).
  - intros x y g; destruct g; reflexivity.
Defined.

Definition zero_erase_adjunction {C : Category} (Z : ZeroObject C) :
  @Diagonal C _1 (@initial_obj C (@zero_initial C Z)) ⊣ Erase C :=
  Initial_Erase_Adjunction (@zero_initial C Z).

Definition zero_erase_fmap_counit_IsIsomorphism {C : Category}
  (Z : ZeroObject C) (a : C) :
  IsIsomorphism
    (fmap[Erase C]
       (@HomSetAdj.counit C _1
          (@Diagonal C _1 (@initial_obj C (@zero_initial C Z)))
          (Erase C) (zero_erase_adjunction Z) a)) :=
  @fmap_counit_IsIsomorphism_of_full C _1
    (@Diagonal C _1 (@initial_obj C (@zero_initial C Z)))
    (Erase C) (zero_erase_adjunction Z)
    (inr (Full_Erase_of_ZeroObject Z)) a.

(* [PointedSets] has a zero object, so the above applies to it; and there
   the right adjoint is provably NOT faithful. *)

Lemma Erase_PointedSets_not_Faithful :
  Faithful (Erase PointedSets) → False.
Proof.
  intros HF.
  assert (Hid : @id PointedSets PointedTwo
                  ≈ @pointed_const PointedTwo PointedTwo).
  { apply (@fmap_inj PointedSets _1 (Erase PointedSets) HF).
    reflexivity. }
  specialize (Hid (Datatypes.Some ttt)).
  simpl in Hid.
  contradiction.
Qed.

(* And its counit at the two-point pointed set is not invertible, though
   its [Erase]-image is: the [Erase]-image lives in 1. *)

Lemma pointed_counit_not_IsIsomorphism :
  IsIsomorphism
    (@HomSetAdj.counit PointedSets _1
       (@Diagonal PointedSets _1
          (@initial_obj PointedSets (@zero_initial PointedSets
                                       PointedSets_Zero)))
       (Erase PointedSets) (zero_erase_adjunction PointedSets_Zero)
       PointedTwo) → False.
Proof.
  intros HI.
  pose proof (@is_right_inverse PointedSets _ _ _ HI) as Hr.
  rewrite (@zero_unique PointedSets
             (@zero_initial PointedSets PointedSets_Zero) PointedTwo
             _ (@pointed_const PointedOne PointedTwo)) in Hr.
  specialize (Hr (Datatypes.Some ttt)).
  simpl in Hr.
  contradiction.
Qed.
