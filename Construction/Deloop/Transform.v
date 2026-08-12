Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.

Generalizable All Variables.

(** * Natural transformations between group homomorphisms are conjugations *)

(* nLab:      https://ncatlab.org/nlab/show/natural+transformation
   nLab:      https://ncatlab.org/nlab/show/delooping
   nLab:      https://ncatlab.org/nlab/show/automorphism+2-group
   Wikipedia: https://en.wikipedia.org/wiki/Inner_automorphism
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §I.4, printed p. 18 (Exercise 3)
   Book:      Awodey, "Category Theory", 2nd ed., Oxford Logic Guides 52,
              2010, §7.7 ("Functor categories"), Example 7.21, printed
              pp. 167-168
   Book:      Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
              September 2005), §7.7, Example 7.21, printed p. 175
   Book:      Riehl, "Category Theory in Context", Exercise 1.4.ii,
              printed p. 30

   CITATION NOTE.  AWODEY CHANGED THE FORMULA BETWEEN EDITIONS, and both
   printings have now been read.  For a transformation ϑ : f → g between
   homomorphisms f, g : G → H the FIRST edition (printed p. 175) writes

       f(x) · h = h · g(x),    equivalently    h⁻¹ · f(x) · h = g(x),

   and calls ϑ "an inner automorphism y ↦ h⁻¹ · y · h of H (called
   conjugation by h), that takes f to g"; the SECOND edition (printed p. 167)
   writes

       g(x) · h = h · f(x),    equivalently    g(x) = h · f(x) · h⁻¹,

   and calls ϑ "an inner automorphism y → h · y · h⁻¹ of H (called
   conjugation by h) that takes f to g".  (Both quotations, and those below,
   normalize the superscript inverse and the inter-word spacing; nothing else
   is changed — the two printings really do use different arrow glyphs and
   different comma placement in that sentence.)

   The two differ in which of the source and the target multiplies on the
   left of h.  Each edition is internally consistent, and the two forms are
   carried to each other by h ↦ h⁻¹: the first edition's is exactly
   [transform_iff_conjugate_SWAPPED] below, whose proof derives it from the
   second edition's [transform_iff_conjugate] by doing nothing but replacing
   h by h⁻¹.  THIS FILE FOLLOWS THE SECOND EDITION, because that is the
   orientation the library's own composition order produces — see the
   COMPOSITION ORDER note below, which derives it rather than assuming it.
   Every Awodey quotation below is from the second printing unless the first
   is named.

   The catalog entry behind this file cites the FIRST edition, as
   Structure/Groupoid.v also does for §7.7, and ITS PARAPHRASE IS CORRECT FOR
   THE EDITION IT CITES: nothing here corrects it, and no erratum against it
   is claimed anywhere in this file.

   Mac Lane's Exercise 3 is cited by location only: its content is what this
   file proves, but its wording is not quoted, not having been checked
   against the book.

   Two monoid homomorphisms S, T : M → N correspond to two functors between
   the deloopings B M ⟶ B N ([Deloop_map] and [Deloop_unmap] below; the round
   trip through a homomorphism is the identity on the nose, the one through a
   functor on its morphism part).  A natural transformation between those two
   functors has exactly one component, at the single object, so it is a single
   element h of N; and its one naturality square says

       T g · h  ≈  h · S g       for every g in M,

   which for a group N is

       T g  ≈  h · S g · h⁻¹,

   the statement that h conjugates S into T.  This file proves that
   correspondence in both directions, at the level of setoids, and draws the
   consequence Awodey draws: since h is invertible when N is a group, every
   such transformation is invertible, so the functor category is a groupoid.

   Contents:

       Deloop_map f              the functor B M ⟶ B N of a homomorphism f
       Deloop_unmap F            the homomorphism of a functor; a left inverse
                                 of [Deloop_map] by [eq_refl]
       deloop_compose_mon_op     composition in B N IS the product of N
       Intertwines F G h         T g · h ≈ h · S g, for every g
       transform_intertwines     a transformation's component intertwines
       intertwines_transform     and conversely
       transform_iff_intertwines the two together (monoids, no inverses)
       transform_intertwiner_iso the correspondence as a bijection of setoids
       Conjugates F G h          T g ≈ h · S g · h⁻¹, for every g
       conjugates_is_conjugation and that IS Structure/Groupoid.v's
                                 [conjugate], by [eq_refl]
       transform_conjugator_iso  the same bijection over a group, onto the
                                 set of CONJUGATING elements
       transform_conjugator_hom  and at two homomorphisms: B S ⟹ B T IS the
                                 set of elements conjugating S into T
       transform_iff_conjugate   Mac Lane §I.4 Exercise 3, both directions
       transform_iff_conjugate_SWAPPED
                                 the same statement with h replaced by h⁻¹ —
                                 Awodey's first-edition orientation
       conjugates_inverse        h⁻¹ conjugates the other way
       Fun_IsGroupoid            [C, D] is a groupoid whenever D is
       Deloop_Fun_IsGroupoid     Awodey's consequence: H^G is a groupoid
       deloop_ginv_conjugates    and the inverse conjugates back, by h⁻¹
       abelian_conjugates_agree  the statement is EMPTY for abelian targets
       Bool_Xor_abelian, Z3_abelian   which the older witnesses are
       S3_hom_conjugate          a nonabelian witness: two homomorphisms
                                 Z/2 → S3 conjugate by a non-central element
                                 ([S3_conjugator_noncentral])
       S3_conjugation_moves      and the conjugation is not the identity
       Deloop_S3_two_objects     H^G has two provably distinct objects
       S3_no_transform_trivial   and two with NO arrow between them, so it is
                                 not connected ([Deloop_Fun_S3_not_connected])
       Deloop_Fun_S3_not_deloop  hence not equivalent to the delooping of any
                                 MONOID — not merely of any group — in either
                                 direction

   The delooping itself, and the monoid/group records [MonObject] and
   [GrpObject], are Construction/Deloop.v; that file's header states that "the
   functor-level half of the dictionary — that functors between deloopings are
   exactly monoid homomorphisms" is deliberately left out of it, and
   [Deloop_map]/[Deloop_unmap] below are that half.  [MonHom], [IsGroupoid],
   [ginv] and the symmetric group [S3_Grp] come from Structure/Groupoid.v. *)

(* What the exercise is about, and the two ways to get it wrong

   nLab:  https://ncatlab.org/nlab/show/automorphism+2-group
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",
          Trans. Amer. Math. Soc. 58(2), 1945

   Mac Lane's Exercise 3 in §I.4 is about as small as a complete example of a
   natural transformation gets.  A group has one object, so a functor out of
   it has nothing to do on objects and is exactly a homomorphism; a natural
   transformation between two such functors has one component, and the
   naturality square — an equation between two composites of three arrows —
   becomes an equation between two products of three elements.  The answer,
   conjugacy, is a fact about groups that predates category theory entirely;
   what the exercise shows is that naturality REPRODUCES it, with no
   group-theoretic input beyond the definitions.  That is the phenomenon the
   1945 paper was written about, here at its smallest.

   The reading upward is the theory of 2-groups.  The delooping B G of a
   group is a one-object groupoid; the functor category B H ^ B G is a
   groupoid ([Deloop_Fun_IsGroupoid]) whose objects CORRESPOND to the
   homomorphisms G → H — they are functors, and the round trip through a
   functor is an identity only on the morphism part
   ([Deloop_map_unmap_fmap], [Deloop_map_unmap_fobj]) — and whose arrows are
   the conjugacies between them.  Two consequences
   are immediate from the definitions below rather than cited: two objects
   are joined by an arrow exactly when the homomorphisms are conjugate
   ([transform_iff_conjugate]), so the connected components are the conjugacy
   classes; and [Intertwines] at F = G says exactly that h commutes with
   every S a, so the endomorphisms of the object S are the centralizer in H
   of the image of S.  The nLab records the corresponding automorphism
   2-group as AUT(H) ≔ Aut(B H), presented by the crossed module
   H →Ad Aut(H) (nLab, "automorphism 2-group"); this file stops at the
   groupoid and builds no 2-group, but the non-connectedness witness at the
   end is exactly a pair of homomorphisms in different conjugacy classes.

   TWO TRAPS, both addressed below rather than in prose only, and both
   scoped there to exactly where they bite.

   The first is VACUITY.  In an abelian group conjugation is the identity:
   h · a · h⁻¹ ≈ a for every h.  So over an abelian target the conjugation
   theorem, however carefully stated, distinguishes nothing at all, and any
   demonstration built on such a target is worthless as evidence that the
   statement has content.  That is not left as a warning here:
   [abelian_conjugates_agree] PROVES that a conjugating element between two
   functors into an abelian target forces the two functors to agree on every
   arrow, and [Bool_Xor_abelian] and [Z3_abelian] show that Z/2 and Z/3 —
   the tree's only groups until Structure/Groupoid.v added S3 — are abelian,
   hence useless for this statement ([Bool_conjugates_agree] spells the
   instantiation out at Z/2).  The witness used here is therefore the
   symmetric group S3, which Structure/Groupoid.v introduced as the tree's
   first nonabelian group: the two homomorphisms Z/2 → S3 picking out the
   transpositions a and c are conjugate by the three-cycle r
   ([S3_hom_conjugate]), the conjugation moves them
   ([S3_conjugation_moves]), and the conjugating element is non-central
   ([S3_conjugator_noncentral], which is that file's [S3_not_abelian] read as
   a statement about r).  [S3_conjugation_needs_nonabelian] closes the loop by
   DERIVING that S3 is nonabelian from those two facts together, so the
   witness cannot be degenerate without contradicting itself.

   The second is COMPOSITION ORDER.  In this library f ∘ g means "g first",
   and Construction/Deloop.v takes `compose f g := mon_op f g` — the monoid
   product in the same argument order, which [deloop_compose_mon_op] below
   restates as an equation holding by [eq_refl].  Reading naturality
   (`fmap[G] f ∘ η ≈ η ∘ fmap[F] f`, Theory/Natural/Transformation.v) through
   that gives, for η : S ⟹ T with component h,

       T g · h ≈ h · S g,       hence      T g ≈ h · S g · h⁻¹.

   So the TARGET of the transformation multiplies on the LEFT of h, and it is
   the target that is the conjugate of the source.  That is Awodey's
   SECOND-EDITION orientation (Example 7.21, 2nd ed. p. 167, quoted with the
   superscript inverse and inter-word spacing normalized): "what is a natural
   transformation between two group homomorphisms f, g : G → H? Such a map
   ϑ : f → g would be an element h ∈ H such that for every x ∈ G, we have
   g(x) · h = h · f(x) or, equivalently, g(x) = h · f(x) · h⁻¹."  Source f,
   target g, target on the left — the same way round as [Intertwines] and
   [Conjugates] below.  ([transform_intertwines] is literally the [naturality]
   field: it is proved by `naturality n ttt ttt` with no rewriting at all,
   which is the sharpest available check that no side has been silently
   swapped.)

   HOW MUCH THE DIRECTION MATTERS, exactly.  Not as much as "trap" suggests
   at the ∃-quantified level.  [transform_iff_conjugate] and its
   source-on-the-left twin [transform_iff_conjugate_SWAPPED] are both proved
   below, and both are biconditionals with the SAME left-hand side, so their
   two right-hand sides are equivalent in this file by composing them; the
   proof actually carried out is the swapped one from the standard one, by
   sending h to h⁻¹ ([conjugates_inverse]) and nothing else.  Neither
   orientation is a false statement, and neither is Awodey's first edition,
   whose formula is the swapped one (see the CITATION NOTE above).
   What the direction does fix is every statement made about a GIVEN h —
   [Intertwines], [Conjugates], [transform_intertwines], [S3_hom_conjugate],
   [deloop_ginv_conjugates] — where exchanging the sides changes the claim
   rather than merely its notation, and where getting it backwards would
   quietly mean something else about a named element.  The opposite
   convention for delooping — composition as `mon_op g f` — would deloop the
   opposite monoid (Construction/Deloop/Opposite.v) and exchange the two
   sides of every equation in this file. *)

(* The obligations in this file are all elementary: for each of the two
   setoid bijections below, one [Equivalence], two [Proper]s and the two
   round trips; and for the S3 witness, one unit law and one finite case
   check over the multiplication table.  None of them wants [cat_simpl]'s
   program machinery, so the ambient obligation tactic is switched off,
   following Construction/Deloop.v and Instance/CMon.v. *)
#[local] Obligation Tactic := idtac.

(** ** Functors between deloopings are monoid homomorphisms *)

(* One half of the functor-level dictionary: a homomorphism f : M → N becomes
   a functor B M ⟶ B N.  There is nothing to do on objects, and the three
   functor laws are the three homomorphism laws by projection — respecting
   `≈`, preserving the unit, preserving the product — in the orientation
   [MonHom] states them, so no obligation is generated.

   ([Build_Functor] is applied to explicit arguments rather than written with
   record syntax because the record fields alone do not determine the two
   categories.) *)
Definition Deloop_map {M N : MonObject} (f : MonHom M N) :
  Deloop M ⟶ Deloop N :=
  @Build_Functor (Deloop M) (Deloop N)
    (fun _ => ttt)                              (* nothing to choose on objects *)
    (fun _ _ a => f a)                          (* an arrow is an element *)
    (fun _ _ => mon_map_respects f)
    (fun _ => mon_map_unit f)                   (* fmap id ≈ id  is  f 1 ≈ 1 *)
    (fun _ _ _ a b => mon_map_op f a b).        (* fmap (a ∘ b) is f (a · b) *)

(* And the other half: a functor between deloopings is a homomorphism, its
   action on the single hom-set.  Again every homomorphism law is a functor
   law by projection. *)
Definition Deloop_unmap {M N : MonObject} (F : Deloop M ⟶ Deloop N) :
  MonHom M N := {|
  mon_map          := fun a => @fmap _ _ F ttt ttt a;
  mon_map_respects := @fmap_respects _ _ F ttt ttt;
  mon_map_unit     := @fmap_id _ _ F ttt;
  mon_map_op       := fun a b => @fmap_comp _ _ F ttt ttt ttt a b
|}.

(* The round trip through a homomorphism is the identity ON THE NOSE — an
   equality of whole records, law fields included, holding by [eq_refl]
   because [Set Primitive Projections] gives records definitional eta and
   because neither construction rebuilds a single field.  This is the same
   strength as [hom_monoid_Deloop] in Construction/Deloop.v, and it is what
   licenses reading the statements below, which are phrased with
   [Deloop_unmap], as statements about the homomorphisms one started with. *)
Example Deloop_unmap_map {M N : MonObject} (f : MonHom M N) :
  Deloop_unmap (Deloop_map f) = f := eq_refl.

(* The round trip through a functor is the identity on the morphism part,
   again by [eq_refl], and agrees with F at every object — but only
   propositionally there, by a case split.  [poly_unit] is an ordinary
   inductive type with no definitional eta (a variable x : poly_unit is not
   convertible to [ttt], which was checked before this comment was written),
   so the object map of [Deloop_map (Deloop_unmap F)] — the constant function
   at [ttt] — and that of F are not the same term.  The whole functors are
   therefore NOT claimed equal, and nothing below needs them to be. *)
Example Deloop_map_unmap_fmap {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (a : carrier M) :
  @fmap _ _ (Deloop_map (Deloop_unmap F)) ttt ttt a = @fmap _ _ F ttt ttt a
  := eq_refl.

Example Deloop_map_unmap_fobj {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (x : Deloop M) : fobj[Deloop_map (Deloop_unmap F)] x = fobj[F] x.
Proof. destruct (fobj[F] x); reflexivity. Qed.

(* Distinct homomorphisms give distinct functors, hence distinct OBJECTS of
   the functor category.  The type ascription on the projected morphism map
   is what makes it non-dependent, so that [f_equal] applies: the hom-set of
   a delooping does not vary with the object. *)
Lemma Deloop_map_distinct {M N : MonObject} (f g : MonHom M N) (a : carrier M) :
  (f a = g a → False) → Deloop_map f = Deloop_map g → False.
Proof.
  intros Hne Heq.
  apply Hne.
  exact (f_equal
           (fun F : Deloop M ⟶ Deloop N => (@fmap _ _ F ttt ttt a : carrier N))
           Heq).
Qed.

(** ** The composition-order convention, checked *)

(* Composition in a delooping IS the monoid product, in the same argument
   order: the two are the same function, not merely equivalent.  Every
   equation in this file is read through this one, so it is recorded as a
   proof rather than as a remark.  (The objects must be supplied explicitly —
   the hom is the same setoid at every pair, so nothing in a composite
   determines them.) *)
Example deloop_compose_mon_op (N : MonObject) :
  @compose (Deloop N) ttt ttt ttt = @mon_op N := eq_refl.

(** ** The characterization, for monoids *)

Section Intertwining.

Context {M N : MonObject}.
Context (F G : Deloop M ⟶ Deloop N).

(* h intertwines F and G when   G a · h ≈ h · F a   for every a.  This is the
   naturality square of a transformation F ⟹ G written multiplicatively, and
   it is Awodey's form of the condition: no inverses appear, so it is stated
   for monoids and specializes to groups below.

   Note which side is which: the TARGET G multiplies on the left of h, the
   SOURCE F on the right. *)
Definition Intertwines (h : carrier N) : Type :=
  ∀ a : carrier M, mon_op (Deloop_unmap G a) h ≈ mon_op h (Deloop_unmap F a).

(* Forward direction.  A natural transformation has a single component, at
   the single object, and that component intertwines — this is the
   [naturality] field itself, instantiated at the one object twice, with no
   rewriting whatever.  That the proof term is exactly `naturality n ttt ttt`
   is the check that the two sides of the equation have not been swapped. *)
Definition transform_intertwines (n : F ⟹ G) : Intertwines (transform n ttt) :=
  naturality n ttt ttt.

(* Backward direction.  An intertwining element is a natural transformation:
   take it as the component at the only object.  (The objects are destructed
   because a bare variable of [poly_unit] is not convertible to [ttt] —
   [fmap] at a variable object is not the same term as [fmap] at [ttt] — and
   after the case split the naturality square is the intertwining equation
   verbatim.) *)
Definition intertwines_transform (h : carrier N) (I : Intertwines h) : F ⟹ G.
Proof.
  refine (@Build_Transform' _ _ F G (fun _ => h) _).
  intros x y a.
  destruct x, y.
  exact (I a).
Defined.

(* The component of the transformation built from h is h, by [eq_refl]. *)
Example intertwines_transform_component (h : carrier N) (I : Intertwines h) :
  transform (intertwines_transform h I) ttt = h := eq_refl.

(* The two directions together.  Both sides are data — a transformation one
   way, an element with its equations the other — so this is Lib/Foundation.v's
   Type-valued `↔` ([iffT]) and `∃` ([sigT]), not the propositional pair. *)
Theorem transform_iff_intertwines : (F ⟹ G) ↔ ∃ h : carrier N, Intertwines h.
Proof.
  split.
  - intro n.
    exists (transform n ttt).
    exact (transform_intertwines n).
  - intros [h I].
    exact (intertwines_transform h I).
Defined.

(** ** The correspondence at the level of setoids *)

(* Setoid-level care, which is what the task behind this file asks for: not
   merely that the two collections are inhabited together, but that they
   CORRESPOND.  They do, and the correspondence is a bijection of setoids —
   an isomorphism in [Sets] — between

     - the transformations F ⟹ G under [Transform_Setoid], where two
       transformations are identified when their components agree at every
       object; and

     - the INTERTWINING elements of N, i.e. the elements h carrying a proof
       of [Intertwines h], where two are identified when the ELEMENTS are
       `≈`-equal in N.

   Intertwining, not conjugating: N is a bare monoid here, with no inverses,
   so "h conjugates F into G" has nothing to refer to yet.  The version over
   a group — the literal set of CONJUGATING elements, cut out by [Conjugates]
   — is [transform_conjugator_iso] below, where the two conditions on h agree
   by [conjugates_iff_intertwines].

   The second setoid ignores the intertwining witness.  That is deliberate
   and is the honest reading of "the set of elements": the witness is proof
   content with no equality of its own, and identifying elements by their
   underlying element of N makes the collection the sub-setoid of N cut out
   by the condition.  It is also forced by the first setoid, which sees only
   components.

   The isomorphism is in [Sets], where it says exactly what a bijection of
   setoids says: two `≈`-respecting maps, inverse to each other up to `≈`.
   Nothing in this file is stated in [Cat], where `≅` would mean only
   equivalence of categories.

   What is NOT claimed: nothing here says the correspondence is a group
   isomorphism, or natural in F and G, or that it identifies composition of
   transformations with multiplication in N.  (Vertical composition does take
   components to composites — [nat_compose]'s component at x is the composite
   of the two components, and composition in a delooping is [mon_op] — but
   for three different functors F ⟹ G ⟹ K that composition is a category's,
   not a monoid's, and the statement is not made here.) *)

Definition Intertwiner : Type := ∃ h : carrier N, Intertwines h.

Program Definition Intertwiner_Setoid : Setoid Intertwiner := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - now transitivity (`1 y).
Qed.

Definition Deloop_Transforms : SetoidObject := {|
  carrier   := F ⟹ G;
  is_setoid := Transform_Setoid
|}.

Definition Deloop_Intertwiners : SetoidObject := {|
  carrier   := Intertwiner;
  is_setoid := Intertwiner_Setoid
|}.

(* A transformation to its component, with the naturality square read as the
   intertwining condition. *)
Program Definition transform_intertwiner :
  Deloop_Transforms ~{Sets}~> Deloop_Intertwiners := {|
  morphism := fun n => existT _ (transform n ttt) (transform_intertwines n)
|}.
Next Obligation.
  intros n1 n2 Hn.
  exact (Hn ttt).
Qed.

(* And back. *)
Program Definition intertwiner_transform :
  Deloop_Intertwiners ~{Sets}~> Deloop_Transforms := {|
  morphism := fun p => intertwines_transform (`1 p) (`2 p)
|}.
Next Obligation.
  intros p q Hpq x; simpl.
  exact Hpq.
Qed.

(* The bijection.  One round trip is [reflexivity], the two elements being
   convertible; the other needs the case split on the object, because a
   transformation's component at a variable object is only reachable from its
   component at [ttt] after that variable is known to be [ttt]. *)
Program Definition transform_intertwiner_iso :
  Deloop_Transforms ≅[Sets] Deloop_Intertwiners := {|
  to   := transform_intertwiner;
  from := intertwiner_transform
|}.
Next Obligation.
  intro p; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n x; simpl.
  destruct x.
  reflexivity.
Qed.

End Intertwining.

Arguments Intertwines {M N} F G h.
Arguments Intertwiner {M N} F G.

(** ** The characterization, for groups: Mac Lane §I.4 Exercise 3 *)

Section GroupConjugation.

Context {M : MonObject}.
Context {Grp : GrpObject}.
Context (F G : Deloop M ⟶ Deloop Grp).

(* h conjugates F into G when  G a ≈ h · F a · h⁻¹  for every a.  This is the
   equation Mac Lane's exercise asks about and Awodey's Example 7.21 writes as
   `g(x) = h · f(x) · h⁻¹`, bracketed the way the derivation below produces
   it; the two bracketings agree by associativity. *)
Definition Conjugates (h : carrier Grp) : Type :=
  ∀ a : carrier M,
    Deloop_unmap G a ≈ mon_op (mon_op h (Deloop_unmap F a)) (grp_inv h).

(* And "conjugation by h" is not a new notion here: the right-hand side above
   is Structure/Groupoid.v's [conjugate] — the inner automorphism
   y ↦ h · y · h⁻¹ that Awodey's example names — evaluated in the groupoid
   [Deloop Grp] at the single object, on the nose.  This is an equality of
   TYPES holding by [eq_refl], so it is also an independent check that this
   file's composition order agrees with that of the existing conjugation
   machinery. *)
Example conjugates_is_conjugation (h : carrier Grp) :
  Conjugates h
    = ∀ a : carrier M,
        Deloop_unmap G a
          ≈ conjugate (Deloop_IsGroupoid Grp) (x:=ttt) (x':=ttt)
              h (Deloop_unmap F a)
  := eq_refl.

(* Conjugating and intertwining are the same condition on h once inverses are
   available: multiply the intertwining equation on the right by h⁻¹ to reach
   the conjugation form, and the conjugation form on the right by h to get
   back. *)
Lemma intertwines_conjugates (h : carrier Grp) :
  Intertwines F G h → Conjugates h.
Proof.
  intros I a.
  rewrite <- (I a).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

Lemma conjugates_intertwines (h : carrier Grp) :
  Conjugates h → Intertwines F G h.
Proof.
  intros Cj a.
  rewrite (Cj a).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_l.
  now rewrite mon_op_unit_r.
Qed.

Lemma conjugates_iff_intertwines (h : carrier Grp) :
  Conjugates h ↔ Intertwines F G h.
Proof.
  split.
  - apply conjugates_intertwines.
  - apply intertwines_conjugates.
Defined.

End GroupConjugation.

Arguments Conjugates {M Grp} F G h.

(** ** The set of conjugating elements *)

Section ConjugatorIso.

Context {M : MonObject}.
Context {Grp : GrpObject}.
Context (F G : Deloop M ⟶ Deloop Grp).

(* The literal deliverable: over a GROUP the transformations F ⟹ G correspond
   to the set of CONJUGATING elements — the elements h of Grp satisfying
   [Conjugates F G h], the equation `G a ≈ h · F a · h⁻¹` that names an inner
   automorphism.  [transform_intertwiner_iso] above is the same bijection
   over a bare monoid, where the condition can only be stated as intertwining
   because no inverses exist; here it is stated as conjugation outright.

   No new mathematical content has to be proved — only the same five
   obligations again.  The two conditions on h are interchangeable
   once inverses are available ([intertwines_conjugates] and
   [conjugates_intertwines]), so the two maps are those of
   [transform_intertwiner_iso] with the witness converted on the way through,
   and the two round trips are still [reflexivity] and a case split on the
   object.

   Every disclosure made for the intertwiner setoid above applies here
   verbatim: the equality is that of the underlying elements of Grp, so the
   proof of [Conjugates] is not seen, and the isomorphism is in [Sets] —
   a bijection of setoids, nothing more. *)
Definition Conjugator : Type := ∃ h : carrier Grp, Conjugates F G h.

Program Definition Conjugator_Setoid : Setoid Conjugator := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - now transitivity (`1 y).
Qed.

Definition Deloop_Conjugators : SetoidObject := {|
  carrier   := Conjugator;
  is_setoid := Conjugator_Setoid
|}.

(* A transformation to its component, read as a conjugating element. *)
Program Definition transform_conjugator :
  Deloop_Transforms F G ~{Sets}~> Deloop_Conjugators := {|
  morphism := fun n => existT _ (transform n ttt)
    (intertwines_conjugates F G _ (transform_intertwines F G n))
|}.
Next Obligation.
  intros n1 n2 Hn.
  exact (Hn ttt).
Qed.

(* And back. *)
Program Definition conjugator_transform :
  Deloop_Conjugators ~{Sets}~> Deloop_Transforms F G := {|
  morphism := fun p => intertwines_transform F G (`1 p)
    (conjugates_intertwines F G (`1 p) (`2 p))
|}.
Next Obligation.
  intros p q Hpq x; simpl.
  exact Hpq.
Qed.

(* The bijection the exercise asks for, over a group: the collection of
   transformations F ⟹ G IS the set of conjugating elements.  Taken at
   F = [Deloop_map S] and G = [Deloop_map T] it is the statement that the
   transformations B S ⟹ B T correspond to the elements of Grp conjugating
   S into T — [transform_iff_conjugate] below with the correspondence made
   explicit instead of existentially quantified away. *)
Program Definition transform_conjugator_iso :
  Deloop_Transforms F G ≅[Sets] Deloop_Conjugators := {|
  to   := transform_conjugator;
  from := conjugator_transform
|}.
Next Obligation.
  intro p; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n x; simpl.
  destruct x.
  reflexivity.
Qed.

End ConjugatorIso.

Arguments Conjugator {M Grp} F G.

(* The same bijection read at two homomorphisms, which is the exercise's own
   phrasing: the transformations B S ⟹ B T ARE the elements of C conjugating
   S into T.  This is only [transform_conjugator_iso] instantiated, and it is
   named because that is the exercise's own phrasing. *)
Definition transform_conjugator_hom {B C : GrpObject} (S T : MonHom B C) :
  Deloop_Transforms (Deloop_map S) (Deloop_map T)
    ≅[Sets] Deloop_Conjugators (Deloop_map S) (Deloop_map T) :=
  transform_conjugator_iso (Deloop_map S) (Deloop_map T).

(* Right cancellation in a group, the one piece of group arithmetic used
   below that is not already in Construction/Deloop.v. *)
Lemma grp_cancel_r {Grp : GrpObject} (a b c : carrier Grp) :
  mon_op a c ≈ mon_op b c → a ≈ b.
Proof.
  intro H.
  rewrite <- (mon_op_unit_r a), <- (grp_inv_r c), mon_op_assoc, H.
  rewrite <- mon_op_assoc, grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

(* Conjugation by h⁻¹ runs the other way.  This is the computation Awodey's
   consequence rests on, isolated from the transformation that carries it. *)
Lemma conjugates_inverse {M : MonObject} {Grp : GrpObject}
  (F G : Deloop M ⟶ Deloop Grp) (h : carrier Grp) :
  Conjugates F G h → Conjugates G F (grp_inv h).
Proof.
  intro Cj.
  apply intertwines_conjugates.
  intro a.
  apply (grp_cancel_r _ _ h).
  rewrite <- !mon_op_assoc.
  rewrite grp_inv_l, mon_op_unit_r.
  rewrite (conjugates_intertwines F G h Cj a).
  rewrite mon_op_assoc, grp_inv_l.
  now rewrite mon_op_unit_l.
Qed.

(* Mac Lane, "Categories for the Working Mathematician", §I.4, Exercise 3, in
   both directions: for groups B and C and homomorphisms S, T : B → C, a
   natural transformation between the two functors those homomorphisms give
   between the deloopings is inhabited exactly when some h in C conjugates S
   into T.

   The forward direction extracts the single component; the backward
   direction builds the transformation from h.  Nothing is assumed about B
   beyond its being a monoid — its inverses are never used — but it is stated
   for groups because that is Mac Lane's setting; [transform_iff_intertwines]
   above is the monoid form. *)
Theorem transform_iff_conjugate {B C : GrpObject} (S T : MonHom B C) :
  (Deloop_map S ⟹ Deloop_map T)
    ↔ ∃ h : carrier C,
        ∀ g : carrier B, T g ≈ mon_op (mon_op h (S g)) (grp_inv h).
Proof.
  split.
  - intro n.
    destruct (fst (transform_iff_intertwines (Deloop_map S) (Deloop_map T)) n)
      as [h I].
    exists h.
    exact (intertwines_conjugates (Deloop_map S) (Deloop_map T) h I).
  - intros [h C'].
    apply (snd (transform_iff_intertwines (Deloop_map S) (Deloop_map T))).
    exists h.
    exact (conjugates_intertwines (Deloop_map S) (Deloop_map T) h C').
Defined.

(* The same statement with the two sides exchanged: the SOURCE exhibited as
   the conjugate of the target, rather than the target as the conjugate of
   the source.  This is Awodey's first-edition equation, moved across:
   `f(x) · h = h · g(x)`, printed there as `h⁻¹ · f(x) · h = g(x)`, is
   `f(x) = h · g(x) · h⁻¹` with f the source and g the target — the statement
   below.  See the CITATION NOTE at the top of the file.

   It is a real theorem, proved here rather than described, and its proof is
   the whole content of the remark: at this level — where h is EXISTENTIALLY
   QUANTIFIED — it follows from [transform_iff_conjugate] by sending h to h⁻¹
   and nothing else, [conjugates_inverse] supplying each step.  Since the two
   are biconditionals with the same left-hand side, their right-hand sides
   are thereby equivalent, and the choice of side is not a choice between a
   true statement and a false one here.

   It is at the COMPONENT level that the direction is real content: the
   statements about a given h — [Intertwines], [Conjugates],
   [transform_intertwines], [S3_hom_conjugate], [deloop_ginv_conjugates] —
   each say something different when the sides are exchanged, and it is those
   that the library's composition order pins down. *)
Theorem transform_iff_conjugate_SWAPPED {B C : GrpObject} (S T : MonHom B C) :
  (Deloop_map S ⟹ Deloop_map T)
    ↔ ∃ h : carrier C,
        ∀ g : carrier B, S g ≈ mon_op (mon_op h (T g)) (grp_inv h).
Proof.
  split.
  - intro n.
    destruct (fst (transform_iff_conjugate S T) n) as [h Cj].
    exists (grp_inv h).
    exact (conjugates_inverse (Deloop_map S) (Deloop_map T) h Cj).
  - intros [h Cj].
    apply (snd (transform_iff_conjugate S T)).
    exists (grp_inv h).
    exact (conjugates_inverse (Deloop_map T) (Deloop_map S) h Cj).
Defined.

(** ** Awodey §7.7: the functor category is a groupoid *)

(* The general fact behind Awodey's consequence, which is where its content
   actually lies: if every arrow of D is invertible then so is every natural
   transformation into D, since the componentwise inverses are again natural
   — the naturality square for them is the original square with the two
   components moved across it — and a transformation whose components are
   two-sided inverses is a two-sided inverse.  (Only that direction is proved
   here; the converse, that an invertible transformation has invertible
   components, is not needed and is not stated.)

   Awodey draws the conclusion for two GROUPOIDS: "It is clear that if G and
   H are any groupoids, then the functor category H^G is also a groupoid"
   (2nd ed., p. 168).  What is proved here is stronger in the domain: C is an
   arbitrary category, and only D must be a groupoid.

   The delooping case is the corollary below; the general statement is proved
   here rather than only at deloopings because the argument uses nothing
   about the domain, and because the inverse it produces has the component
   this file needs — [ginv] at each object, which for a delooping IS the
   group inverse ([deloop_ginv_component]). *)
Definition Fun_ginv {C D : Category} (GD : IsGroupoid D) {F K : C ⟶ D}
  (n : F ⟹ K) : K ⟹ F.
Proof.
  refine (@Build_Transform' _ _ K F (fun x => ginv GD (transform n x)) _).
  intros x y f.
  symmetry.
  apply (ginv_move_r GD).
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc, ginv_left.
  now rewrite id_left.
Defined.

Definition Fun_IsGroupoid {C D : Category} (GD : IsGroupoid D) :
  IsGroupoid ([C, D]).
Proof.
  intros F K n.
  refine (@Build_IsIsomorphism ([C, D]) F K n (Fun_ginv GD n) _ _).
  - intro x; simpl.
    rewrite fmap_id.
    apply ginv_right.
  - intro x; simpl.
    rewrite fmap_id.
    apply ginv_left.
Defined.

(* Awodey §7.7: for groups G and H the functor category H^G is a groupoid.
   Only the TARGET need be a group — the domain may be the delooping of any
   monoid, since the inverse of a transformation is built from the inverse of
   its component, which lives in the target. *)
Definition Deloop_Fun_IsGroupoid (M : MonObject) (Grp : GrpObject) :
  IsGroupoid ([Deloop M, Deloop Grp]) :=
  Fun_IsGroupoid (Deloop_IsGroupoid Grp).

(* Awodey's invertibility sentence, named — "Clearly, every such arrow
   ϑ : f → g has an inverse ϑ⁻¹ : g → f (conjugation by h⁻¹)", which stands
   in both editions (2nd ed. p. 167, 1st ed. p. 175): every natural
   transformation between two functors into the delooping of a group is
   invertible.  This is [Deloop_Fun_IsGroupoid] read at one transformation. *)
Definition deloop_transform_invertible {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  @IsIsomorphism ([Deloop M, Deloop Grp]) F G n :=
  Deloop_Fun_IsGroupoid M Grp F G n.

(* And the inverse really is conjugation by h⁻¹, in two steps.  First, its
   component is the group inverse of the component, on the nose: no
   transport, no rewriting, [eq_refl]. *)
Example deloop_ginv_component {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  transform (ginv (Deloop_Fun_IsGroupoid M Grp) n) ttt
    = grp_inv (transform n ttt) := eq_refl.

(* Second, that element conjugates G back into F.  Together with the equation
   above this is Awodey's sentence in full: the transformation is invertible,
   and its inverse is conjugation by h⁻¹. *)
Lemma deloop_ginv_conjugates {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  Conjugates G F (grp_inv (transform n ttt)).
Proof.
  apply conjugates_inverse.
  apply intertwines_conjugates.
  exact (transform_intertwines F G n).
Qed.

(** ** The first trap: the statement is empty over an abelian target *)

(* Conjugation in an abelian group is the identity, so a conjugating element
   between two functors into an abelian target forces them to agree on every
   arrow: the conjugation theorem, over such a target, relates nothing that
   was not already equal.  This is proved, not asserted, because it is the
   precise sense in which an abelian witness would demonstrate nothing. *)
Lemma abelian_conjugates_agree {M : MonObject} {Grp : GrpObject}
  (F G : Deloop M ⟶ Deloop Grp) (h : carrier Grp)
  (comm : ∀ a b : carrier Grp, mon_op a b ≈ mon_op b a)
  (Cj : Conjugates F G h) :
  ∀ a : carrier M, Deloop_unmap G a ≈ Deloop_unmap F a.
Proof.
  intro a.
  rewrite (Cj a).
  rewrite (comm h (Deloop_unmap F a)).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

(* Z/2 and Z/3 — the only groups the tree had until Structure/Groupoid.v
   added S3 — are both abelian, so by the lemma above neither can display a
   conjugation that moves anything. *)
Lemma Bool_Xor_abelian :
  ∀ a b : carrier Bool_Xor_Grp, mon_op a b ≈ mon_op b a.
Proof. intros [|] [|]; reflexivity. Qed.

Lemma Z3_abelian : ∀ a b : carrier Z3_Grp, mon_op a b ≈ mon_op b a.
Proof. intros [| |] [| |]; reflexivity. Qed.

(* Instantiated at Z/2 — the library's first group witness, and the target
   one would reach for first.  Over it a conjugating element forces the two
   functors to agree pointwise, so nothing about conjugacy can be seen
   there.  (Only that direction is proved; the converse, that agreeing
   functors are conjugate, is not needed and is not stated.) *)
Corollary Bool_conjugates_agree {M : MonObject}
  (F G : Deloop M ⟶ Deloop Bool_Xor_Grp) (h : carrier Bool_Xor_Grp)
  (Cj : Conjugates F G h) :
  ∀ a : carrier M, Deloop_unmap G a ≈ Deloop_unmap F a.
Proof. exact (abelian_conjugates_agree F G h Bool_Xor_abelian Cj). Qed.

(** ** A nonabelian witness *)

(* An element of order dividing two names a homomorphism Z/2 → S3, since
   Z/2 is generated by one element of order two.  Three instances are used
   below: the trivial homomorphism and the two picking out the transpositions
   a and c.  (The hypothesis is Coq's `=` because Structure/Groupoid.v builds
   [S3_Mon] over the carrier setoid whose [equiv] field IS [eq], as it does
   for [Z3_Mon] and as Construction/Deloop.v does for [Bool_Xor]; so `≈` and
   `=` are the same relation here and nothing weaker is being assumed.) *)
Program Definition S3_involution_hom (x : S3) (Hx : S3_mul x x = S3_e) :
  MonHom Bool_Xor S3_Mon := {|
  mon_map := fun b => if b then x else S3_e
|}.
Next Obligation.                        (* the unit goes to the unit *)
  intros x Hx.
  reflexivity.
Qed.
Next Obligation.                        (* and the product to the product *)
  intros x Hx a b.
  destruct x, a, b; simpl; try reflexivity; discriminate Hx.
Qed.

Definition S3_hom_e : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_e eq_refl.
Definition S3_hom_a : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_a eq_refl.
Definition S3_hom_c : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_c eq_refl.

(* The conjugating element is NON-CENTRAL, which is the whole point of
   choosing it: this is Structure/Groupoid.v's [S3_not_abelian] read as the
   statement that r does not commute with a.  ([mon_op] at [S3_Mon] is
   [S3_mul] and `≈` is `=`, both definitionally, so that lemma is this
   statement already.) *)
Definition S3_conjugator_noncentral :
  mon_op (m:=S3_Mon) S3_r S3_a ≈ mon_op (m:=S3_Mon) S3_a S3_r → False :=
  S3_not_abelian.

(* The witness the vacuity note requires: the three-cycle r conjugates the
   homomorphism picking out a into the one picking out c.  Both cases are a
   computation in the multiplication table — r · a · r⁻¹ = b · rr = c. *)
Theorem S3_hom_conjugate :
  @Conjugates Bool_Xor S3_Grp (Deloop_map S3_hom_a) (Deloop_map S3_hom_c) S3_r.
Proof. intros [|]; reflexivity. Qed.

(* So a natural transformation between the two homomorphisms exists, built
   through the backward direction of the theorem. *)
Definition S3_conjugating_transform :
  Deloop_map S3_hom_a ⟹ Deloop_map S3_hom_c :=
  snd (@transform_iff_conjugate Bool_Xor_Grp S3_Grp S3_hom_a S3_hom_c)
      (existT _ S3_r S3_hom_conjugate).

(* Its single component is the conjugating element r itself, by [eq_refl] —
   the backward direction of the theorem puts h in as the component and
   nothing intervenes. *)
Example S3_conjugating_transform_component :
  transform S3_conjugating_transform ttt = S3_r := eq_refl.

(* And it is not degenerate: the two homomorphisms it relates are different,
   so the conjugation genuinely moves one to the other. *)
Theorem S3_conjugation_moves :
  (∀ g : carrier Bool_Xor, S3_hom_a g ≈ S3_hom_c g) → False.
Proof.
  intro H.
  specialize (H true).
  discriminate H.
Qed.

(* The two facts together DERIVE that S3 is nonabelian, which is the check
   that the witness exercises exactly the hypothesis it was chosen for: were
   the target abelian, [abelian_conjugates_agree] would force the two
   homomorphisms to agree, and [S3_conjugation_moves] says they do not.  A
   witness over Z/2 or Z/3 could not survive this test: [Bool_Xor_abelian] and
   [Z3_abelian], fed to the same lemma, are the proof that it would not. *)
Corollary S3_conjugation_needs_nonabelian :
  (∀ a b : carrier S3_Grp, mon_op a b ≈ mon_op b a) → False.
Proof.
  intro comm.
  apply S3_conjugation_moves.
  intro g.
  symmetry.
  exact (@abelian_conjugates_agree Bool_Xor S3_Grp
           (Deloop_map S3_hom_a) (Deloop_map S3_hom_c) S3_r comm
           S3_hom_conjugate g).
Qed.

(** ** Awodey's second sentence: a groupoid, but not a group *)

(* Awodey, immediately after the invertibility remark (2nd ed., p. 167):
   "But H^G is still not usually a group, simply because there may be many
   different homomorphisms G → H, so the functor category H^G has more than
   one object."  Here are two such homomorphisms: those Z/2 → S3 picking out
   a and c are different functors, so the object type of the functor category
   is not a singleton.  (They are also the two that
   [S3_conjugating_transform] connects, so this groupoid carries an arrow
   between distinct objects.) *)
Theorem Deloop_S3_two_objects :
  Deloop_map S3_hom_a = Deloop_map S3_hom_c → False.
Proof.
  apply (Deloop_map_distinct S3_hom_a S3_hom_c true).
  discriminate.
Qed.

Definition Deloop_Fun_S3 : Category := [Deloop Bool_Xor_Grp, Deloop S3_Grp].

(* The stronger statement, which object-counting alone does not give: the
   functor category is not a group even up to equivalence.  A group, read as
   a category, is a one-object groupoid, so "essentially a group" means
   "equivalent to a delooping"; and a category equivalent to a delooping is
   connected, since an equivalence is full and a delooping has an arrow
   between any two of its objects (there being one object and at least the
   identity arrow).

   [Full] here is the library's chosen-section form, so no choice principle
   is used: [prefmap] is applied to the unit element of the monoid. *)
Definition deloop_equivalence_connected {C : Category} {N : MonObject}
  (F : C ⟶ Deloop N) (E : EquivalenceOfCategories F) : Connected C.
Proof.
  pose proof (Equivalence_Full E) as Ful.
  intros x y.
  apply hom_zigzag.
  exact (@prefmap _ _ F Ful x y mon_unit).
Defined.

(* The trivial homomorphism and the one picking out a are NOT conjugate: an
   intertwining element would satisfy a · h ≈ h · e, i.e. a · h ≈ h, and no
   element of S3 does — which the proof checks over its six elements.  So the
   functor category has two objects with no arrow between them. *)
Theorem S3_no_transform_trivial :
  (Deloop_map S3_hom_e ⟹ Deloop_map S3_hom_a) → False.
Proof.
  intro n.
  destruct (fst (transform_iff_intertwines
                   (Deloop_map S3_hom_e) (Deloop_map S3_hom_a)) n) as [h I].
  specialize (I true).
  simpl in I.
  destruct h; discriminate I.
Qed.

(* Hence it is not connected — a zig-zag between those two objects would
   collapse, the category being a groupoid, to an arrow between them. *)
Theorem Deloop_Fun_S3_not_connected : Connected Deloop_Fun_S3 → False.
Proof.
  intro K.
  apply S3_no_transform_trivial.
  exact (zigzag_hom (Deloop_Fun_IsGroupoid Bool_Xor_Grp S3_Grp)
           (K (Deloop_map S3_hom_e) (Deloop_map S3_hom_a))).
Qed.

(* And therefore it is not equivalent to the delooping of any monoid — in
   particular of any group — so it is a groupoid that is not a group in a
   stronger sense than object-counting gives.  Both directions of the
   equivalence are covered: the second statement turns an equivalence out of
   a delooping into one into it, by [EquivalenceOfCategories_sym]. *)
Theorem Deloop_Fun_S3_not_deloop (N : MonObject) (F : Deloop_Fun_S3 ⟶ Deloop N)
  (E : EquivalenceOfCategories F) : False.
Proof.
  exact (Deloop_Fun_S3_not_connected (deloop_equivalence_connected F E)).
Qed.

Corollary Deloop_Fun_S3_not_deloop_rev (N : MonObject)
  (F : Deloop N ⟶ Deloop_Fun_S3) (E : EquivalenceOfCategories F) : False.
Proof.
  exact (Deloop_Fun_S3_not_deloop N (@quasi_inverse _ _ F E)
           (@EquivalenceOfCategories_sym _ _ F E)).
Qed.
