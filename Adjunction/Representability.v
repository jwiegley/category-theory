Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Functor.Representable.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(** * Adjoints by pointwise representability

    nLab:      https://ncatlab.org/nlab/show/adjoint+functor
    nLab:      https://ncatlab.org/nlab/show/representable+functor
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, §IV.1 Corollary 2 and Exercise 1,
          printed pp. 85-86 -- maclane:IV.1:cor2, maclane:IV.1:ex1.
    Book: Riehl, "Category Theory in Context", Dover 2016, §4.4 -- the
          same statement, and the source of the uniqueness clause
          discussed below.

    Mac Lane's Corollary 2 reads: a functor G : D ⟶ C has a left adjoint
    precisely when the functor Hom_C(c, G−) : D ⟶ Sets is representable
    for every object c : C -- and a choice of representations IS a choice
    of universal arrows.  Exercise 1 asks the same question in the other
    orientation, where representations of Hom_D(F−, a) for every a : D
    assemble into a RIGHT adjoint of F.  Both orientations are delivered,
    and each as a genuine biconditional
    ([adjunction_iff_pointwise_representable],
    [coadjunction_iff_pointwise_representable]) rather than as a pair of
    unrelated passages.

    THE VARIANCE, BECAUSE THE TWO DONOR FILES USE OPPOSITE LETTERS.
    Theory/Adjunction.v declares [Adjunction] over [F : D ⟶ C] (left) and
    [U : C ⟶ D] (right), so its [unit] is indexed by objects of D.
    Theory/Universal/Arrow.v instead names its functor [U : D ⟶ C] and
    builds a LEFT adjoint [C ⟶ D] out of universal arrows from objects of
    C.  This file follows the second convention throughout: [F : C ⟶ D]
    is the left adjoint, [G : D ⟶ C] the right one, and [unit] at c : C
    has type [c ~> G (F c)] -- which is exactly the type
    [AUniversalArrow c G (F c)] wants for its arrow.  Nothing here
    transports between the two spellings; [F ⊣ G] with those variances is
    already [@Adjunction D C F G] on the nose.

    WHAT MAKES THE CHAIN COMPOSABLE, AND IT IS NEW.  The chain Mac Lane
    runs is "representation at every c" ⟹ "universal arrow at every c" ⟹
    "left adjoint".  Its last step is
    [AdjunctionFromUniversalArrows], which consumes the COMMA-INITIAL
    [UniversalArrow]; but the representability side arrives at the OTHER
    encoding, [AUniversalArrow], since that is what
    Theory/Universal/Element.v's [AUniversalArrow_of_hom] produces.
    Theory/Universal/Arrow.v carried both classes without relating them,
    so the chain could not previously be run end to end.  It is
    [ua_of_aua]/[aua_of_ua] in that file -- landed alongside this work --
    that closes the gap: every passage below from the direct encoding to
    the comma-packaged one goes through [ua_of_aua], and there is no
    other route.  Note the asymmetry this repairs: the COUNIVERSAL side
    already had its packaging passage
    ([ACouniversalArrow_of_CouniversalArrow] and its inverse,
    Theory/Universal/Arrow/Dual.v:557-580, whose own comment records that
    "Theory/Universal/Arrow.v carries both encodings but never relates
    them"), so the dual was composable before the primal was.

    Nothing else here is rebuilt.  [HomAfter] (Theory/Universal/Element.v)
    IS Mac Lane's Hom_C(c, G−) and is used as given; before this file its
    only occurrences in the tree were its own module and one probe file.
    [Representable] (Functor/Representable.v) is used as given too, and
    this is emphatically not its first consumer -- 25 files on master
    Require that module (27 with this file and its probe), and one of the
    inhabitants,
    [Curry_Representable] (Structure/Cartesian/Closed/Adjunction.v:346),
    is itself in an adjunction file.

    RELATION TO Adjunction/Determination.v.  [adj_unit_universal] below
    is the PRIMAL MIRROR of that file's [adj_counit_couniversal]: from an
    arbitrary adjunction, each unit component packaged as a universal
    arrow, where that file packages each counit component as a
    couniversal one.  The two are at the SAME strength -- both arrow
    readbacks are [eq_refl] (see Test/ProbeDetermination347.v:57 for the
    counit side) -- so this is a mirror and not an improvement, and the
    counit-side statement is not duplicated here.

    STRENGTHS, MEASURED STRICT-FIRST.  Four object-and-arrow readbacks
    hold at [eq_refl] and are shipped as [Example]s:

      * [adj_unit_universal_obj]  : the universal object is F c;
      * [adj_unit_universal_arrow]: the universal arrow IS [unit];
      * [adj_representable_obj]   : the representing object is F c;
      * [left_adjoint_of_representable_obj]: the induced left adjoint
        agrees ON OBJECTS with the chosen representing objects, which is
        the check Mac Lane's "a choice of representations is a choice of
        universal arrows" actually asks for.

    So does the object half of the round trip,
    [representable_roundtrip_obj]: reading an adjunction out as
    representations and building the left adjoint back returns F on
    objects, definitionally.

    THE ONE PLACE THE STRICT FORM FAILS, WITH A CAUSE THAT
    DISCRIMINATES.  Recovering the UNIT from a family of universal arrows
    reaches only [≈], and the reason is neither a rebuilt record nor an
    opaque donor: the transpose of the identity is [fmap[G] id ∘ arrow],
    one [fmap_id] and one [id_left] away from [arrow].  That is not an
    inference -- [representable_roundtrip_arrow_residue] and
    [adjunction_of_representable_unit_residue] state the offending term
    literally, and both close by [eq_refl], so the residue is exhibited
    rather than guessed.  The strict forms were attempted and rejected;
    the [≈] statements are [representable_roundtrip_arrow],
    [adjunction_of_representable_unit] and
    [adjunction_of_natural_universal_unit].  Theory/Universal/Arrow/Dual.v
    records the same residue for [counit_couniversal], from the dual side.

    THE DUAL ORIENTATION IS INSTANTIATION, NOT A SECOND DEVELOPMENT.
    [CoHomBefore F a] is [HomAfter (Opposite_Functor F) a], read at
    a : D^op, and its value at d is Hom_{D^op}(a, F d) = Hom_D(F d, a) --
    so [couniversal_of_corepresentable] is [universal_of_representable]
    applied at the opposite categories, with no transport and no tactic,
    and [CouniversalArrow a F] is definitionally the [UniversalArrow] it
    returns.  Everything downstream is then Dual.v's
    [RightAdjointFunctorFromCouniversalArrows] and
    [AdjunctionFromCouniversalArrows].  The object readback
    [right_adjoint_of_corepresentable_obj] is [eq_refl] as well, and so
    is [adj_corepresentable_obj] on the forward leg, which is
    [adj_representable] at [Opposite_Adjunction].  NOTATION HAZARD, and
    it is the reason no [^op] appears on a functor below: [_ ^op] is
    declared in three scopes and Functor/Opposite.v opens [functor_scope],
    so every opposite functor here is written [Opposite_Functor F] by
    name, following Theory/Universal/Arrow/Dual.v.

    UNIQUENESS: WHAT IS DELIVERED IS NOT THE STRONGEST READING, AND THE
    TWO ARE KEPT APART.  Riehl's clause asks that the extension of the
    object assignment c ↦ repr_obj (R c) to a functor be unique.  Three
    things are proved, in decreasing strength of what they fix:

      1. [unit_square_forces_fmap] -- THE UNIT SQUARE HAS AT MOST ONE
         SOLUTION up to [≈].  Read the hypotheses exactly: it takes BOTH
         that [fmap[L] f] satisfies the square at f AND that g does, and
         concludes they agree, so it is SYMMETRIC in the two -- which is
         why the proof is the uniqueness field used twice.  It is NOT the
         stronger "any g satisfying the square is [fmap[L] f]": for an
         arbitrary L and an arbitrary family H nothing ties [fmap[L]] to
         H, and without the first hypothesis the conclusion is false.
         The instance [left_adjoint_of_representable_fmap_unique] is
         sound because it discharges that hypothesis from the proved
         [left_adjoint_of_representable_natural].

      2. [adjunction_of_natural_universal] -- a functor carrying a
         NATURAL family of universal arrows is itself left adjoint to G,
         on the nose rather than up to comparison.  So the object
         assignment is honoured by an actual adjunction, not merely by
         one isomorphic to it.

      3. [natural_universal_left_adjoint_iso] and
         [left_adjoint_of_representable_iso] -- via the in-tree
         [left_adjoint_iso], any left adjoint of G is naturally
         isomorphic to the induced one.  This is the WEAKER statement:
         it says nothing about the object assignment, and it is not
         claimed to be Riehl's clause.

    NOT DELIVERED, and stated plainly.  There is no equation, and no
    isomorphism, between two functor RECORDS pinning the object
    assignment: comparing L with the induced functor when their object
    actions are Leibniz-equal but not definitionally so needs a transport
    in the type of [fmap], and no such transport is performed here.  So
    the strong reading exists only in the two forms (1) and (2) above.
    UNIVERSES, MEASURED RATHER THAN DISCLAIMED.  The Yoneda-free
    constructions are used throughout, as Theory/Universal/Element.v's own
    header directs, and the payoff is visible in the binders: the
    delivered constants are over [C : Category@{u u0 u0}] and
    [D : Category@{u1 u2 u2}], object universes FREE of hom, whereas
    [Yoneda_Lemma@{u u0}] is over [Category@{u0 u0 u0}] with all three
    identified -- so that restriction is genuinely not inherited.  But the
    constraint blocks DO carry one identification, and it is recorded here
    rather than left for a reader to find: [u0 = u2], collapsing C's and
    D's hom-and-proof universes to one, in
    [adjunction_iff_pointwise_representable],
    [left_adjoint_of_representable] and [adj_representable].
    ([ua_of_aua] carries no equation at all.)  Its CAUSE is not
    attributed: no isolating experiment against the candidate donors was
    run, so nothing here says which of them forces it, and it is not
    claimed unavoidable.

    Scope the Yoneda claim precisely: it is about the CONSTANT chain, not
    the module closure.  Every passage consumed here
    ([UniversalElement_of_Representable], [Representable_of_UniversalElement],
    [AUniversalElement_of_hom], [AUniversalArrow_of_hom] and the two
    [AUniversalElement]/[UniversalElement] passages) is a record literal
    over [ue_representation]/[AUniversalElement_of_repr], none of which
    touches [Yoneda_Lemma] -- but Functor/Hom/Yoneda IS in this file's
    transitive closure, pulled in by Theory/Universal/Element.v:8.

    Also absent: no naturality of the family of representations in c (the
    proved [left_adjoint_of_representable_natural] is a different object,
    naturality of the universal ARROWS rather than of the representing
    isomorphisms); no concrete witness instantiating either biconditional
    at a named category; and no uniqueness statement for the
    representations themselves. *)

(** ** From an adjunction to pointwise representability *)

Section Forward.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

#[local] Existing Instance A.

(* Mac Lane §IV.1 Corollary 2, the easy leg: each unit component is a
   universal arrow.  The mediating morphism is the inverse transpose
   [⌈f⌉], its property is [to_adj_unit] followed by
   [from_adj_comp_law], and its uniqueness is [adj_univ] read
   backwards.  Note the ORIENTATION: [AUniversalArrow] concludes
   [fmap[G] g ∘ universal_arrow ≈ f] where [ump_universal_arrows]
   concludes the mirror, so a [symmetry] is spent in the uniqueness
   field. *)
Definition adj_unit_auniversal (c : C) : AUniversalArrow c G (F c).
Proof using A F G.
  unshelve econstructor.
  - exact unit.
  - intros d f.
    unshelve econstructor.
    + exact (from adj[A] f).
    + simpl.
      rewrite <- to_adj_unit.
      apply from_adj_comp_law.
    + simpl; intros v Hv.
      symmetry.
      apply (snd (adj_univ v f)).
      rewrite to_adj_unit.
      exact Hv.
Defined.

(* The comma-initial packaging, through the passage that makes the whole
   chain composable. *)
Definition adj_unit_universal (c : C) : UniversalArrow c G :=
  ua_of_aua (adj_unit_auniversal c).

(* Both readbacks survive the packaging, because
   [universal_arrow_from_UMP] builds the comma object as ((ttt, a); η) and
   the two projections return what they were given. *)
Example adj_unit_universal_obj (c : C) :
  @arrow_obj C D c G (adj_unit_universal c) = F c := eq_refl.

Example adj_unit_universal_arrow (c : C) :
  @arrow C D c G (adj_unit_universal c) = @unit D C F G A c := eq_refl.

(* Mac Lane's Hom_C(c, G−) with its universal element, then its
   representation.  Both steps are Theory/Universal/Element.v's, applied. *)
Definition adj_auniversal_element (c : C)
  : AUniversalElement (HomAfter G c) (F c) :=
  AUniversalElement_of_hom G c (adj_unit_auniversal c).

Definition adj_universal_element (c : C) : UniversalElement (HomAfter G c) :=
  UniversalElement_of_AUniversalElement (adj_auniversal_element c).

Definition adj_representable (c : C) : Representable (HomAfter G c) :=
  Representable_of_UniversalElement (adj_universal_element c).

Example adj_representable_obj (c : C) :
  @repr_obj D (HomAfter G c) (adj_representable c) = F c := eq_refl.

End Forward.

(** ** From pointwise representability to an adjunction *)

Section Converse.

Context {C : Category}.
Context {D : Category}.
Context (G : D ⟶ C).

(* A representation of Hom_C(c, G−) IS a universal arrow from c to G:
   read it as a universal element, then across
   [AUniversalArrow_of_hom].  No tactic is spent -- the whole passage is
   three applications. *)
Definition auniversal_of_representable
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C)
  : AUniversalArrow c G (@repr_obj D (HomAfter G c) (R c)) :=
  AUniversalArrow_of_hom G c
    (AUniversalElement_of_UniversalElement
       (UniversalElement_of_Representable (R c))).

Definition universal_of_representable
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) : UniversalArrow c G :=
  ua_of_aua (auniversal_of_representable R c).

Example universal_of_representable_arrow
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) :
  @arrow C D c G (universal_of_representable R c)
    = @universal_arrow C D c G _ (auniversal_of_representable R c) := eq_refl.

Definition left_adjoint_of_representable
  (R : ∀ c : C, Representable (HomAfter G c)) : C ⟶ D :=
  LeftAdjointFunctorFromUniversalArrows G (universal_of_representable R).

Definition adjunction_of_representable
  (R : ∀ c : C, Representable (HomAfter G c))
  : left_adjoint_of_representable R ⊣ G :=
  AdjunctionFromUniversalArrows G (universal_of_representable R).

(* The check Mac Lane's phrasing calls for: the left adjoint built from a
   family of representations agrees ON OBJECTS with the chosen
   representing objects, definitionally. *)
Example left_adjoint_of_representable_obj
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) :
  fobj[left_adjoint_of_representable R] c
    = @repr_obj D (HomAfter G c) (R c) := eq_refl.

(* The unit does NOT return the chosen universal arrow on the nose, and
   the obstruction is exhibited rather than described: the transpose of
   the identity is literally the arrow with an [fmap[G] id] in front. *)
Example adjunction_of_representable_unit_residue
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) :
  @unit D C (left_adjoint_of_representable R) G
        (adjunction_of_representable R) c
    = fmap[G] (id{D}) ∘ @universal_arrow C D c G _
                          (auniversal_of_representable R c) := eq_refl.

Lemma adjunction_of_representable_unit
  (R : ∀ c : C, Representable (HomAfter G c)) (c : C) :
  @unit D C (left_adjoint_of_representable R) G
        (adjunction_of_representable R) c
    ≈ @universal_arrow C D c G _ (auniversal_of_representable R c).
Proof.
  rewrite adjunction_of_representable_unit_residue, fmap_id.
  apply id_left.
Qed.

End Converse.

(** ** The round trip *)

Section RoundTrip.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

(* Reading an adjunction out as a family of representations and building
   the left adjoint back returns F on objects, definitionally. *)
Example representable_roundtrip_obj (c : C) :
  fobj[left_adjoint_of_representable G (adj_representable A)] c = F c
  := eq_refl.

(* On arrows the same residue appears, for the same reason. *)
Example representable_roundtrip_arrow_residue (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    = fmap[G] (id{D}) ∘ @unit D C F G A c := eq_refl.

Lemma representable_roundtrip_arrow (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    ≈ @unit D C F G A c.
Proof.
  rewrite representable_roundtrip_arrow_residue, fmap_id.
  apply id_left.
Qed.

End RoundTrip.

(** ** Mac Lane §IV.1 Corollary 2 as a biconditional *)

Section Biconditional.

Context {C : Category}.
Context {D : Category}.
Context (G : D ⟶ C).

(* Stated over an arbitrary G, with no adjunction in the ambient
   context -- the point of the sectioning. *)
Theorem adjunction_iff_pointwise_representable :
  (∀ c : C, Representable (HomAfter G c)) ↔ { L : C ⟶ D & L ⊣ G }.
Proof.
  split.
  - intro R.
    exact (left_adjoint_of_representable G R; adjunction_of_representable G R).
  - intros [L AL] c.
    exact (adj_representable AL c).
Defined.

End Biconditional.

(** ** The dual orientation (Mac Lane §IV.1 Exercise 1) *)

Section Dual.

Context {C : Category}.
Context {D : Category}.
Context (F : C ⟶ D).

(* d ↦ Hom_D(F d, a), as a functor C^op ⟶ Sets.  It is [HomAfter] at the
   opposite functor: the value at d is Hom_{D^op}(a, F d), which is
   Hom_D(F d, a). *)
Definition CoHomBefore (a : D) : C^op ⟶ Sets :=
  HomAfter (Opposite_Functor F) a.

(* [CouniversalArrow a F] is by definition the [UniversalArrow] in the
   opposite categories that [universal_of_representable] returns there, so
   this is instantiation and nothing else. *)
Definition couniversal_of_corepresentable
  (R : ∀ a : D, Representable (CoHomBefore a)) (a : D)
  : CouniversalArrow a F :=
  universal_of_representable (Opposite_Functor F) R a.

Definition right_adjoint_of_corepresentable
  (R : ∀ a : D, Representable (CoHomBefore a)) : D ⟶ C :=
  RightAdjointFunctorFromCouniversalArrows F
    (couniversal_of_corepresentable R).

Definition adjunction_of_corepresentable
  (R : ∀ a : D, Representable (CoHomBefore a))
  : F ⊣ right_adjoint_of_corepresentable R :=
  AdjunctionFromCouniversalArrows F (couniversal_of_corepresentable R).

Example right_adjoint_of_corepresentable_obj
  (R : ∀ a : D, Representable (CoHomBefore a)) (a : D) :
  fobj[right_adjoint_of_corepresentable R] a
    = @repr_obj (C^op) (CoHomBefore a) (R a) := eq_refl.

End Dual.

Section DualForward.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

(* The forward leg dualizes by instantiating [adj_representable] at the
   opposite adjunction; [Opposite_Adjunction] carries [F ⊣ G] to
   [Opposite_Functor G ⊣ Opposite_Functor F]. *)
Definition adj_corepresentable (a : D) : Representable (CoHomBefore F a) :=
  adj_representable (Opposite_Adjunction F G A) a.

Example adj_corepresentable_obj (a : D) :
  @repr_obj (C^op) (CoHomBefore F a) (adj_corepresentable a) = G a := eq_refl.

End DualForward.

Section DualBiconditional.

Context {C : Category}.
Context {D : Category}.
Context (F : C ⟶ D).

Theorem coadjunction_iff_pointwise_representable :
  (∀ a : D, Representable (CoHomBefore F a)) ↔ { R : D ⟶ C & F ⊣ R }.
Proof.
  split.
  - intro R.
    exact (right_adjoint_of_corepresentable F R;
           adjunction_of_corepresentable F R).
  - intros [R AR] a.
    exact (adj_corepresentable AR a).
Defined.

End DualBiconditional.

(** ** Uniqueness of the extension *)

Section Uniqueness.

Context {C : Category}.
Context {D : Category}.
Context (G : D ⟶ C).
Context (L : C ⟶ D).
Context (H : ∀ c : C, AUniversalArrow c G (L c)).

(* Naturality of the family in c: the unit square. *)
Definition UnitNatural : Type :=
  ∀ (x y : C) (f : x ~{C}~> y),
    fmap[G] (fmap[L] f) ∘ @universal_arrow C D x G (L x) (H x)
      ≈ @universal_arrow C D y G (L y) (H y) ∘ f.

(* Riehl's uniqueness clause, read pointwise on arrows with the object
   assignment held fixed: an arrow satisfying the unit square at f IS
   [fmap[L] f].  Both sides factor the same morphism through the same
   universal arrow, so the whole proof is the uniqueness field used
   twice. *)
Lemma unit_square_forces_fmap {x y : C} (f : x ~{C}~> y)
      (g : L x ~{D}~> L y)
      (Hf : fmap[G] (fmap[L] f) ∘ @universal_arrow C D x G (L x) (H x)
              ≈ @universal_arrow C D y G (L y) (H y) ∘ f)
      (Hg : fmap[G] g ∘ @universal_arrow C D x G (L x) (H x)
              ≈ @universal_arrow C D y G (L y) (H y) ∘ f) :
  fmap[L] f ≈ g.
Proof.
  pose (W := @universal_arrow_universal C D x G (L x) (H x) (L y)
               (@universal_arrow C D y G (L y) (H y) ∘ f)).
  rewrite <- (uniqueness W _ Hf).
  exact (uniqueness W _ Hg).
Qed.

(* A functor carrying a NATURAL family of universal arrows is itself a
   left adjoint of G -- not merely isomorphic to one -- with that family
   as the unit.  The hom-set isomorphism is the universal factorization;
   naturality in the first variable is where [N] is spent, and naturality
   in the second is [fmap_comp] with an associativity. *)
Definition adjunction_of_natural_universal (N : UnitNatural) : L ⊣ G.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros x y.
    unshelve eapply Isomorphism.Build_Isomorphism.
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun g => fmap[G] g ∘ @universal_arrow C D x G (L x) (H x)).
      * abstract (proper; now rewrite X).
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun f =>
                 unique_obj (@universal_arrow_universal C D x G (L x)
                               (H x) y f)).
      * abstract (proper;
          apply (uniqueness
                   (@universal_arrow_universal C D x G (L x) (H x) y x0));
          rewrite X;
          exact (unique_property
                   (@universal_arrow_universal C D x G (L x) (H x) y y0))).
    + abstract (intro f;
        exact (unique_property
                 (@universal_arrow_universal C D x G (L x) (H x) y f))).
    + abstract (simpl; intro g;
        apply (uniqueness
                 (@universal_arrow_universal C D x G (L x) (H x) y _));
        reflexivity).
  - abstract (intros x y z f g; simpl;
      rewrite fmap_comp, <- comp_assoc, (N x y g), comp_assoc;
      reflexivity).
  - abstract (intros x y z f g; simpl;
      rewrite fmap_comp, <- comp_assoc; reflexivity).
Defined.

(* Only up to [≈], and for the residue reason recorded in the header. *)
Lemma adjunction_of_natural_universal_unit (N : UnitNatural) (c : C) :
  @unit D C L G (adjunction_of_natural_universal N) c
    ≈ @universal_arrow C D c G (L c) (H c).
Proof.
  unfold unit; simpl.
  rewrite fmap_id.
  apply id_left.
Qed.

(* The weaker, object-assignment-free comparison. *)
Corollary natural_universal_left_adjoint_iso (N : UnitNatural)
          (L' : C ⟶ D) (AL' : L' ⊣ G) : L ≈ L'.
Proof.
  exact (left_adjoint_iso G L L' (adjunction_of_natural_universal N) AL').
Qed.

End Uniqueness.

Section UniquenessOfRepresentableExtension.

Context {C : Category}.
Context {D : Category}.
Context (G : D ⟶ C).
Context (R : ∀ c : C, Representable (HomAfter G c)).

(* The induced functor's arrow action is defined BY the factorization, so
   naturality is that factorization's own property read backwards. *)
Lemma left_adjoint_of_representable_natural :
  UnitNatural G (left_adjoint_of_representable G R)
    (auniversal_of_representable G R).
Proof.
  intros x y f; simpl.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (universal_of_representable G R x)
              (@arrow C D y G (universal_of_representable G R y) ∘ f))).
Qed.

Theorem left_adjoint_of_representable_fmap_unique {x y : C}
        (f : x ~{C}~> y)
        (g : @repr_obj D (HomAfter G x) (R x)
               ~{D}~> @repr_obj D (HomAfter G y) (R y))
        (Hg : fmap[G] g
                ∘ @universal_arrow C D x G _ (auniversal_of_representable G R x)
              ≈ @universal_arrow C D y G _ (auniversal_of_representable G R y)
                ∘ f) :
  fmap[left_adjoint_of_representable G R] f ≈ g.
Proof.
  exact (unit_square_forces_fmap G (left_adjoint_of_representable G R)
           (auniversal_of_representable G R) f g
           (left_adjoint_of_representable_natural x y f) Hg).
Qed.

(* The weaker statement again, at the induced functor. *)
Corollary left_adjoint_of_representable_iso (L : C ⟶ D) (AL : L ⊣ G) :
  L ≈ left_adjoint_of_representable G R.
Proof.
  exact (left_adjoint_iso G L (left_adjoint_of_representable G R) AL
           (adjunction_of_representable G R)).
Qed.

End UniquenessOfRepresentableExtension.
