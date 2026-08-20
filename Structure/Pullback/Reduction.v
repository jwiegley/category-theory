Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Regular.

Generalizable All Variables.

(** * Interdefinability of the finite (co)limit constructions *)

(* nLab:      https://ncatlab.org/nlab/show/finite+limit
              https://ncatlab.org/nlab/show/pullback
              https://ncatlab.org/nlab/show/equalizer
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)
              https://en.wikipedia.org/wiki/Pullback_(category_theory)

   Mac Lane, CWM 2nd ed., §III.3 Exercise 2 p. 71 (`maclane:III.3:ex2`)
   and §III.4 Exercises 7, 9 and 10 pp. 72-73 (`maclane:III.4:ex7`,
   `maclane:III.4:ex9`, `maclane:III.4:ex10`).  Awodey, *Category
   Theory*, 2nd ed., §5.2 Proposition 5.7 and Corollary 5.8
   (`awodey:5.2:prop7`, `awodey:5.2:cor8`), §5.4 Proposition 5.16
   (`awodey:5.4:prop16`), and the chapter exercises 3 and 5
   (`awodey:5:ex3`, `awodey:5:ex5`).  Riehl, *Category Theory in
   Context*, §3.5 Lemmas 3.5.15 and 3.5.16 (`riehl:3.5:lem15`,
   `riehl:3.5:lem16`).

   ------------------------------------------------------------------
   ** What the reductions are, and why anyone cares

   A category has all FINITE limits as soon as it has a small handful of
   them, and there is more than one handful that works.  The two standard
   generating sets are

     (i)  a terminal object, binary products, and equalizers; and
     (ii) a terminal object and pullbacks,

   and the content of the classical results collected here is that each
   generates the other.  The practical payoff is that a construction one
   wants to perform in an arbitrary finitely complete category can be
   carried out with whichever presentation is cheapest to verify in the
   case at hand: pullbacks are what a fibration or a subobject lattice
   hands you directly, while products and equalizers are what an
   algebraic category hands you directly.

   The arguments are old and are usually left as exercises.  Mac Lane
   states three of them that way -- his Exercise 7 builds the pullback of
   f and g as the equalizer of f ∘ exl and g ∘ exr on x × y, his Exercise
   9 recovers an equalizer from a pullback, and his Exercise 10 obtains
   binary products as pullbacks over a terminal object.  Awodey works the
   same ground with proofs: his Proposition 5.7 is Mac Lane's Exercise 7
   with its converse, his Corollary 5.8 is the packaged "products and
   equalizers give pullbacks", and his Proposition 5.16 is the pullbacks
   half.  Riehl's Lemma 3.5.15 is the general statement that limits of
   arbitrary finite shape are generated, of which the binary case is
   proved here.

   Everything below is stated FIRST at the apex-pinned predicate level --
   [IsPullback] of Theory/Morphisms/Stability.v, [IsEqualizer] of
   Structure/Equalizer/Fork.v, [IsCoequalizer] of
   Structure/Coequalizer.v, [IsCartesianProduct] of
   Structure/Cartesian.v -- because those are the forms that can be
   applied to a square one already has.  The bundled classes
   ([HasPullbacks], [HasEqualizers], [Cartesian], [HasPushouts]) are
   packaged afterwards, and nothing here is declared an [Instance]:
   several of these reductions run in opposite directions, so registering
   them for resolution would loop.

   ------------------------------------------------------------------
   ** (D) Mac Lane's Exercise 9 and Awodey's Exercise 3 are NOT the same
      square, and this file proves it rather than asserting it

   It is tempting -- and the issue that prompted this file does it -- to
   describe the two "pullbacks give equalizers" constructions as one
   square read two ways.  They are not.

     - Mac Lane pulls back ⟨id, f⟩ and ⟨id, g⟩, two morphisms out of the
       SAME object x, over x × y.
     - Awodey and Riehl pull back the diagonal ⟨id, id⟩ : y ~> y × y
       along ⟨f, g⟩ : x ~> y × y, two morphisms out of DIFFERENT objects,
       over y × y.

   Three separate measurements say these differ, and all three are
   recorded as probes at the end of the file:

     1. The cospans do not share a codomain.  [x × y = y × y] is well
        typed and refused by [eq_refl] -- a CONVERSION negative.
     2, 3. The legs are not parallel.  [ml_left] inhabits [x ~> x × y]
        while [aw_pair] inhabits [x ~> y × y], so the equation between
        them cannot even be stated -- FORMABILITY negatives, and a
        different kind of failure from 1.

   Those are facts about how the two are written.  The difference is also
   structural, and that is the part worth keeping: BOTH of Mac Lane's
   legs are split monic, with one common retraction ([ml_left_split],
   [ml_right_split], each [exl ∘ - ≈ id]), whereas on Awodey's side only
   the diagonal is ([aw_diag_split]); the other leg retracts along [exl]
   to f itself ([aw_pair_retracts_to_f]), which is not an identity in
   general.  Read that at the strength it has: it exhibits a property one
   cospan has and the other lacks for general f, and it is NOT a proof
   that no isomorphism of cospans exists at particular f and g.  No such
   theorem is proved here and none is claimed.

   What IS true, and is proved, is the weaker and more useful statement:
   the two vertices are canonically isomorphic, because both are
   equalizers of the same parallel pair ([maclane_awodey_iso], through
   [equalizer_unique]), and the comparison commutes with both equalizing
   maps ([maclane_awodey_iso_commutes]) -- so it is an isomorphism of
   equalizers and not merely of objects.

   There is one genuine coincidence, and it is degenerate.  At f := id
   (hence y := x) Mac Lane's cospan and Awodey's consist of the very same
   two morphisms with the two legs interchanged, and that holds
   DEFINITIONALLY: [maclane_awodey_degenerate_left] and
   [maclane_awodey_degenerate_right] are both [eq_refl].  No converse is
   proved -- it is not shown that f = id is the only case.

   ------------------------------------------------------------------
   ** (F) The duality is NOT definitional, and the one step that costs
      something is named

   [Cocartesian C] is notation for [@Cartesian (C^op)] and
   [IsPushout f g] unfolds to a [Pullback] in [C^op], so one might expect
   the pushout half to fall out of the pullback half by instantiation
   alone.  It very nearly does, and the residue was measured rather than
   assumed.

   REFUTED: [HasCoequalizers C = HasEqualizers (C^op)] is refused by
   [eq_refl], and so is the predicate-level
   [IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e] (negatives 6
   and 7, both CONVERSION failures).  [IsCoequalizer] and [IsEqualizer]
   are separately declared records, and Coq's record types are nominal:
   no amount of agreement between their fields makes them one type.

   CONFIRMED: every field type IS convertible.  [cofork]'s
   [e ∘ f ≈ e ∘ g] is accepted where [fork_eq]'s
   [f ∘[C^op] e ≈ g ∘[C^op] e] is expected, on the nose
   ([pos_cofork_is_fork_eq]), and likewise for the descent fields.  So
   both bridges -- [IsEqualizer_op_of_IsCoequalizer] and
   [IsCoequalizer_of_IsEqualizer_op] -- are supplied by [:=] with NO
   tactic and NO obligation, and BOTH round trips close by [eq_refl] on
   the whole record, record eta doing the work
   ([IsCoequalizer_op_round], [IsEqualizer_op_round]).

   So the honest accounting is: the duality is free except for TWO
   repackaging steps, [HasEqualizers_op_of_HasCoequalizers] and its
   mirror [HasCoequalizers_of_HasEqualizers_op], each of which destructs
   the existential and rebuilds it through the corresponding bridge.  (An
   earlier draft of this paragraph said "one", counting only the first
   and overlooking the second, which sits in the same section.)
   Everything on either side of them is instantiation.  In particular the
   coproduct vocabulary needs no translation at all --
   [Coprod_is_op_product], [inl_is_op_exl] and [inr_is_op_exr] are
   [eq_refl] -- so (A) is applied at [C^op] verbatim, and
   Structure/Pushout.v's own [HasPushouts_of_HasPullbacks_op] closes the
   loop.  The covariant reading is delivered too:
   [IsPushout_of_coequalizer] lands in Structure/Pushout.v's own
   [IsPushout], and its apex and both injections COMPUTE, by [eq_refl].

   ------------------------------------------------------------------
   ** Strength measurements

   Measured strict-first throughout; [eq_refl] was attempted before any
   [≈] was accepted.

   Closing by [eq_refl]:
     - [kernel_pair_is_pullback_along_itself]: Structure/Regular.v's
       [kernel_pair f] IS [pullback f f], so section (C) is about that
       constant and not a parallel notion of its own;
     - the two degenerate Mac Lane/Awodey coincidences at f := id;
     - both [IsCoequalizer]/[IsEqualizer (C^op)] record round trips;
     - the three coproduct-is-op-product readings;
     - the apex and both injections of [IsPushout_of_coequalizer].

   Holding only up to [≈], with the strict form REFUTED and probed:
     - [equalizer_pullback_round]: pairing the two projections that (A)
       extracts recovers the original equalizing map, but by
       [fork_exl_exr], which is a [≈]-law and not a conversion
       (negative 4);
     - [pullback_equalizer_round_fst]/[_snd]: projecting out of the
       pairing that (B) forms recovers the original projections, by
       [exl_fork]/[exr_fork] -- again [≈] only (negative 5).

   A note on (B), since it departs from the textbook: Awodey derives the
   uniqueness half of Proposition 5.7's converse from the fact that an
   equalizer is monic.  Structure/Equalizer/Fork.v:83 has that lemma
   ([equalizer_monic]) and it was read, but it is NOT used here.  Any
   competing factorization through the pairing ⟨p1, p2⟩ projects to a
   competing factorization through p1 and p2 separately, so the PULLBACK's
   own uniqueness clause discharges the goal directly, and routing through
   monicity would be a longer path to the same place.

   ------------------------------------------------------------------
   ** What this file does NOT do

   Scoped to this file; none of these is a claim about the tree.

     - It does not treat WIDE pullbacks or wide equalizers, in any
       direction; those live elsewhere.
     - It does not conclude [Complete] or [Cocomplete], and does not
       state Riehl's Lemma 3.5.15 for limits of arbitrary finite shape.
       Only the binary/parallel-pair generators are related; assembling
       them into a completeness statement would need the finite-shape
       induction, which is not performed.
     - It does not derive a [Terminal] object from anything, so (E)'s
       hypotheses are not shown minimal, and no converse to (E) is given.
     - It does not compare the [Cartesian] structure that (E) produces
       with any pre-existing [Cartesian] structure on the same category;
       in particular no coherence or canonicity is claimed for it, and
       the two need not be the same instance.
     - It packages none of the [≈]-round-trips as an isomorphism of
       structures.
     - It declares no [Instance] and registers nothing for typeclass
       resolution.
     - It makes no universe claim of any kind. *)

(* ====================================================================== *)
(** * (A) Cartesian + equalizers give pullbacks                           *)

Section PullbackFromEqualizer.

Context {C : Category}.
Context `{@Cartesian C}.

(* maclane:III.4:ex7, forward; awodey:5.2:prop7, forward.  The two legs
   of the cospan are shifted onto the product and their equalizer taken:
   an element of x × y equalizing f ∘ exl and g ∘ exr is exactly a pair
   whose two components agree over z.  The projections of the resulting
   pullback square are the two components of the equalizing map. *)
Lemma pullback_of_equalizer {x y z : C} (f : x ~> z) (g : y ~> z)
      {E : C} {e : E ~> x × y}
      (Eq : IsEqualizer (f ∘ exl) (g ∘ exr) E e) :
  IsPullback f g E (exl ∘ e) (exr ∘ e).
Proof.
  constructor.
  - rewrite !comp_assoc.
    exact (fork_eq Eq).
  - intros Q q1 q2 Hq.
    assert (Hh : (f ∘ exl) ∘ (q1 △ q2) ≈ (g ∘ exr) ∘ (q1 △ q2)).
    { rewrite <- !comp_assoc, exl_fork, exr_fork.
      exact Hq. }
    destruct (eq_desc Eq (q1 △ q2) Hh) as [u Hu Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + split.
      * rewrite <- comp_assoc, Hu.
        apply exl_fork.
      * rewrite <- comp_assoc, Hu.
        apply exr_fork.
    + intros v [Hv1 Hv2].
      apply Huniq.
      apply ump_products; split.
      * rewrite comp_assoc.
        exact Hv1.
      * rewrite comp_assoc.
        exact Hv2.
Qed.

End PullbackFromEqualizer.

Definition HasPullbacks_of_Cartesian_HasEqualizers {C : Category}
           `{@Cartesian C} (E : @HasEqualizers C) : @HasPullbacks C.
Proof.
  constructor.
  intros x y z f g.
  destruct (@equalizer C E (x × y)%object z (f ∘ exl) (g ∘ exr))
    as [q [e Eq]].
  exact (is_pullback_pullback (pullback_of_equalizer f g Eq)).
Defined.

(* ====================================================================== *)
(** * (B) The converse: a pullback square is an equalizer                 *)

Section EqualizerFromPullback.

Context {C : Category}.
Context `{@Cartesian C}.

Lemma equalizer_of_pullback {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y}
      (HP : IsPullback f g P p1 p2) :
  IsEqualizer (f ∘ exl) (g ∘ exr) P (p1 △ p2).
Proof.
  constructor.
  - rewrite <- !comp_assoc, exl_fork, exr_fork.
    exact (is_pullback_commutes HP).
  - intros Q h Hh.
    assert (Hq : f ∘ (exl ∘ h) ≈ g ∘ (exr ∘ h)).
    { rewrite !comp_assoc.
      exact Hh. }
    destruct (is_pullback_ump HP Q (exl ∘ h) (exr ∘ h) Hq)
      as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + rewrite <- fork_comp.
      symmetry.
      apply ump_products; split.
      * symmetry; exact Hu1.
      * symmetry; exact Hu2.
    + intros v Hv.
      apply Huniq; split.
      * rewrite <- Hv.
        now rewrite exl_fork_comp.
      * rewrite <- Hv.
        now rewrite exr_fork_comp.
Qed.

(** ** The two passages round-trip, up to [≈] but not on the nose *)

(* Starting from an equalizer [e : E ~> x × y] of the shifted pair, (A)
   produces the projections exl ∘ e and exr ∘ e, and (B) pairs them back
   up.  The result is [e] again -- but only up to [≈]: [fork_exl_exr] is a
   [≈]-law, not a conversion, so the strict form is refuted (see the
   probes at the end of the file). *)
Lemma equalizer_pullback_round {x y : C} (E : C) (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e.
Proof.
  now rewrite fork_comp, fork_exl_exr, id_left.
Qed.

(* The other composite, on each projection separately; this is exactly
   [exl_fork]/[exr_fork], i.e. again a [≈]-law and not a conversion. *)
Lemma pullback_equalizer_round_fst {x y : C} {P : C}
      (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) ≈ p1.
Proof. apply exl_fork. Qed.

Lemma pullback_equalizer_round_snd {x y : C} {P : C}
      (p1 : P ~> x) (p2 : P ~> y) : exr ∘ (p1 △ p2) ≈ p2.
Proof. apply exr_fork. Qed.

End EqualizerFromPullback.

(* ====================================================================== *)
(** * (C) The kernel pair as an equalizer                                 *)

Section KernelPair.

Context {C : Category}.
Context `{@Cartesian C}.

(* maclane:III.4:ex7, second clause.  The kernel pair of f is the
   pullback of f along ITSELF, so this is (B) read at g := f and carries
   no new proof content -- the whole statement is [equalizer_of_pullback]
   instantiated, and it is written that way rather than reproved. *)
Lemma kernel_pair_of_IsPullback {x y : C} {f : x ~> y}
      {P : C} {p1 p2 : P ~> x} (HP : IsPullback f f P p1 p2) :
  IsEqualizer (f ∘ exl) (f ∘ exr) P (p1 △ p2).
Proof. exact (equalizer_of_pullback HP). Qed.

(* The tie to the tree's existing notion.  Structure/Regular.v:46 already
   defines [kernel_pair f := pullback f f] under [HasPullbacks], and the
   statements below are about THAT constant -- no parallel notion of a
   kernel pair is introduced here.  The identification is definitional
   ([kernel_pair_is_pullback_along_itself], by [eq_refl]). *)
Context `{HPB : @HasPullbacks C}.

Definition kernel_pair_fst {x y : C} (f : x ~> y) :
  Pull f f (kernel_pair f) ~> x := pullback_fst f f (kernel_pair f).

Definition kernel_pair_snd {x y : C} (f : x ~> y) :
  Pull f f (kernel_pair f) ~> x := pullback_snd f f (kernel_pair f).

Lemma kernel_pair_IsEqualizer {x y : C} (f : x ~> y) :
  IsEqualizer (f ∘ exl) (f ∘ exr) (Pull f f (kernel_pair f))
              (kernel_pair_fst f △ kernel_pair_snd f).
Proof.
  exact (kernel_pair_of_IsPullback
           (pullback_is_pullback f f (kernel_pair f))).
Qed.

Example kernel_pair_is_pullback_along_itself {x y : C} (f : x ~> y) :
  kernel_pair f = pullback f f := eq_refl.

End KernelPair.

(* ====================================================================== *)
(** * (D) Pullbacks give equalizers: two genuinely different squares      *)

Section EqualizerFromPullbackSquares.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(** ** Mac Lane's square (maclane:III.4:ex9) *)

Definition ml_left  : x ~> x × y := id △ f.
Definition ml_right : x ~> x × y := id △ g.

Lemma ml_projections_agree {E : C} {p1 p2 : E ~> x}
      (HP : IsPullback ml_left ml_right E p1 p2) : p1 ≈ p2.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  assert (Hl : exl ∘ (ml_left ∘ p1) ≈ exl ∘ (ml_right ∘ p2))
    by now rewrite Hc.
  unfold ml_left, ml_right in Hl.
  rewrite !comp_assoc, !exl_fork, !id_left in Hl.
  exact Hl.
Qed.

Lemma equalizer_of_pullback_maclane {E : C} {p1 p2 : E ~> x}
      (HP : IsPullback ml_left ml_right E p1 p2) :
  IsEqualizer f g E p1.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  pose proof (ml_projections_agree HP) as Hp.
  assert (Hr : f ∘ p1 ≈ g ∘ p2).
  { assert (Hr' : exr ∘ (ml_left ∘ p1) ≈ exr ∘ (ml_right ∘ p2))
      by now rewrite Hc.
    unfold ml_left, ml_right in Hr'.
    rewrite !comp_assoc, !exr_fork in Hr'.
    exact Hr'. }
  constructor.
  - rewrite Hr.
    now rewrite Hp.
  - intros Q h Hh.
    assert (Hcomm : ml_left ∘ h ≈ ml_right ∘ h).
    { unfold ml_left, ml_right.
      rewrite <- !fork_comp, !id_left.
      now rewrite Hh. }
    destruct (is_pullback_ump HP Q h h Hcomm) as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + exact Hu1.
    + intros v Hv.
      apply Huniq; split.
      * exact Hv.
      * now rewrite <- Hp.
Qed.

(** ** Awodey's and Riehl's square (awodey:5:ex3, riehl:3.5:lem16) *)

Definition aw_diag : y ~> y × y := id △ id.
Definition aw_pair : x ~> y × y := f △ g.

Lemma equalizer_of_pullback_awodey {E : C} {p1 : E ~> x} {p2 : E ~> y}
      (HP : IsPullback aw_pair aw_diag E p1 p2) :
  IsEqualizer f g E p1.
Proof.
  pose proof (is_pullback_commutes HP) as Hc.
  assert (Hl : f ∘ p1 ≈ p2).
  { assert (H' : exl ∘ (aw_pair ∘ p1) ≈ exl ∘ (aw_diag ∘ p2))
      by now rewrite Hc.
    unfold aw_pair, aw_diag in H'.
    rewrite !comp_assoc, !exl_fork, id_left in H'.
    exact H'. }
  assert (Hr : g ∘ p1 ≈ p2).
  { assert (H' : exr ∘ (aw_pair ∘ p1) ≈ exr ∘ (aw_diag ∘ p2))
      by now rewrite Hc.
    unfold aw_pair, aw_diag in H'.
    rewrite !comp_assoc, !exr_fork, id_left in H'.
    exact H'. }
  constructor.
  - now rewrite Hl, Hr.
  - intros Q h Hh.
    assert (Hcomm : aw_pair ∘ h ≈ aw_diag ∘ (f ∘ h)).
    { unfold aw_pair, aw_diag.
      rewrite <- !fork_comp, !id_left.
      now rewrite Hh. }
    destruct (is_pullback_ump HP Q h (f ∘ h) Hcomm) as [u [Hu1 Hu2] Huniq].
    unshelve eapply Build_Unique.
    + exact u.
    + exact Hu1.
    + intros v Hv.
      apply Huniq; split.
      * exact Hv.
      * rewrite <- Hl, <- comp_assoc.
        now rewrite Hv.
Qed.

(** ** Comparing the two squares

    The two cospans are not the same square.  They do not share a
    codomain (x × y against y × y), and their legs are not even parallel:
    Mac Lane's two legs both issue from x, Awodey's from x and from y.
    Those are refuted at the end of the file, the leg comparisons being
    FORMABILITY negatives (ill-typed when x and y differ) rather than
    conversion negatives.

    The difference is not merely syntactic, and the FOUR lemmas below
    bear on it: BOTH of Mac Lane's legs are split monic, with the single
    common retraction exl, whereas [exl ∘ aw_pair] is f, which is not an
    identity FOR GENERAL f.  Read that hedge strictly.  It does NOT say
    Awodey's leg is never split -- at f := id it is, by [ml_right_split]
    -- and an earlier draft of this comment concluded "so no relabelling
    of objects can turn one cospan into the other", which is REFUTED by
    this file's own [maclane_awodey_degenerate_left]/[_right], where at
    f := id the two cospans are the same two morphisms.  No non-existence
    of a cospan isomorphism is proved anywhere here.  What is true is
    that the two vertices are canonically
    isomorphic, both being equalizers of the same parallel pair, and that
    the comparison commutes with the two equalizing maps. *)

Lemma ml_left_split : exl ∘ ml_left ≈ id.
Proof. unfold ml_left. apply exl_fork. Qed.

Lemma ml_right_split : exl ∘ ml_right ≈ id.
Proof. unfold ml_right. apply exl_fork. Qed.

Lemma aw_diag_split : exl ∘ aw_diag ≈ id.
Proof. unfold aw_diag. apply exl_fork. Qed.

(* Awodey's other leg retracts to f.  NOTE THE NAME: an earlier draft
   called this [aw_pair_not_split], which asserted more than it proves and
   more than is true -- at f := id this very statement makes [aw_pair]
   split, discharged by [ml_right_split] above.  All that is proved is the
   retraction identity. *)
Lemma aw_pair_retracts_to_f : exl ∘ aw_pair ≈ f.
Proof. unfold aw_pair. apply exl_fork. Qed.

Lemma maclane_awodey_iso {E F : C} {p1 p2 : E ~> x} {r1 : F ~> x} {r2 : F ~> y}
      (HE : IsPullback ml_left ml_right E p1 p2)
      (HF : IsPullback aw_pair aw_diag F r1 r2) : E ≅ F.
Proof.
  exact (equalizer_unique f g (equalizer_of_pullback_maclane HE)
                              (equalizer_of_pullback_awodey HF)).
Defined.

Lemma maclane_awodey_iso_commutes {E F : C} {p1 p2 : E ~> x}
      {r1 : F ~> x} {r2 : F ~> y}
      (HE : IsPullback ml_left ml_right E p1 p2)
      (HF : IsPullback aw_pair aw_diag F r1 r2) :
  r1 ∘ to (maclane_awodey_iso HE HF) ≈ p1
    ∧ p1 ∘ from (maclane_awodey_iso HE HF) ≈ r1.
Proof.
  split; simpl.
  - exact (unique_property
             (eq_desc (equalizer_of_pullback_awodey HF) p1
                (fork_eq (equalizer_of_pullback_maclane HE)))).
  - exact (unique_property
             (eq_desc (equalizer_of_pullback_maclane HE) r1
                (fork_eq (equalizer_of_pullback_awodey HF)))).
Qed.

End EqualizerFromPullbackSquares.

(** The two cospans coincide, up to swapping the two legs, exactly in the
    degenerate case f = id.  Both sides are checked at Leibniz equality. *)

Example maclane_awodey_degenerate_left {C : Category} `{@Cartesian C}
        {x : C} : @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

Example maclane_awodey_degenerate_right {C : Category} `{@Cartesian C}
        {x : C} (g : x ~> x) :
  @ml_right C _ x x g = @aw_pair C _ x x id g := eq_refl.

(* ====================================================================== *)
(** * (E) Pullbacks and a terminal object give products and equalizers    *)

Section ProductFromPullback.

Context {C : Category}.
Context `{T : @Terminal C}.
Context {x y : C}.
Context {P : C} {p1 : P ~> x} {p2 : P ~> y}.
Context (HP : IsPullback (one : x ~> 1) (one : y ~> 1) P p1 p2).

(* maclane:III.4:ex10; awodey:5.4:prop16; riehl:3.5:lem15, binary case.
   Pulling back over the terminal object imposes no condition -- the
   square commutes automatically, by [one_unique] -- so the pullback of
   x --!--> 1 <--!-- y is the product, and its universal property is the
   product's with the commutation hypothesis discharged rather than
   assumed.  The conclusion is stated at [IsCartesianProduct], the
   apex-pinned form, before any class is packaged. *)
Definition pb_fork {a : C} (u : a ~> x) (v : a ~> y) : a ~> P :=
  unique_obj (is_pullback_ump HP a u v (one_unique _ _)).

Lemma pb_fork_fst {a : C} (u : a ~> x) (v : a ~> y) :
  p1 ∘ pb_fork u v ≈ u.
Proof.
  unfold pb_fork.
  now destruct (unique_property (is_pullback_ump HP a u v (one_unique _ _))).
Qed.

Lemma pb_fork_snd {a : C} (u : a ~> x) (v : a ~> y) :
  p2 ∘ pb_fork u v ≈ v.
Proof.
  unfold pb_fork.
  now destruct (unique_property (is_pullback_ump HP a u v (one_unique _ _))).
Qed.

Lemma pb_fork_unique {a : C} (u : a ~> x) (v : a ~> y) (h : a ~> P) :
  p1 ∘ h ≈ u → p2 ∘ h ≈ v → pb_fork u v ≈ h.
Proof.
  intros H1 H2.
  exact (uniqueness (is_pullback_ump HP a u v (one_unique _ _)) h
           (H1, H2)).
Qed.

Definition product_of_pullback : @IsCartesianProduct C x y P.
Proof using All.
  unshelve econstructor.
  - exact (@pb_fork).
  - exact p1.
  - exact p2.
  - intros a u u' Hu v v' Hv.
    apply pb_fork_unique.
    + now rewrite pb_fork_fst.
    + now rewrite pb_fork_snd.
  - intros a u v h; split.
    + intros Hh; split.
      * rewrite Hh.
        apply pb_fork_fst.
      * rewrite Hh.
        apply pb_fork_snd.
    + intros [H1 H2].
      symmetry.
      now apply pb_fork_unique.
Defined.

End ProductFromPullback.

Section CartesianFromPullbacks.

Context {C : Category}.
Context `{T : @Terminal C}.
Context (HPB : @HasPullbacks C).

(* The chosen pullback of the terminal cospan a --!--> 1 <--!-- b. *)
Definition pb_chosen (a b : C) : Pullback (one : a ~> 1) (one : b ~> 1) :=
  @pullback C HPB a b 1%object one one.

Definition pb_prod (a b : C) : C := Pull _ _ (pb_chosen a b).

Definition pb_prod_IsCartesianProduct (a b : C) :
  @IsCartesianProduct C a b (pb_prod a b) :=
  product_of_pullback (pullback_is_pullback one one (pb_chosen a b)).

Definition Cartesian_of_HasPullbacks_Terminal : @Cartesian C := {|
  product_obj := pb_prod ;
  fork := fun a b c u v =>
            @fork' C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a u v ;
  exl := fun a b => @exl' C a b (pb_prod a b)
                      (pb_prod_IsCartesianProduct a b) ;
  exr := fun a b => @exr' C a b (pb_prod a b)
                      (pb_prod_IsCartesianProduct a b) ;
  fork_respects := fun a b c =>
    @fork'_respects C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a ;
  ump_products := fun a b c =>
    @ump_product C b c (pb_prod b c) (pb_prod_IsCartesianProduct b c) a
|}.

(* Combining (E) with (D): the Awodey square is now available, so a
   category with pullbacks and a terminal object has all equalizers. *)
Definition HasEqualizers_of_HasPullbacks_Terminal : @HasEqualizers C.
Proof using All.
  pose (CC := Cartesian_of_HasPullbacks_Terminal).
  constructor.
  intros a b f g.
  exists (Pull _ _ (@pullback C HPB a b (@product_obj C CC b b)
                      (@aw_pair C CC a b f g) (@aw_diag C CC b))).
  exists (pullback_fst _ _ _).
  exact (@equalizer_of_pullback_awodey C CC a b f g _ _ _
           (pullback_is_pullback _ _ _)).
Defined.

End CartesianFromPullbacks.

(* ====================================================================== *)
(** * (F) The dual: cocartesian + coequalizers give pushouts              *)

Section Duality.

Context {C : Category}.

Definition IsEqualizer_op_of_IsCoequalizer {x y : C} {f g : x ~> y}
           {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  @IsEqualizer (C^op) y x f g q e :=
  @Build_IsEqualizer (C^op) y x f g q e (cofork E)
    (fun z h Hh => coeq_desc E h Hh).

Definition IsCoequalizer_of_IsEqualizer_op {x y : C} {f g : x ~> y}
           {q : C} {e : y ~> q} (E : @IsEqualizer (C^op) y x f g q e) :
  IsCoequalizer f g q e :=
  @Build_IsCoequalizer C x y f g q e (fork_eq E)
    (fun z h Hh => eq_desc E h Hh).

Example IsCoequalizer_op_round {x y : C} {f g : x ~> y}
        {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  IsCoequalizer_of_IsEqualizer_op (IsEqualizer_op_of_IsCoequalizer E) = E
  := eq_refl.

Example IsEqualizer_op_round {x y : C} {f g : x ~> y}
        {q : C} {e : y ~> q} (E : @IsEqualizer (C^op) y x f g q e) :
  IsEqualizer_op_of_IsCoequalizer (IsCoequalizer_of_IsEqualizer_op E) = E
  := eq_refl.

Definition HasEqualizers_op_of_HasCoequalizers
           (E : @HasCoequalizers C) : @HasEqualizers (C^op).
Proof.
  constructor.
  intros x y f g.
  destruct (@coeq C E y x f g) as [q [e Eq]].
  exists q, e.
  exact (IsEqualizer_op_of_IsCoequalizer Eq).
Defined.

Definition HasCoequalizers_of_HasEqualizers_op
           (E : @HasEqualizers (C^op)) : @HasCoequalizers C.
Proof.
  constructor.
  intros x y f g.
  destruct (@equalizer (C^op) E y x f g) as [q [e Eq]].
  exists q, e.
  exact (IsCoequalizer_of_IsEqualizer_op Eq).
Defined.

End Duality.

Section PushoutFromCoequalizer.

Context {C : Category}.
Context `{O : @Cocartesian C}.

(* The coproduct vocabulary of Structure/Cocartesian.v is the product
   vocabulary of C^op ON THE NOSE, which is what lets (A) be instantiated
   below with no translation step at all. *)
Example Coprod_is_op_product (a b : C) :
  @Coprod C O a b = @product_obj (C^op) O a b := eq_refl.

Example inl_is_op_exl {a b : C} :
  (@inl C O a b) = @exl (C^op) O a b := eq_refl.

Example inr_is_op_exr {a b : C} :
  (@inr C O a b) = @exr (C^op) O a b := eq_refl.

Lemma pushout_of_coequalizer {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  @IsPullback (C^op) y z x f g E (e ∘ inl) (e ∘ inr).
Proof.
  exact (@pullback_of_equalizer (C^op) O y z x f g E e
           (IsEqualizer_op_of_IsCoequalizer Eq)).
Qed.

(* Read through the covariant accessors of Structure/Pushout.v.  The apex
   and both injections compute: no transport, no [≈]-step. *)
Definition IsPushout_of_coequalizer {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) : IsPushout f g :=
  is_pullback_pullback (pushout_of_coequalizer f g Eq).

Example IsPushout_of_coequalizer_apex {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_apex (IsPushout_of_coequalizer f g Eq) = E := eq_refl.

Example IsPushout_of_coequalizer_in1 {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_in1 (IsPushout_of_coequalizer f g Eq) = e ∘ inl := eq_refl.

Example IsPushout_of_coequalizer_in2 {x y z : C} (f : x ~> y) (g : x ~> z)
      {E : C} {e : y + z ~> E}
      (Eq : IsCoequalizer (inl ∘ f) (inr ∘ g) E e) :
  pushout_in2 (IsPushout_of_coequalizer f g Eq) = e ∘ inr := eq_refl.

End PushoutFromCoequalizer.

Definition HasPushouts_of_Cocartesian_HasCoequalizers {C : Category}
           `{O : @Cocartesian C} (E : @HasCoequalizers C) : @HasPushouts C :=
  HasPushouts_of_HasPullbacks_op
    (@HasPullbacks_of_Cartesian_HasEqualizers (C^op) O
       (HasEqualizers_op_of_HasCoequalizers E)).

(* ====================================================================== *)
(** * Measured negatives

    Every strengthening attempted and refused, recorded as a [Fail] so a
    later change to a donor breaks this file loudly rather than silently
    invalidating a prose claim.  The two KINDS are kept apart, and the
    split is measured rather than guessed: negatives 2 and 3 are
    FORMABILITY failures -- the two legs do not live in a common hom-set,
    so the equation cannot be stated -- while negatives 1, 4, 5, 6 and 7
    are CONVERSION failures, where both sides are well typed and [eq_refl]
    is refused.  Positive controls sit beside them.

    These are measurements made in this file, not a substitute for a
    guarded probe file with an instrument check. *)

Section Negatives.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(* 1. The two cospans of section (D) do not share a codomain. *)
Fail Example neg_ml_aw_codomain :
  (x × y)%object = (y × y)%object := eq_refl.

(* positive control: the degenerate instantiation y := x does. *)
Example pos_ml_aw_codomain_degenerate :
  (x × x)%object = (x × x)%object := eq_refl.

(* 2, 3. Nor are the legs parallel: these are ill-typed, not merely
   inconvertible. *)
Fail Example neg_ml_left_is_aw_pair :
  @ml_left C _ x y f = @aw_pair C _ x y f g := eq_refl.

Fail Example neg_ml_right_is_aw_diag :
  @ml_right C _ x y g = @aw_diag C _ y := eq_refl.

(* positive control: at f := id the legs DO coincide, up to swapping the
   two sides of the cospan -- this is [maclane_awodey_degenerate_*]. *)
Example pos_ml_aw_degenerate :
  @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

(* 4. The (A)/(B) round trip on the equalizing map is [≈], not [=]. *)
Fail Example neg_equalizer_pullback_round {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) = e := eq_refl.

(* 5. Nor is the reverse composite strict on the projections. *)
Fail Example neg_pullback_equalizer_round {P : C}
     (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) = p1 := eq_refl.

(* positive control for 4 and 5: both hold at [≈]. *)
Example pos_rounds_up_to_equiv {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e := equalizer_pullback_round E e.

End Negatives.

Section NegativesDuality.

Context {C : Category}.

(* 6, 7. The duality of section (F) is NOT definitional: [IsCoequalizer]
   and [IsEqualizer] are distinct record types, so neither the predicates
   nor the classes are related by [eq_refl], however convertible their
   fields are. *)
Fail Example neg_HasCoequalizers_is_op :
  HasCoequalizers C = HasEqualizers (C^op) := eq_refl.

Fail Example neg_IsCoequalizer_is_op {x y : C} (f g : x ~> y)
     (q : C) (e : y ~> q) :
  IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e := eq_refl.

(* positive control: the FIELD types are convertible, which is exactly
   why the bridge below needs no tactic. *)
Example pos_cofork_is_fork_eq {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (Hyp : e ∘ f ≈ e ∘ g) :
  f ∘[C^op] e ≈ g ∘[C^op] e := Hyp.

End NegativesDuality.
