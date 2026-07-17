Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* Subobject classifiers.

   nLab:      https://ncatlab.org/nlab/show/subobject+classifier
   Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

   In a category with a terminal object and pullbacks, a subobject classifier
   is an object Ω together with a point [truth : 1 ~> Ω] such that every
   monomorphism m : u ~> x arises, in exactly one way, as the pullback of
   [truth] along a characteristic morphism [char m : x ~> Ω]:

        u ---!---> 1
        |          |
       m|          | truth
        v          v
        x --char-> Ω

   The data below packages the characteristic morphism as an operation
   [char], respecting the subobject equivalence of Theory/Subobject.v, with
   the square above a pullback ([char_pullback]) and unique among morphisms
   classifying m ([char_unique]).  The classification theorem
   [classifier_classifies] then exhibits the setoid of subobjects of x as
   isomorphic in Sets to the hom-setoid x ~> Ω, the backward map being
   pullback of [truth] via the reindexing of Theory/Subobject/Functor.v. *)

Section SubobjectClassifier.

Context {C : Category}.
Context `{HT : @Terminal C}.
Context `{HP : @HasPullbacks C}.

Class SubobjectClassifier := {
  Ω : C;                                (* the object of truth values *)
  truth : 1 ~> Ω;                       (* the generic subobject *)

  (* the characteristic morphism of a mono m : u ~> x *)
  char {u x : C} (m : u ~> x) (M : Monic m) : x ~> Ω;

  (* the classifying square is a pullback of truth along char m *)
  char_pullback {u x : C} (m : u ~> x) (M : Monic m) :
    IsPullback (char m M) truth u m one;

  (* and char m is the unique morphism with that property *)
  char_unique {u x : C} (m : u ~> x) (M : Monic m) (h : x ~> Ω) :
    IsPullback h truth u m one → h ≈ char m M
}.

Context `{HS : SubobjectClassifier}.

(* truth is monic, trivially: its domain is terminal, so any two morphisms
   z ~> 1 already agree by one_unique, before truth is even applied. *)
Lemma truth_monic : Monic truth.
Proof.
  constructor.
  intros z g1 g2 _.
  apply one_unique.
Qed.

(* The generic subobject: truth as a subobject of Ω. *)
Definition truth_subobject : SubObj Ω := {|
  sub_dom      := 1;
  sub_mono     := truth;
  sub_is_monic := truth_monic
|}.

(* A pullback square is stable under replacing its second projection by an
   ≈-equal morphism; both fields transport by rewriting.  Companion to
   [is_pullback_respects_left] of Theory/Subobject/Functor.v, used below to
   trade the chosen projection into 1 for the canonical [one]. *)
Lemma is_pullback_respects_snd {x y z : C} {f : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 p2' : P ~> y} (Hp : p2 ≈ p2') :
  IsPullback f g P p1 p2 → IsPullback f g P p1 p2'.
Proof.
  intros [Hc Hu].
  constructor.
  - now rewrite <- Hp.
  - intros Q q1 q2 Hq.
    pose proof (Hu Q q1 q2 Hq) as U.
    destruct (unique_property U) as [U1 U2].
    unshelve refine {| unique_obj := unique_obj U |}.
    + split.
      * exact U1.
      * now rewrite <- Hp.
    + intros v [Hv1 Hv2].
      apply (uniqueness U); split.
      * exact Hv1.
      * now rewrite Hp.
Qed.

(* A pullback square transports across an isomorphism of its apex: given a
   pullback with apex P and an isomorphism i : P' ≅ P, precomposing the two
   projections with [to i] yields a pullback with apex P'.  The two extra
   equalities let the caller name the transported projections directly.
   Companion to [is_pullback_respects_snd] above and
   [is_pullback_respects_left] of Theory/Subobject/Functor.v. *)
Lemma is_pullback_precompose_iso {A B Z : C} {f : A ~> Z} {g : B ~> Z}
      {P P' : C} {p1 : P ~> A} {p2 : P ~> B} (i : P' ≅ P)
      {p1' : P' ~> A} {p2' : P' ~> B}
      (H1 : p1 ∘ to i ≈ p1') (H2 : p2 ∘ to i ≈ p2') :
  IsPullback f g P p1 p2 → IsPullback f g P' p1' p2'.
Proof.
  intros Hpb.
  assert (E1 : p1' ∘ from i ≈ p1).
  { rewrite <- H1, <- comp_assoc, iso_to_from; cat. }
  assert (E2 : p2' ∘ from i ≈ p2).
  { rewrite <- H2, <- comp_assoc, iso_to_from; cat. }
  constructor.
  - rewrite <- H1, <- H2, !comp_assoc.
    now rewrite (is_pullback_commutes Hpb).
  - intros Q q1 q2 Hq.
    pose proof (is_pullback_ump Hpb Q q1 q2 Hq) as U.
    destruct (unique_property U) as [U1 U2].
    unshelve refine {| unique_obj := from i ∘ unique_obj U |}.
    + split.
      * now rewrite comp_assoc, E1.
      * now rewrite comp_assoc, E2.
    + intros v [Hv1 Hv2].
      assert (Hvw : unique_obj U ≈ to i ∘ v).
      { apply (uniqueness U); split;
          [ now rewrite comp_assoc, H1
          | now rewrite comp_assoc, H2 ]. }
      rewrite Hvw, comp_assoc, iso_from_to.
      now rewrite id_left.
Qed.

(* [char] respects the subobject equivalence of Theory/Subobject.v.  This
   was formerly a class field; it is derivable from [char_pullback] and
   [char_unique] (transport the classifying square of m' across the domain
   isomorphism, then invoke uniqueness), so it is proved here once rather
   than paid as a redundant obligation by every instance. *)
Lemma char_respects {u u' x : C} (m : u ~> x) (M : Monic m)
      (m' : u' ~> x) (M' : Monic m') :
  {| sub_dom := u; sub_mono := m; sub_is_monic := M |}
    ≈ {| sub_dom := u'; sub_mono := m'; sub_is_monic := M' |}
  → char m M ≈ char m' M'.
Proof.
  intros [i Hi]; simpl in Hi.
  symmetry.
  apply char_unique.
  apply (is_pullback_precompose_iso i Hi (one_unique (one ∘ to i) one)).
  exact (char_pullback m' M').
Qed.

(* Round trip (i): classifying the pullback of truth along h recovers h.
   The chosen pullback square, with its projection into 1 traded for [one],
   is a classifying square for h, so char_unique concludes. *)
Lemma classifier_char_roundtrip {x : C} (h : x ~> Ω) :
  char (sub_mono (sub_reindex h truth_subobject))
       (sub_is_monic (sub_reindex h truth_subobject)) ≈ h.
Proof.
  symmetry.
  apply char_unique.
  apply (is_pullback_respects_snd
           (one_unique (pullback_snd h truth (pullback h truth)) one)).
  exact (pullback_is_pullback h truth (pullback h truth)).
Qed.

(* Round trip (ii): pulling truth back along char m recovers the subobject
   (u, m) up to the SubObj equivalence, since the classifying square is
   itself a pullback of truth along char m; any two pullbacks of one cospan
   agree, via sub_reindex_transport. *)
Lemma classifier_pullback_roundtrip {x : C} (s : SubObj x) :
  sub_reindex (char (sub_mono s) (sub_is_monic s)) truth_subobject ≈ s.
Proof.
  apply (sub_reindex_transport _ truth_subobject s one).
  apply char_pullback.
Qed.

(* The classification theorem: subobjects of x correspond to morphisms
   x ~> Ω, as an isomorphism of setoids.  Forward: char, respecting the
   SubObj equivalence by char_respects.  Backward: pullback of truth along
   h via sub_reindex, respecting ≈ of morphisms by sub_reindex_respects_mor.
   The two round trips are the lemmas above.  Ends in Defined so the
   correspondence computes. *)
Theorem classifier_classifies (x : C) :
  @Isomorphism Sets {| carrier := SubObj x |} {| carrier := x ~> Ω |}.
Proof using Type HP.
  unshelve econstructor.
  - (* to: classify a subobject by its characteristic morphism *)
    simpl.
    unshelve refine {| morphism := fun s : SubObj x =>
                         char (sub_mono s) (sub_is_monic s) |}.
    (* respects the SubObj equivalence *)
    intros s s' Hs.
    destruct s, s'.
    now apply char_respects.
  - (* from: pull truth back along h *)
    simpl.
    unshelve refine {| morphism := fun h : x ~> Ω =>
                         sub_reindex h truth_subobject |}.
    (* the HasPullbacks instance hole left by refine *)
    1: typeclasses eauto.
    (* respects ≈ of characteristic morphisms *)
    intros h h' Hh.
    now apply sub_reindex_respects_mor.
  - (* to ∘ from ≈ id, pointwise *)
    intro h; simpl.
    apply classifier_char_roundtrip.
  - (* from ∘ to ≈ id, pointwise *)
    intro s; simpl.
    apply classifier_pullback_roundtrip.
Defined.

End SubobjectClassifier.
