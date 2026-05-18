Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Span.Category.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(** * Cospan bridging: C-vs-C^op direction inverters

    The cospan category is implemented as the span category in [C^op]:
    the apex of a cospan lives in [C], but the morphisms between apexes
    (when stating [cospan_equiv]) live in [C^op].  This file provides a
    thin bridging layer so that downstream coherence proofs can phrase
    each obligation purely as a C-level equation and let the bridging
    lemmas handle the direction-flip.

    The key tactic pattern: each leg-condition obligation in a
    [cospan_equiv] proof reduces (via [change]) to a C-level equation
    over morphisms in [C].  The bridging lemmas below normalise the
    composite [pushout_in1 P ∘ cospan_in1 f] style expressions and
    provide rewrites for the [cover]/[merge] interaction with the
    pullback/pushout mediator. *)

(** ** Section 1: C^op composition reads as flipped C composition

    The fundamental identity: [f ∘[C^op] g ≈[C^op] h]  iff
    [g ∘[C] f ≈[C] h].  These wrappers let goals built out of
    [cospan_compose], [cospan_in1], etc. be normalised to C-level
    arithmetic without having to wave the C^op flag manually. *)

Section CopComp.

Context {C : Category}.

(** Composition in [C^op] of [f : x ~{C^op}~> y] and [g : y ~{C^op}~> z]
    is composition in [C] of [g : z ~{C}~> y] and [f : y ~{C}~> x] in
    flipped order. *)
Lemma cop_compose_eq {x y z : C}
      (f : x ~{C^op}~> y) (g : y ~{C^op}~> z) :
  (g ∘[C^op] f) = (f ∘[C] g).
Proof. reflexivity. Qed.

(** [id] in [C^op] and [id] in [C] coincide at the data level. *)
Lemma cop_id_eq (x : C) : (@id (C^op) x) = (@id C x).
Proof. reflexivity. Qed.

End CopComp.

(** ** Section 2: Cospan-equiv lifted from C-level apex isos

    The most common pattern: we have a C-level iso of apexes [phi : N ≅ M]
    and we want a cospan_equiv between two cospans whose apexes are
    related by [phi].  The two leg-conditions amount to two C-level
    equations. *)

Section CospanEquivFromCIso.

Context {C : Category}.

(** Build a [cospan_equiv] from a C-iso of apexes and two C-level
    leg-relations.  This is just a re-export of the C^op-iso-with-
    C-equations pattern that recurs throughout.

    Note: [span_equiv] requires [phi : apex f ≅[C^op] apex g] with
    [leg1 g ∘[C^op] to phi ≈ leg1 f], which in C-direction reads as
    [to phi ∘[C] cospan_in1 g ≈ cospan_in1 f].  The user-facing
    [phi] here is a [C]-iso from [cospan_apex g] to [cospan_apex f]
    (so its [to] in C goes [cospan_apex g ~> cospan_apex f]); this
    matches the C-direction of the equation. *)
Lemma cospan_equiv_intro {X Y : C}
      (f g : CospanArrow X Y)
      (phi : cospan_apex g ≅ cospan_apex f)
      (Hin1 : to phi ∘ cospan_in1 g ≈ cospan_in1 f)
      (Hin2 : to phi ∘ cospan_in2 g ≈ cospan_in2 f) :
  cospan_equiv f g.
Proof.
  unfold cospan_equiv, span_equiv.
  (* span_equiv needs [psi : apex f ≅[C^op] apex g] with
     [leg1 g ∘[C^op] to psi ≈ leg1 f].
     [Isomorphism_Opposite (iso_sym phi)] gives such a psi with
     [to psi = from (iso_sym phi) = to phi : apex g ~{C}~> apex f
                                  = apex f ~{C^op}~> apex g]. *)
  exists (Isomorphism_Opposite (iso_sym phi)).
  simpl.
  split; [exact Hin1 | exact Hin2].
Defined.

End CospanEquivFromCIso.

(** ** Section 3: Pushout/cover bridging

    When proving the bifunctor [fmap_comp] for [cospan_tensor], the leg
    conditions involve a [merge]-of-mediators composed against
    [cover]-style legs.  The fundamental simplification:

       (m1 ▽ m2) ∘ inl ≈ m1   (by inl_merge)
       (m1 ▽ m2) ∘ inr ≈ m2   (by inr_merge)
       cover f g ∘ inl ≈ inl ∘ f  (by cover_inl)
       cover f g ∘ inr ≈ inr ∘ g  (by cover_inr)

    The trouble in Phase 2 was associativity-direction: the rewrites
    above need the inner composition in a specific shape.  These bridge
    lemmas pre-associate the chain so the rewrites match. *)

Section PushoutCoverBridging.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(** When you have a [merge ∘ cover] composite, you can bring the
    [inl/inr] selector across to the C-level: *)

Lemma merge_cover_inl
      {a b c d e : C}
      (m1 : c ~> e) (m2 : d ~> e)
      (h1 : a ~> c) (h2 : b ~> d) :
  (m1 ▽ m2) ∘ (cover h1 h2) ∘ inl ≈ m1 ∘ h1.
Proof.
  rewrite <- comp_assoc.
  rewrite cover_inl.
  rewrite comp_assoc.
  rewrite inl_merge.
  reflexivity.
Qed.

Lemma merge_cover_inr
      {a b c d e : C}
      (m1 : c ~> e) (m2 : d ~> e)
      (h1 : a ~> c) (h2 : b ~> d) :
  (m1 ▽ m2) ∘ (cover h1 h2) ∘ inr ≈ m2 ∘ h2.
Proof.
  rewrite <- comp_assoc.
  rewrite cover_inr.
  rewrite comp_assoc.
  rewrite inr_merge.
  reflexivity.
Qed.

(** Variant: when the [merge] is composed with an [inl] on the right
    via two-step composition, you can collapse directly. *)
Lemma merge_inl_assoc
      {a c d e : C} (m1 : c ~> e) (m2 : d ~> e) (h : a ~> c) :
  (m1 ▽ m2) ∘ inl ∘ h ≈ m1 ∘ h.
Proof.
  rewrite inl_merge; reflexivity.
Qed.

Lemma merge_inr_assoc
      {b c d e : C} (m1 : c ~> e) (m2 : d ~> e) (h : b ~> d) :
  (m1 ▽ m2) ∘ inr ∘ h ≈ m2 ∘ h.
Proof.
  rewrite inr_merge; reflexivity.
Qed.

End PushoutCoverBridging.

(** ** Section 4: Coproduct mediator extensionality

    A morphism out of a coproduct is determined by its action on [inl]
    and [inr].  This is the joint-epi property — already available as
    [merge_inv]/[fork_inv], but stated here in a form convenient for
    cospan-leg goals. *)

Section CoprodJointEpi.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(** Two morphisms out of a coproduct are equal iff they agree on
    [inl] and [inr]. *)
Lemma coprod_ext {a b c : C} (u v : a + b ~> c) :
  u ∘ inl ≈ v ∘ inl -> u ∘ inr ≈ v ∘ inr -> u ≈ v.
Proof.
  intros Hl Hr.
  (* u ≈ u ∘ id ≈ u ∘ (inl ▽ inr) ≈ (u ∘ inl) ▽ (u ∘ inr) *)
  rewrite <- (id_right u).
  rewrite <- merge_inl_inr.
  rewrite <- merge_comp.
  rewrite Hl, Hr.
  rewrite merge_comp.
  rewrite merge_inl_inr.
  rewrite id_right.
  reflexivity.
Qed.

End CoprodJointEpi.

(** ** Section 5: Cospan-compose accessors restated cleanly

    The library already has [cospan_compose_in1/in2] as reflexivity
    lemmas; this section provides a few derived rewrites useful for
    the bifunctor proof. *)

Section CospanComposeRewrites.

Context {C : Category}.
Context (HP : HasPushouts C).

(** Apex of a cospan-composite is the pushout apex.  Restated as an
    equation rather than a [reflexivity] so [rewrite] can use it. *)
Lemma cospan_compose_apex_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_apex (cospan_compose HP g f)
  = pushout_apex (pushout (cospan_in2 f) (cospan_in1 g)).
Proof. reflexivity. Qed.

(** The leg-1 of a composite is [pushout_in1 ∘ cospan_in1 f]. *)
Lemma cospan_compose_in1_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in1 (cospan_compose HP g f)
  ≈ pushout_in1 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in1 f.
Proof. reflexivity. Qed.

Lemma cospan_compose_in2_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in2 (cospan_compose HP g f)
  ≈ pushout_in2 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in2 g.
Proof. reflexivity. Qed.

End CospanComposeRewrites.

(** ** Section 6: pushout_in1/in2 are C-morphisms

    Reminder type aliases: when the goal mentions [pullback_fst _ _ P]
    after unfolding [cospan_compose], the term is identical to
    [pushout_in1 P] in C (as objects in [C^op] flip arrow direction,
    [pullback_fst] in [C^op] becomes [pushout_in1] in [C]).

    These [change]-friendly equalities help rewrites land. *)

Section PullbackPushoutAlias.

Context {C : Category}.

Lemma pullback_fst_is_pushout_in1
      {x y z : C} (f : x ~> y) (g : x ~> z)
      (P : IsPushout f g) :
  @pullback_fst (C^op) y z x f g P = pushout_in1 P.
Proof. reflexivity. Qed.

Lemma pullback_snd_is_pushout_in2
      {x y z : C} (f : x ~> y) (g : x ~> z)
      (P : IsPushout f g) :
  @pullback_snd (C^op) y z x f g P = pushout_in2 P.
Proof. reflexivity. Qed.

End PullbackPushoutAlias.
