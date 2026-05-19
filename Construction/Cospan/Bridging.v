Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(** * Cospan bridging helpers (direct-CospanCat version)

    With [CospanCat] now built directly via pushouts in [C] (rather than
    as [SpanCat (C^op)]), the cospan obligations are already phrased in
    terms of C-direction morphisms.  This file collects a few derived
    rewrites that come up repeatedly in Monoidal / SCFA / Hypergraph
    coherence proofs over [CospanCat C]. *)

(** ** Section 1: pushout/cover bridging

    When proving the bifunctor [fmap_comp] for [cospan_tensor], the leg
    conditions involve a [merge]-of-mediators composed against
    [cover]-style legs.  The fundamental simplifications are
    [merge ∘ cover] and [merge ∘ inl/inr]. *)

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

(** ** Section 2: Coproduct mediator extensionality

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

(** ** Section 3: Cospan-equiv ergonomic builder

    Builds a [cospan_equiv f g] from a C-iso of apexes plus two C-level
    leg-relations.  In the direct CospanCat this is just the record
    constructor, exposed here for clarity. *)

Section CospanEquivIntro.

Context {C : Category}.

Lemma cospan_equiv_intro {X Y : C}
      (f g : CospanArrow X Y)
      (phi : cospan_apex f ≅ cospan_apex g)
      (Hin1 : to phi ∘ cospan_in1 f ≈ cospan_in1 g)
      (Hin2 : to phi ∘ cospan_in2 f ≈ cospan_in2 g) :
  cospan_equiv f g.
Proof.
  exists phi; split; [exact Hin1 | exact Hin2].
Defined.

End CospanEquivIntro.

(** ** Section 4: Cospan-compose accessors restated cleanly

    The library already has [cospan_compose_in1/in2] as reflexivity
    lemmas; these are convenience aliases. *)

Section CospanComposeRewrites.

Context {C : Category}.
Context (HP : HasPushouts C).

Lemma cospan_compose_apex_eq {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_apex (cospan_compose HP g f)
  = pushout_apex (pushout (cospan_in2 f) (cospan_in1 g)).
Proof. reflexivity. Qed.

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
