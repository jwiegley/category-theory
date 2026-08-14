Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Limit.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Essential uniqueness of limits: reconciliations

    Structure/Limit/Unique.v proves Riehl's Proposition 3.1.7 from the
    mediator calculus.  This satellite ties the three pre-existing
    routes to it, so they stop being unrelated developments:

    - [equalizer_unique] (Structure/Equalizer/Fork.v) and
      [pullback_unique] (Structure/Pullback.v) are the hand-rolled
      shape-specific results, each concluding a bare ≅ from its own
      universal property.  Through the in-tree bridges
      ([is_equalizer_limit], [Pullback_from_Universal]) both are shown
      to AGREE with [limit_unique_iso]: the isomorphisms have the same
      forward component ([equalizer_unique_agrees],
      [pullback_unique_agrees]).  Their terminating [Qed]s become
      [Defined]s for exactly this purpose — the statements say nothing
      about the components, so agreement is expressible only against
      the transparent terms; no proof text changed.  In particular the
      general theorem strictly subsumes both: it adds the
      leg-commutation equations and the uniqueness clause the bare ≅
      lacked.

    - [univ_property_unique_up_to_unique_iso]
      (Structure/UniversalProperty.v) is the generic representability
      route, in tree instantiated only at terminal and initial objects
      (Structure/UniversalProperty/Terminal.v) and never at limits —
      the gap issue #950 records.  [limit_unique_up_to_transport_iso]
      takes it at [LimitIsUniversalProperty]: two limit witnesses of one diagram
      are related by an isomorphism (in C^op) UNIQUE among those
      transporting one witness's representation to the other's.  The
      identification of that transport with precomposition of the limit
      legs — which would let the generic isomorphism be compared
      componentwise with [limit_unique_iso] — is NOT proved here: the
      generic route's representation equivalence is assembled by hint
      automation, and no in-tree lemma characterises its action on leg
      families (the gap issue #950 itself documents).  What this file
      contributes is the instantiation, so the generic statement is
      finally available at limits at all; the componentwise comparison
      remains open alongside that characterisation. *)

(** ** Equalizers: the elementary uniqueness agrees *)

Section EqualizerAgrees.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~{C}~> y).

(* An elementary equalizer, read as a limit witness pinned at its own
   apex, through Fork.v's bridge. *)
Definition is_equalizer_alimit {q : C} {e : q ~> x}
  (E : IsEqualizer f g q e) : IsALimit (APair f g) q :=
  limit_is_alimit (is_equalizer_limit f g E).

(* The two forward components coincide, and with them the whole
   isomorphisms ([equalizer_unique_agrees_iso], one line through
   [to_equiv_implies_iso_equiv]).  The general result adds what the
   bare ≅ could not say: the legs and the uniqueness clause of
   [limit_unique_iso_unique]. *)
Theorem equalizer_unique_agrees {q1 q2 : C} {e1 : q1 ~> x} {e2 : q2 ~> x}
  (E1 : IsEqualizer f g q1 e1) (E2 : IsEqualizer f g q2 e2) :
  to (equalizer_unique f g E1 E2)
    ≈ to (limit_unique_iso (is_equalizer_alimit E1)
                           (is_equalizer_alimit E2)).
Proof.
  apply limit_unique_iso_unique; intro p; destruct p; simpl.
  - exact (unique_property (eq_desc E2 e1 (fork_eq E1))).
  - transitivity (f ∘ (e2 ∘ unique_obj (eq_desc E2 e1 (fork_eq E1)))).
    { symmetry; apply comp_assoc. }
    now rewrite (unique_property (eq_desc E2 e1 (fork_eq E1))).
Qed.

(* ...and therefore the isomorphisms agree outright. *)
Theorem equalizer_unique_agrees_iso {q1 q2 : C} {e1 : q1 ~> x}
  {e2 : q2 ~> x}
  (E1 : IsEqualizer f g q1 e1) (E2 : IsEqualizer f g q2 e2) :
  equalizer_unique f g E1 E2
    ≈ limit_unique_iso (is_equalizer_alimit E1) (is_equalizer_alimit E2).
Proof.
  apply to_equiv_implies_iso_equiv, equalizer_unique_agrees.
Qed.

End EqualizerAgrees.

(** ** Pullbacks: the elementary uniqueness agrees *)

Section PullbackAgrees.

Context {C : Category}.
Context {x y z : C}.
Context (f : x ~{C}~> z) (g : y ~{C}~> z).

(* A pullback square, read as a limit witness pinned at its own apex,
   through Pullback/Limit.v's bridge. *)
Definition pullback_alimit (P : Pullback f g) :
  IsALimit ((@ASpan (C^op) _ _ _ f g)^op) (Pull f g P) :=
  limit_is_alimit (Pullback_from_Universal f g P).

Theorem pullback_unique_agrees (P Q : Pullback f g) :
  to (pullback_unique P Q)
    ≈ to (limit_unique_iso (pullback_alimit P) (pullback_alimit Q)).
Proof.
  assert (T : to (pullback_unique P Q)
                ≈ unique_obj (ump_pullbacks f g Q (Pull f g P)
                     (pullback_fst f g P) (pullback_snd f g P)
                     (pullback_commutes f g P))).
  { unfold pullback_unique; simpl.
    destruct (unique_property
      (ump_pullbacks f g Q (Pull f g P) (pullback_fst f g P)
         (pullback_snd f g P) (pullback_commutes f g P))).
    destruct (unique_property
      (ump_pullbacks f g P (Pull f g Q) (pullback_fst f g Q)
         (pullback_snd f g Q) (pullback_commutes f g Q))).
    reflexivity. }
  rewrite T.
  destruct (unique_property
    (ump_pullbacks f g Q (Pull f g P) (pullback_fst f g P)
       (pullback_snd f g P) (pullback_commutes f g P))) as [HQfst HQsnd].
  apply limit_unique_iso_unique; intro r; destruct r.
  - exact HQfst.
  - transitivity
      (f ∘ (pullback_fst f g Q
              ∘ unique_obj (ump_pullbacks f g Q (Pull f g P)
                   (pullback_fst f g P) (pullback_snd f g P)
                   (pullback_commutes f g P)))).
    { symmetry; apply comp_assoc. }
    now rewrite HQfst.
  - exact HQsnd.
Qed.

Theorem pullback_unique_agrees_iso (P Q : Pullback f g) :
  pullback_unique P Q
    ≈ limit_unique_iso (pullback_alimit P) (pullback_alimit Q).
Proof.
  apply to_equiv_implies_iso_equiv, pullback_unique_agrees.
Qed.

End PullbackAgrees.

(** ** The generic representability route, finally instantiated *)

Section TransportUnique.

Context {J : Category}.
Context {C : Category}.
Context (F : J ⟶ C).

(* The composite never before formed at limits:
   [univ_property_unique_up_to_unique_iso] at
   [LimitIsUniversalProperty].  Two limit witnesses of one diagram
   are related by an isomorphism (of C^op, the representability side's
   home) unique among those transporting the one representation to the
   other. *)
Definition limit_unique_up_to_transport_iso
  (c d : C) (Hc : IsALimit F c) (Hd : IsALimit F d) :
  @Unique (@Isomorphism C^op c d) _
    (fun p =>
       @univ_property_respects_iso C^op (fun v => IsALimit F v)
         (fun v => @LimitSetoid J C F v)
         (LimitIsUniversalProperty J C F) c d p Hc ≈ Hd) :=
  @univ_property_unique_up_to_unique_iso C^op
    (fun v => IsALimit F v)
    (fun v => @LimitSetoid J C F v)
    (LimitIsUniversalProperty J C F) c d Hc Hd.

End TransportUnique.
