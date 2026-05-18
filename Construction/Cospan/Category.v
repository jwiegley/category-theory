Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Span.Category.

Generalizable All Variables.

(** * The cospan category (dual derivation)

    A cospan from [X] to [Y] in [C] is a span from [X] to [Y] in [C^op]:
    the apex is the same object, and the two legs flip direction.  We expose
    cospans through ergonomic notation that hides the [C^op] but reuse the
    full machinery — equivalence, composition via pullback in [C^op] (which
    is a pushout in [C]), proper instances, identity and associativity
    proofs — from [Construction.Span.Category].

    User-facing API:

      - [CospanArrow X Y]   — the record of cospans from [X] to [Y]
      - [cospan_apex f]     — the apex
      - [cospan_in1 f]      — the leg [X ~> apex]
      - [cospan_in2 f]      — the leg [Y ~> apex]
      - [CospanCat C HP]    — the category of cospans

    No [C^op] symbol leaks into downstream code. *)

(** A cospan is exactly a span in the opposite category. *)
Definition CospanArrow {C : Category} (X Y : C) : Type :=
  @SpanArrow (C^op) X Y.

(** Ergonomic constructor: build a cospan from an apex and two legs in [C]. *)
Definition Build_CospanArrow {C : Category} {X Y : C}
           (N : C) (l1 : X ~{C}~> N) (l2 : Y ~{C}~> N) : CospanArrow X Y :=
  @Build_SpanArrow (C^op) X Y N l1 l2.

(** Apex of a cospan (lives in [C]). *)
Definition cospan_apex {C : Category} {X Y : C} (f : CospanArrow X Y) : C :=
  @apex (C^op) X Y f.

(** The two legs go INTO the apex in [C]. *)
Definition cospan_in1 {C : Category} {X Y : C} (f : CospanArrow X Y)
  : X ~{C}~> cospan_apex f :=
  @leg1 (C^op) X Y f.

Definition cospan_in2 {C : Category} {X Y : C} (f : CospanArrow X Y)
  : Y ~{C}~> cospan_apex f :=
  @leg2 (C^op) X Y f.

(** Equivalence on cospans: iso of apexes intertwining both legs. *)
Definition cospan_equiv {C : Category} {X Y : C} (f g : CospanArrow X Y) : Type :=
  @span_equiv (C^op) X Y f g.

(** The cospan setoid (delegates to [SpanArrow_Setoid] in [C^op]). *)
#[export] Program Instance CospanArrow_Setoid {C : Category} {X Y : C} :
  Setoid (CospanArrow X Y) := @SpanArrow_Setoid (C^op) X Y.

(** Identity cospan: apex is [X], both legs are identity. *)
Definition cospan_id {C : Category} (X : C) : CospanArrow X X :=
  @span_id (C^op) X.

(** Cospan composition (pushout in [C], pullback in [C^op]). *)
Definition cospan_compose {C : Category} (HP : HasPushouts C)
           {X Y Z : C}
           (g : CospanArrow Y Z) (f : CospanArrow X Y) : CospanArrow X Z :=
  @span_compose (C^op) (HasPullbacks_op_of_HasPushouts HP) X Y Z g f.

(** ** Cospan composition: what comes out, in [C]-vocabulary

    Given [g : Y ~> Z] (cospan with apex [N_g], legs [cospan_in1 g : Y ~> N_g],
    [cospan_in2 g : Z ~> N_g]) and [f : X ~> Y] (cospan with apex [N_f]), the
    composite [cospan_compose HP g f] has apex equal to the pushout of
    [cospan_in2 f : Y ~> N_f] and [cospan_in1 g : Y ~> N_g] in [C], with
    legs [pushout_in1 ∘ cospan_in1 f] and [pushout_in2 ∘ cospan_in2 g].

    These three accessor lemmas hold by [reflexivity] — the definitional
    unfolding of [cospan_compose] through [span_compose] in [C^op] lines up
    exactly with the pushout-of-pushout shape in [C].  No [C^op] reasoning
    is required downstream. *)

Section CospanCompositionAccessors.

Context {C : Category}.
Context (HP : HasPushouts C).

Lemma cospan_compose_apex {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_apex (cospan_compose HP g f)
  = pushout_apex (pushout (cospan_in2 f) (cospan_in1 g)).
Proof. reflexivity. Qed.

Lemma cospan_compose_in1 {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in1 (cospan_compose HP g f)
  ≈ pushout_in1 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in1 f.
Proof. reflexivity. Qed.

Lemma cospan_compose_in2 {X Y Z : C}
      (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_in2 (cospan_compose HP g f)
  ≈ pushout_in2 (pushout (cospan_in2 f) (cospan_in1 g)) ∘ cospan_in2 g.
Proof. reflexivity. Qed.

End CospanCompositionAccessors.

(** The cospan category — a thin dual derivation of [SpanCat (C^op)]. *)
Definition CospanCat (C : Category) (HP : HasPushouts C) : Category :=
  SpanCat (C^op) (HasPullbacks_op_of_HasPushouts HP).

(** ** User-facing identity and associativity re-exports *)

Section CospanLaws.

Context {C : Category}.
Context (HP : HasPushouts C).

Lemma cospan_id_left {X Y : C} (f : CospanArrow X Y) :
  cospan_equiv (cospan_compose HP (cospan_id Y) f) f.
Proof.
  exact (@span_id_left (C^op) (HasPullbacks_op_of_HasPushouts HP) X Y f).
Defined.

Lemma cospan_id_right {X Y : C} (f : CospanArrow X Y) :
  cospan_equiv (cospan_compose HP f (cospan_id X)) f.
Proof.
  exact (@span_id_right (C^op) (HasPullbacks_op_of_HasPushouts HP) X Y f).
Defined.

Lemma cospan_compose_assoc {X Y Z W : C}
      (h : CospanArrow Z W) (g : CospanArrow Y Z) (f : CospanArrow X Y) :
  cospan_equiv
    (cospan_compose HP h (cospan_compose HP g f))
    (cospan_compose HP (cospan_compose HP h g) f).
Proof.
  exact (@span_compose_assoc (C^op)
           (HasPullbacks_op_of_HasPushouts HP) X Y Z W h g f).
Defined.

End CospanLaws.
