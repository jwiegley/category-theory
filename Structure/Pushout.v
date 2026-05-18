Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.

Generalizable All Variables.

(** * Pushouts: ergonomic accessors

    A pushout of a span [B <-f- A -g-> C] in [C] is a pullback of the dual
    cospan in [C^op].  The library defines

        Definition Pushout {C} {x y z : C^op} (f : x ~> z) (g : y ~> z)
          := Pullback f g.

    which forces users to write their morphisms in [C^op] (i.e. reversed).
    This file provides a thin convenience layer that takes the span in [C]
    directly, plus a [HasPushouts] predicate that quantifies the existence of
    all binary pushouts.

    The accessors [pushout_apex], [pushout_in1], [pushout_in2],
    [pushout_commutes] and [pushout_ump] are written with the morphisms
    inverted to the underlying [Pullback] representation, so downstream code
    can think entirely in terms of [C]. *)

Section Pushout.

Context {C : Category}.

(** Pushout of the span [y <-f- x -g-> z]. *)
Definition IsPushout {x y z : C} (f : x ~> y) (g : x ~> z) : Type :=
  @Pullback (C^op) y z x f g.

Definition pushout_apex {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : C :=
  @Pull (C^op) y z x f g P.

Definition pushout_in1 {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : y ~{C}~> pushout_apex P :=
  @pullback_fst (C^op) y z x f g P.

Definition pushout_in2 {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g) : z ~{C}~> pushout_apex P :=
  @pullback_snd (C^op) y z x f g P.

(** The square commutes: both legs precomposed with the span agree. *)
Lemma pushout_commutes {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g) :
  pushout_in1 P ∘ f ≈ pushout_in2 P ∘ g.
Proof.
  exact (@pullback_commutes (C^op) y z x f g P).
Qed.

(** The universal property: given any other cocone over the same span there
    is a unique mediating morphism from the pushout apex. *)
Lemma pushout_ump {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      (Q : C) (q1 : y ~> Q) (q2 : z ~> Q)
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  ∃! u : pushout_apex P ~> Q,
    u ∘ pushout_in1 P ≈ q1 ∧ u ∘ pushout_in2 P ≈ q2.
Proof.
  exact (@ump_pullbacks (C^op) y z x f g P Q q1 q2 Hcomm).
Qed.

(** Convenience: the mediating morphism out of a pushout. *)
Definition pushout_med {x y z : C} {f : x ~> y} {g : x ~> z}
           (P : IsPushout f g)
           {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
           (Hcomm : q1 ∘ f ≈ q2 ∘ g)
  : pushout_apex P ~> Q :=
  unique_obj (pushout_ump P Q q1 q2 Hcomm).

Lemma pushout_med_in1 {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  pushout_med P Hcomm ∘ pushout_in1 P ≈ q1.
Proof.
  unfold pushout_med.
  destruct (unique_property (pushout_ump P Q q1 q2 Hcomm)) as [H _].
  exact H.
Qed.

Lemma pushout_med_in2 {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g) :
  pushout_med P Hcomm ∘ pushout_in2 P ≈ q2.
Proof.
  unfold pushout_med.
  destruct (unique_property (pushout_ump P Q q1 q2 Hcomm)) as [_ H].
  exact H.
Qed.

Lemma pushout_med_unique {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g)
      (v : pushout_apex P ~> Q) :
  v ∘ pushout_in1 P ≈ q1 -> v ∘ pushout_in2 P ≈ q2 ->
  pushout_med P Hcomm ≈ v.
Proof.
  intros H1 H2.
  unfold pushout_med.
  apply (uniqueness (pushout_ump P Q q1 q2 Hcomm)); split; assumption.
Qed.

(** Equality lemma: two mediators out of a pushout that agree on both
    pushout legs are equal.  Useful for showing [u ≈ v] without
    exhibiting the intermediate [pushout_med] explicitly. *)
Lemma pushout_med_eq {x y z : C} {f : x ~> y} {g : x ~> z}
      (P : IsPushout f g)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q}
      (Hcomm : q1 ∘ f ≈ q2 ∘ g)
      (u v : pushout_apex P ~> Q) :
  u ∘ pushout_in1 P ≈ q1 ->
  u ∘ pushout_in2 P ≈ q2 ->
  v ∘ pushout_in1 P ≈ q1 ->
  v ∘ pushout_in2 P ≈ q2 ->
  u ≈ v.
Proof.
  intros Hu1 Hu2 Hv1 Hv2.
  transitivity (pushout_med P Hcomm).
  - symmetry. apply pushout_med_unique; assumption.
  - apply pushout_med_unique; assumption.
Qed.

End Pushout.

(** A category has all binary pushouts if every span has a pushout. *)
Class HasPushouts (C : Category) : Type := {
  pushout : forall {x y z : C} (f : x ~> y) (g : x ~> z), IsPushout f g
}.

Arguments pushout {C _ x y z} f g.

(** [HasPushouts C] is exactly [HasPullbacks (C^op)] by definitional
    unfolding of [IsPushout].  We expose both directions of the equivalence
    as functions so the two predicates can be interchanged at will. *)
Definition HasPullbacks_op_of_HasPushouts
           {C : Category} (HP : HasPushouts C) : HasPullbacks (C^op).
Proof.
  unshelve econstructor.
  intros x y z f g.
  (* A pullback in C^op of f : x ~{C^op}~> z, g : y ~{C^op}~> z is a pushout in
     C of f : z ~{C}~> x, g : z ~{C}~> y; the latter is supplied by [HP]. *)
  exact (@pushout C HP z x y f g).
Defined.

Definition HasPushouts_of_HasPullbacks_op
           {C : Category} (HP : HasPullbacks (C^op)) : HasPushouts C.
Proof.
  unshelve econstructor.
  intros x y z f g.
  exact (@pullback (C^op) HP y z x f g).
Defined.
