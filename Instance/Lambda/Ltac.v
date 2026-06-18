From Coq Require Import Utf8.
From Coq Require Import Program.

(** * Proof automation for the intrinsically-typed de Bruijn STLC.

    This module collects the general-purpose tactics shared across the
    [Instance.Lambda] development.  Because terms, values and the reduction
    relations are all indexed by typing contexts and types, proofs constantly
    produce heterogeneous ([JMeq], notation [~=]) equalities between
    differently-typed objects and equalities between dependent pairs
    ([existT]); these tactics discharge that bookkeeping so that proof scripts
    can focus on the operational content.  [Program] is imported for
    [inj_pair2] (injectivity of [existT] up to UIP, from [Coq.Logic.Eqdep]). *)

(* The [~=] (JMeq) notation is flagged deprecated by recent Rocq; silence the
   warning locally since it is pervasive in the dependently-typed goals below. *)
Local Set Warnings "-deprecated-notation".

(* [reduce_jmeq] specialises induction hypotheses (and other quantified
   premises) of the shape
       ∀ x .., a = b → p ~= q → .. → Goal
   by supplying the witnesses and discharging each side-condition with the
   reflexive proof [eq_refl] / [JMeq_refl].  Such hypotheses arise from
   [dependent induction] / [dependent destruction]: the equality premises
   record how the indices of the eliminated term match those at the recursive
   call, and at each use site they hold definitionally.  The match is unrolled
   for one to four trailing [~=] premises, optionally preceded by three
   implicit arguments and one homogeneous [=] premise, covering the arities
   that actually occur in this development. *)
Ltac reduce_jmeq :=
  repeat match goal with
  | [ H : ∀ _: _, _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _: _, _ ~= _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ JMeq_refl JMeq_refl JMeq_refl JMeq_refl)

  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl)
  | [ H : ∀ _ _ _, _ = _ → _ ~= _ → _ ~= _ → _ ~= _ → _ ~= _ → _ |- _ ] =>
      specialize (H _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl JMeq_refl)
  end.

(* [reduce] runs [reduce_jmeq], then exhaustively breaks apart structured
   hypotheses left in the context: it collapses [existT] equalities via
   [inj_pair2] (relying on UIP for the index type) and destructs conjunctions,
   pairs, existentials, [sig] ([{x | P}]) and [sigT] ([{x & P}]) witnesses,
   substituting freed variables along the way.  The net effect is to flatten a
   tangle of dependent-equality and packaging hypotheses into their plain
   components. *)
Ltac reduce :=
  reduce_jmeq;
  repeat (match goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H; subst
          | [ H : _ ∧ _ |- _ ] => destruct H
          | [ H : _ * _ |- _ ] => destruct H
          | [ H : ∃ _, _ |- _ ] => destruct H
          | [ H : { _ : _ | _ } |- _ ] => destruct H
          | [ H : { _ : _ & _ } |- _ ] => destruct H
          end; subst).

(* [inv H] is the usual "invert and clean up" idiom: derive the constructor
   constraints of [H] by [inversion], [subst] the resulting equations, discard
   the now-redundant [H], and finish with [reduce] to dispatch the dependent
   equalities (often [existT] equalities) that inversion of an indexed
   inductive leaves behind.  Used throughout to case-analyse the reduction and
   value judgements. *)
Ltac inv H := inversion H; subst; clear H; reduce.

(* [equality] closes goals that are purely a matter of (dis)equality between
   constructor terms, combining propositional reasoning ([intuition]) with the
   congruence-closure decision procedure ([congruence]). *)
Ltac equality := intuition congruence.
