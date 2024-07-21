From Coq Require Import Utf8.
From Coq Require Import Program.

Local Set Warnings "-deprecated-notation".

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

Ltac inv H := inversion H; subst; clear H; reduce.

Ltac equality := intuition congruence.
