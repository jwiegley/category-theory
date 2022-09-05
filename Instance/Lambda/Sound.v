Require Import Category.Instance.Lambda.Lib.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Sem.
Require Import Category.Instance.Lambda.Step.

From Equations Require Import Equations.
Set Equations With UIP.

Section Sound.

Generalizable All Variables.

Import ListNotations.

Theorem soundness {Γ τ} {e : Exp Γ τ} {v} :
  e ---> v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto;
  extensionality se.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - now rewrite IHStep.
  - rewrite <- SemExp_SubSem.
    f_equal; simpl.
    simp SubSem.
    now rewrite SubSem_idSub.
  - now rewrite IHStep.
  - now rewrite IHStep.
Qed.

End Sound.
