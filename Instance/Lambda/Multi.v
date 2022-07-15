Require Import
  Category.Instance.Lambda.Lib
  Category.Instance.Lambda.Ltac
  Category.Instance.Lambda.Ty
  Category.Instance.Lambda.Exp
  Category.Instance.Lambda.Value
  Category.Instance.Lambda.Ren
  Category.Instance.Lambda.Sub
  Category.Instance.Lambda.Sem
  Category.Instance.Lambda.Step.

From Equations Require Import Equations.
Set Equations With UIP.

Section Multi.

Generalizable All Variables.

Import ListNotations.

Inductive multi `(R : relation X) : relation X :=
  | multi_refl (x : X) : multi R x x
  | multi_step (x y z : X) :
      R x y → multi R y z → multi R x z.

Derive Signature for multi.

Theorem multi_R `(R : relation X) (x y : X) :
  R x y → multi R x y.
Proof.
  intros.
  eapply multi_step; eauto.
  now constructor.
Qed.

Theorem multi_trans `(R : relation X) (x y z : X) :
  multi R x y →
  multi R y z →
  multi R x z.
Proof.
  intros.
  induction H; auto.
  now eapply multi_step; eauto.
Qed.

#[export]
Program Instance multi_PreOrder `(R : relation X) :
  PreOrder (multi R).
Next Obligation. now constructor. Qed.
Next Obligation. now eapply multi_trans; eauto. Qed.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).

#[export]
Program Instance multi_respects_Step {Γ τ} :
  Proper (Step --> Step ==> impl) (multi (Step (Γ:=Γ) (τ:=τ))).
Next Obligation.
  econstructor; eauto.
  generalize dependent y0.
  generalize dependent y.
  induction H1; intros; eauto.
  - now do 4 (econstructor; eauto).
  - unfold flip in *.
    now econstructor; eauto.
Qed.

#[export]
Program Instance multi_respects_multi `(R : relation X) :
  Proper (multi R --> multi R ==> impl) (multi R).
Next Obligation.
  unfold flip in *.
  transitivity x; eauto.
  now transitivity x0; eauto.
Qed.

Ltac simpl_multistep :=
  intros;
  match goal with
  | [ H : _ --->* _ |- _ ] => induction H
  end;
  [ now apply multi_refl
  | eapply multi_step; eauto;
    now econstructor; eauto ].

#[local] Hint Constructors ValueP Step : core.

#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

Corollary values_final {Γ τ} {e e' : Exp Γ τ} :
  e --->* e' → ValueP e → e = e'.
Proof.
  intros.
  apply value_is_nf in H0.
  unfold normal_form in H0.
  induction H; auto.
  now intuition.
Qed.

Lemma multistep_AppR {Γ dom cod} {e e' : Γ ⊢ dom} {v : Γ ⊢ (dom ⟶ cod)} :
  (e --->* e') → ValueP v → APP v e --->* APP v e'.
Proof.
  intros.
  induction H.
  - now apply multi_refl.
  - rewrite <- IHmulti; clear IHmulti; auto.
    inv H0.
    eapply (AppR_LAM (e:=e)) in H.
    + now apply multi_R.
Qed.

End Multi.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).
