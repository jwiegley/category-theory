Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sub.
Require Import Category.Instance.Lambda.Sem.
Require Import Category.Instance.Lambda.Step.

From Equations Require Import Equations.
Set Equations With UIP.

Local Ltac Tauto.intuition_solver ::= auto with eqdep solve_subterm exfalso.

Section Multi.

Generalizable All Variables.

Inductive multi `(R : crelation X) : crelation X :=
  | multi_refl (x : X) : multi x x
  | multi_step (x y z : X) : R x y → multi y z → multi x z.

Derive Signature for multi.

Theorem multi_R `(R : crelation X) (x y : X) :
  R x y → multi R x y.
Proof.
  intros.
  eapply multi_step; eauto.
  now constructor.
Qed.

Theorem multi_trans `(R : crelation X) (x y z : X) :
  multi R x y →
  multi R y z →
  multi R x z.
Proof.
  intros.
  induction X0; auto.
  now eapply multi_step; eauto.
Qed.

#[export]
Program Instance multi_PreOrder `(R : crelation X) :
  PreOrder (multi R).
Next Obligation. now constructor. Qed.
Next Obligation. now eapply multi_trans; eauto. Qed.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).

#[export]
Program Instance multi_respects_Step {Γ τ} :
  Proper (Step --> Step ==> arrow) (multi (Step (Γ:=Γ) (τ:=τ))).
Next Obligation.
  econstructor; eauto.
  generalize dependent y0.
  generalize dependent y.
  induction X; intros; eauto.
  - now do 4 (econstructor; eauto).
  - unfold flip in *.
    now econstructor; eauto.
Qed.

#[export]
Program Instance multi_respects_multi `(R : crelation X) :
  Proper (multi R --> multi R ==> arrow) (multi R).
Next Obligation.
  unfold flip in *.
  transitivity x; eauto.
  now transitivity x0; eauto.
Qed.

#[local] Hint Constructors ValueP Step : core.

#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

Corollary values_final {Γ τ} {e e' : Exp Γ τ} :
  e --->* e' → ValueP e → e = e'.
Proof.
  intros.
  apply value_is_nf in H.
  unfold normal_form in H.
  induction X; auto.
  now intuition.
Qed.

Lemma multistep_AppR {Γ dom cod} {e e' : Γ ⊢ dom} {v : Γ ⊢ (dom ⟶ cod)} :
  (e --->* e') → ValueP v → APP v e --->* APP v e'.
Proof.
  intros.
  induction X.
  - now apply multi_refl.
  - rewrite <- IHX; clear IHX; auto.
    inv H.
    eapply (AppR_LAM (e:=e)) in r.
    now apply multi_R.
Qed.

Ltac simpl_multistep :=
  intros;
  match goal with
  | [ H : _ --->* _ |- _ ] => induction H
  end;
  [ now apply multi_refl
  | eapply multi_step; eauto;
    now econstructor; eauto ].

Lemma multistep_Pair1 {Γ τ1 τ2} {e1 e1' : Γ ⊢ τ1} {e2 : Γ ⊢ τ2} :
  (e1 --->* e1') → Pair e1 e2 --->* Pair e1' e2.
Proof. now simpl_multistep. Qed.

Lemma multistep_Pair2 {Γ τ1 τ2} {e1 : Γ ⊢ τ1} {e2 e2' : Γ ⊢ τ2} :
  ValueP e1 → (e2 --->* e2') → Pair e1 e2 --->* Pair e1 e2'.
Proof. now simpl_multistep. Qed.

Lemma multistep_Pair {Γ τ1 τ2} {e1 e1' : Γ ⊢ τ1} {e2 e2' : Γ ⊢ τ2} :
  ValueP e1' →
  (e1 --->* e1') → (e2 --->* e2') → Pair e1 e2 --->* Pair e1' e2'.
Proof.
  intros.
  erewrite multistep_Pair1; eauto.
  erewrite multistep_Pair2; eauto.
  now apply multi_refl.
Qed.

Lemma multistep_Fst1 {Γ τ1 τ2} {p p' : Γ ⊢ (τ1 × τ2)} :
  (p --->* p') → Fst p --->* Fst p'.
Proof. now simpl_multistep. Qed.

Lemma multistep_Snd1 {Γ τ1 τ2} {p p' : Γ ⊢ (τ1 × τ2)} :
  (p --->* p') → Snd p --->* Snd p'.
Proof. now simpl_multistep. Qed.

End Multi.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).
