Require Import
  Category.Instance.Lambda.Lib
  Category.Instance.Lambda.Ltac
  Category.Instance.Lambda.Ty
  Category.Instance.Lambda.Exp
  Category.Instance.Lambda.Value
  Category.Instance.Lambda.Ren
  Category.Instance.Lambda.Sub
  Category.Instance.Lambda.Sem
  Category.Instance.Lambda.Log.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Evaluation contexts *)

Section Step.

Import ListNotations.

Open Scope Ty_scope.

Reserved Notation " t '--->' t' " (at level 40).

Inductive Step : ∀ {Γ τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | ST_Pair1 Γ τ1 τ2 (x x' : Exp Γ τ1) (y : Exp Γ τ2) :
    x ---> x' →
    Pair x y ---> Pair x' y
  | ST_Pair2 Γ τ1 τ2 (x : Exp Γ τ1) (y y' : Exp Γ τ2) :
    ValueP x →
    y ---> y' →
    Pair x y ---> Pair x y'

  | ST_Fst1 Γ τ1 τ2 (p p' : Exp Γ (TyPair τ1 τ2)) :
    p ---> p' →
    Fst p ---> Fst p'
  | ST_FstPair Γ τ1 τ2 (v1 : Exp Γ τ1) (v2 : Exp Γ τ2) :
    ValueP v1 →
    ValueP v2 →
    Fst (Pair v1 v2) ---> v1

  | ST_Snd1 Γ τ1 τ2 (p p' : Exp Γ (TyPair τ1 τ2)) :
    p ---> p' →
    Snd p ---> Snd p'
  | ST_SndPair Γ τ1 τ2 (v1 : Exp Γ τ1) (v2 : Exp Γ τ2) :
    ValueP v1 →
    ValueP v2 →
    Snd (Pair v1 v2) ---> v2

  | ST_Beta Γ dom cod (e : Exp (dom :: Γ) cod) (v : Exp Γ dom) :
    ValueP v →
    APP (LAM e) v ---> SubExp {|| v ||} e

  | ST_AppL Γ dom cod (e1 : Exp Γ (dom ⟶ cod)) e1' (e2 : Exp Γ dom) :
    e1 ---> e1' →
    APP e1 e2 ---> APP e1' e2

  | ST_AppR Γ dom cod (v1 : Exp Γ (dom ⟶ cod)) (e2 : Exp Γ dom) e2' :
    ValueP v1 →
    e2 ---> e2' →
    APP v1 e2 ---> APP v1 e2'

  where " t '--->' t' " := (Step t t').

Derive Signature for Step.

#[local] Hint Constructors ValueP Step : core.

#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e; reduce.
  - now left; constructor.
  - destruct IHe1 as [V1|[e1' H1']];
    destruct IHe2 as [V2|[e2' H2']].
    + now left; constructor.
    + now right; eauto 6.
    + now right; eauto 6.
    + now right; eauto 6.
  - destruct IHe as [V|[e' H']].
    + dependent elimination V.
      * now right; eauto 6.
    + now right; eauto 6.
  - destruct IHe as [V|[e' H']].
    + dependent elimination V.
      * now right; eauto 6.
    + now right; eauto 6.
  - now inv v.
  - now left; constructor.
  - right.
    destruct IHe1 as [V1|[e1' H1']];
    destruct IHe2 as [V2|[e2' H2']].
    + dependent elimination V1;  now eauto 6.
    + dependent elimination H2'; now eauto 6.
    + dependent elimination H1'; now eauto 6.
    + dependent elimination H1'; now eauto 6.
Qed.

Lemma Value_irreducible {Γ τ} {e e' : Exp Γ τ} :
  ValueP e → ¬ (e ---> e').
Proof.
  repeat intro.
  dependent induction H0;
  dependent elimination H;
  intuition eauto.
Qed.

Lemma Value_cannot_start {Γ τ} {e e' : Exp Γ τ} :
  (e ---> e') → ¬ ValueP e.
Proof.
  repeat intro.
  dependent induction H0;
  dependent elimination H;
  intuition eauto.
Qed.

Lemma AppL_LAM {Γ dom cod} {e e' : Exp Γ (dom ⟶ cod)} {x : Exp Γ dom} :
  e ---> e' →
  APP e x ---> APP e' x.
Proof.
  intros.
  dependent induction H; now eauto 6.
Qed.

Lemma AppR_LAM {Γ dom cod} {e : Exp (dom :: Γ) cod} {x x' : Exp Γ dom} :
  x ---> x' →
  APP (LAM e) x ---> APP (LAM e) x'.
Proof.
  intros.
  dependent induction H; now eauto 6.
Qed.

(* Definition normal_form `(R : relation X) (t : X) : Prop := *)
(*   ¬ ∃ t', R t t'. *)
Definition normal_form `(R : relation X) (t : X) : Prop :=
  ∀ t', ¬ R t t'.

Definition deterministic `(R : relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Lemma value_is_nf {Γ τ} (v : Exp Γ τ) :
  ValueP v → normal_form Step v.
Proof.
  repeat intro.
  dependent induction H0;
  now inv H.
Qed.

Theorem Step_deterministic Γ τ :
  deterministic (Step (Γ:=Γ) (τ:=τ)).
Proof.
  repeat intro.
  induction H0.
  - inv H.
    + now f_equal; intuition.
    + eapply Value_cannot_start in H5; eauto; tauto.
  - inv H.
    + eapply Value_cannot_start in H4; eauto; tauto.
    + now f_equal; intuition.
  - inv H.
    + now f_equal; intuition.
    + inv H0.
      * eapply Value_cannot_start in H6; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
  - inv H.
    + inv H5.
      * eapply Value_cannot_start in H3; eauto; tauto.
      * eapply Value_cannot_start in H1; eauto; tauto.
    + now f_equal; intuition.
  - inv H.
    + now f_equal; intuition.
    + inv H0.
      * eapply Value_cannot_start in H6; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
  - inv H.
    + inv H5.
      * eapply Value_cannot_start in H3; eauto; tauto.
      * eapply Value_cannot_start in H1; eauto; tauto.
    + now f_equal; intuition.
  - inv H; auto.
    + now inv H4.
    + eapply Value_cannot_start in H0; eauto; tauto.
  - inv H.
    + now inv H0.
    + now f_equal; intuition.
    + now inv H0.
  - inv H.
    + eapply Value_cannot_start in H5; eauto; tauto.
    + eapply Value_cannot_start in H0; eauto; tauto.
    + now f_equal; intuition.
Qed.

End Step.

Notation " t '--->' t' " := (Step t t') (at level 40).
