Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.
Require Import Category.Instance.Lambda.Sub.
Require Import Category.Instance.Lambda.Sem.
Require Import Category.Instance.Lambda.Log.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Small-step call-by-value reduction by congruence rules. *)

(* This module gives the structural (congruence-rule) presentation of the
   small-step operational semantics for the de Bruijn STLC (see [Exp]).  The
   relation [e ---> e'] reduces one redex; the next redex is located not by a
   reified evaluation context (that is the job of [Full], which factors the
   same relation through [Frame]/[Ctxt]/[Plug]) but by one congruence rule per
   elimination form that descends into the appropriate subterm:

     ST_Pair1   x ---> x'              ⟹  Pair x y ---> Pair x' y
     ST_Pair2   ValueP x,  y ---> y'   ⟹  Pair x y ---> Pair x y'
     ST_Fst1    p ---> p'              ⟹  Fst p ---> Fst p'
     ST_Snd1    p ---> p'              ⟹  Snd p ---> Snd p'
     ST_AppL    e1 ---> e1'            ⟹  APP e1 e2 ---> APP e1' e2
     ST_AppR    ValueP v1, e2 ---> e2' ⟹  APP v1 e2 ---> APP v1 e2'

   and one contraction rule per elimination form at the root:

     ST_FstPair ValueP v1, ValueP v2  ⟹  Fst (Pair v1 v2) ---> v1
     ST_SndPair ValueP v1, ValueP v2  ⟹  Snd (Pair v1 v2) ---> v2
     ST_Beta    ValueP v              ⟹  APP (LAM e) v ---> SubExp {|| v ||} e

   The relation is call-by-value, not full beta: ST_Beta fires only when the
   argument is a value, the projections only when both components are values,
   and the rules guarding a second subterm on a value of the first (ST_Pair2,
   ST_AppR) fix a left-to-right evaluation order.  Reduction never proceeds
   under a [LAM].  Because [Step] is indexed by [Exp Γ τ] on both sides,
   preservation (subject reduction) holds by construction: a step cannot
   change the context or the type, so there is no separate preservation lemma.

   The metatheory established here: [strong_progress] (a closed well-typed
   term is a value or steps), [Value_irreducible]/[Value_cannot_start]/
   [value_is_nf] (values are normal forms), the congruence lemmas
   [AppL_LAM]/[AppR_LAM], and [Step_deterministic] (reduction is a partial
   function).  Semantic soundness of [--->] is proved in [Sound] and strong
   normalization in [Norm].

   References:
     small-step / structural operational semantics
       https://en.wikipedia.org/wiki/Operational_semantics
     beta-reduction      https://ncatlab.org/nlab/show/beta-reduction
     lambda-calculus     https://ncatlab.org/nlab/show/lambda-calculus *)

Section Step.

Import ListNotations.

Open Scope Ty_scope.

Reserved Notation " t '--->' t' " (at level 40).

(* The single-step CBV reduction relation; intrinsically typed, so each step
   preserves the context [Γ] and type [τ] (preservation by construction). *)
Inductive Step : ∀ {Γ τ}, Exp Γ τ → Exp Γ τ → Set :=
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

(* Progress: a closed (well-typed) term is either a value or can take a step. *)
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

(* Values are irreducible (and the contrapositive [Value_cannot_start]): a
   value cannot be on the left of a step. *)
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

(* Congruence lemmas restating ST_AppL/ST_AppR with the bound names used by
   downstream developments ([Multi], [Norm]). *)
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

(* A term is in normal form for [R] when no [R]-step issues from it.  The
   commented variant ¬ ∃ t', R t t' is logically equivalent but the ∀/¬ form
   below is more convenient to apply pointwise. *)
Definition normal_form `(R : crelation X) (t : X) : Type :=
  ∀ t', ¬ R t t'.

Definition deterministic `(R : crelation X) : Type :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

(* Every value is a normal form (the [normal_form] packaging of irreducibility). *)
Lemma value_is_nf {Γ τ} (v : Exp Γ τ) :
  ValueP v → normal_form Step v.
Proof.
  repeat intro.
  dependent induction H0;
  now inv H.
Qed.

(* Determinism: the CBV strategy contracts a unique redex, so [--->] is a
   partial function.  Overlaps between congruence and contraction rules are
   ruled out via [Value_cannot_start] (a stepping subterm is not a value). *)
Theorem Step_deterministic Γ τ :
  deterministic (Step (Γ:=Γ) (τ:=τ)).
Proof.
  repeat intro.
  induction H0.
  - inv H.
    + now f_equal; intuition.
    + eapply Value_cannot_start in H5; eauto; tauto.
  - inv H.
    + eapply Value_cannot_start in H3; eauto; tauto.
    + now f_equal; intuition.
  - inv H.
    + now f_equal; intuition.
    + inv H0.
      * eapply Value_cannot_start in H6; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
  - inv H.
    + inv H3.
      * eapply Value_cannot_start in H1; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
    + now f_equal; intuition.
  - inv H.
    + now f_equal; intuition.
    + inv H0.
      * eapply Value_cannot_start in H6; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
  - inv H.
    + inv H3.
      * eapply Value_cannot_start in H1; eauto; tauto.
      * eapply Value_cannot_start in H7; eauto; tauto.
    + now f_equal; intuition.
  - inv H; auto.
    + now inv H3.
    + eapply Value_cannot_start in H7; eauto; tauto.
  - inv H.
    + now inv H0.
    + now f_equal; intuition.
    + now inv H0.
  - inv H.
    + eapply Value_cannot_start in H0; eauto; tauto.
    + eapply Value_cannot_start in H4; eauto; tauto.
    + now f_equal; intuition.
Qed.

End Step.

Notation " t '--->' t' " := (Step t t') (at level 40).
