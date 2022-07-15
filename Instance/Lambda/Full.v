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

Section Full.

Import ListNotations.

Open Scope Ty_scope.

(* A context defines a hole which, after substitution, yields an expression of
   the index type. *)
Inductive Frame Γ : Ty → Ty → Type :=
  | F_PairL {τ1 τ2}  : Exp Γ τ2 → Frame Γ τ1 (τ1 × τ2)
  | F_PairR {τ1 τ2}  : Exp Γ τ1 → Frame Γ τ2 (τ1 × τ2)
  | F_Fst {τ1 τ2}    : Frame Γ (τ1 × τ2) τ1
  | F_Snd {τ1 τ2}    : Frame Γ (τ1 × τ2) τ2
  | F_AppL {dom cod} : Exp Γ dom → Frame Γ (dom ⟶ cod) cod
  | F_AppR {dom cod} : Exp Γ (dom ⟶ cod) → Frame Γ dom cod.

Derive Signature NoConfusion Subterm for Frame.

Inductive Ctxt Γ : Ty → Ty → Type :=
  | C_Nil {τ}         : Ctxt Γ τ τ
  | C_Cons {τ τ' τ''} : Frame Γ τ' τ → Ctxt Γ τ'' τ' → Ctxt Γ τ'' τ.

Derive Signature NoConfusion NoConfusionHom Subterm for Ctxt.

(* [Ctxt] forms a category with objects = types and morphisms = contexts. *)

Definition Ctxt_id {Γ τ} : Ctxt Γ τ τ := C_Nil _.
Arguments Ctxt_id {_ _} /.

Program Fixpoint Ctxt_comp {Γ τ τ' τ''}
        (C : Ctxt Γ τ' τ) (C' : Ctxt Γ τ'' τ') : Ctxt Γ τ'' τ :=
  match C with
  | C_Nil _      => C'
  | C_Cons _ f c => C_Cons _ f (Ctxt_comp c C')
  end.

Theorem Ctxt_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} :
  Ctxt_comp Ctxt_id C = C.
Proof. induction C; simpl; auto; now f_equal. Qed.

Theorem Ctxt_id_right {Γ τ τ'} {C : Ctxt Γ τ' τ} :
  Ctxt_comp C Ctxt_id = C.
Proof. induction C; simpl; auto; now f_equal. Qed.

Theorem Ctxt_comp_assoc {Γ τ τ' τ'' τ'''}
        {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'} {C'' : Ctxt Γ τ''' τ''} :
  Ctxt_comp C (Ctxt_comp C' C'') = Ctxt_comp (Ctxt_comp C C') C''.
Proof. induction C; simpl; auto; now f_equal. Qed.

Inductive Redex {Γ} : ∀ {τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | R_Beta {dom cod} (e : Exp (dom :: Γ) cod) v :
    ValueP v →
    Redex (APP (LAM e) v) (SubExp {|| v ||} e)
  | R_Fst {τ1 τ2} (x : Exp Γ τ1) (y : Exp Γ τ2) :
    ValueP x →
    ValueP y →
    Redex (Fst (Pair x y)) x
  | R_Snd {τ1 τ2} (x : Exp Γ τ1) (y : Exp Γ τ2) :
    ValueP x →
    ValueP y →
    Redex (Snd (Pair x y)) y.

Derive Signature for Redex.

Unset Elimination Schemes.

Inductive Plug {Γ τ'} (e : Exp Γ τ') : ∀ {τ}, Ctxt Γ τ' τ → Exp Γ τ → Prop :=
  | Plug_Hole : Plug e (C_Nil _) e

  | Plug_PairL {τ1 τ2} {C : Ctxt Γ τ' τ1} {e' : Exp Γ τ1} {e2 : Exp Γ τ2} :
    Plug e C e' →
    Plug e (C_Cons _ (F_PairL _ e2) C) (Pair e' e2)

  | Plug_PairR {τ1 τ2} {C : Ctxt Γ τ' τ2} {e1 : Exp Γ τ1} {e' : Exp Γ τ2} :
    ValueP e1 →
    Plug e C e' →
    Plug e (C_Cons _ (F_PairR _ e1) C) (Pair e1 e')

  | Plug_Fst {τ1 τ2} {C : Ctxt Γ τ' (τ1 × τ2)} {e' : Exp Γ (τ1 × τ2)} :
    Plug e C e' →
    Plug e (C_Cons _ (F_Fst _) C) (Fst e')

  | Plug_Snd {τ1 τ2} {C : Ctxt Γ τ' (τ1 × τ2)} {e' : Exp Γ (τ1 × τ2)} :
    Plug e C e' →
    Plug e (C_Cons _ (F_Snd _) C) (Snd e')

  | Plug_AppL {dom cod} {C : Ctxt Γ τ' (dom ⟶ cod)}
              {e' : Exp Γ (dom ⟶ cod)} {e2 : Exp Γ dom} :
    Plug e C e' →
    Plug e (C_Cons _ (F_AppL _ e2) C) (APP e' e2)

  | Plug_AppR {dom cod} {C : Ctxt Γ τ' dom}
              {e' : Exp Γ dom} {e1 : Exp Γ (dom ⟶ cod)} :
    ValueP e1 →
    Plug e C e' →
    Plug e (C_Cons _ (F_AppR _ e1) C) (APP e1 e').

Derive Signature for Plug.

Set Elimination Schemes.

Scheme Plug_ind := Induction for Plug Sort Prop.

(* [Plug] forms a category with objects = expressions and morphisms = plugs
   over existential contexts. *)

Definition Plug_id {Γ τ} {x : Exp Γ τ} : Plug x (C_Nil Γ) x := Plug_Hole _.
Arguments Plug_id {_ _ _} /.

Fixpoint Plug_comp {Γ τ τ' τ''}
         {x : Exp Γ τ''} {y : Exp Γ τ'} {z : Exp Γ τ}
         {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'}
         (P : Plug x C' y) (P' : Plug y C z) :
  Plug x (Ctxt_comp C C') z :=
  match P' with
  | Plug_Hole _       => P
  | Plug_PairL _ p'   => Plug_PairL _ (Plug_comp P p')
  | Plug_PairR _ V p' => Plug_PairR _ V (Plug_comp P p')
  | Plug_Fst _ p'     => Plug_Fst _ (Plug_comp P p')
  | Plug_Snd _ p'     => Plug_Snd _ (Plug_comp P p')
  | Plug_AppL _ p'    => Plug_AppL _ (Plug_comp P p')
  | Plug_AppR _ V p'  => Plug_AppR _ V (Plug_comp P p')
  end.

(*
(* This should be provable, but the dependent types get in the way. *)
Theorem Plug_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} {x : Exp Γ τ'} {y : Exp Γ τ}
        (P : Plug x C y) :
  Plug_comp Plug_id P ~= P.
*)

Reserved Notation " t '--->' t' " (at level 40).

Inductive Step {Γ τ} : Exp Γ τ → Exp Γ τ → Prop :=
  | StepRule {τ'} {C : Ctxt Γ τ' τ} {e1 e2 : Exp Γ τ'} {e1' e2' : Exp Γ τ} :
    Plug e1 C e1' →
    Plug e2 C e2' →
    Redex e1 e2 →
    e1' ---> e2'

  where " t '--->' t' " := (Step t t').

Derive Signature for Step.

#[local] Hint Constructors ValueP Plug Redex Step : core.

#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e; reduce.
  - now left; constructor.
  - destruct IHe1 as [V1|[e1' H1']];
    destruct IHe2 as [V2|[e2' H2']].
    + now left; constructor.
    + dependent elimination H2'; now eauto 6.
    + dependent elimination H1'; now eauto 6.
    + dependent elimination H1';
      dependent elimination H2'; now eauto 6.
  - destruct IHe as [V|[e' H']].
    + dependent elimination V;  now eauto 6.
    + dependent elimination H'; now eauto 6.
  - destruct IHe as [V|[e' H']].
    + dependent elimination V;  now eauto 6.
    + dependent elimination H'; now eauto 6.
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

(*
Lemma Plug_deterministic {Γ τ} e2 :
  ∀ τ' (C : Ctxt Γ τ' τ) e1 e1',
    Redex e1 e1' → Plug e1 C e2 →
  ∀ τ'' (C' : Ctxt Γ τ'' τ) f1 f1',
    Redex f1 f1' → Plug f1 C' e2 →
    τ' = τ'' ∧ C ~= C' ∧ e1 ~= f1.
*)

Lemma Plug_functional {Γ τ τ'} {C : Ctxt Γ τ' τ} e :
  ∀ e1, Plug e C e1 → ∀ e2, Plug e C e2 → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
Qed.

Lemma Plug_injective {Γ τ τ'} {C : Ctxt Γ τ' τ} e :
  ∀ e1, Plug e1 C e → ∀ e2, Plug e2 C e → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
  - dependent destruction H.
    now f_equal; auto.
Qed.

Lemma Redex_deterministic {Γ τ} {e : Exp Γ τ} :
  ∀ e', Redex e e' → ∀ e'', Redex e e'' → e' = e''.
Proof.
  intros.
  dependent induction H0;
  dependent elimination H; eauto.
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

Definition normal_form `(R : relation X) (t : X) : Prop :=
  ∀ t', ¬ R t t'.

Definition deterministic `(R : relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

(*
Lemma value_is_nf {Γ τ} (v : Exp Γ τ) :
  ValueP v → normal_form Step v.
*)

End Full.

Notation " t '--->' t' " := (Step t t') (at level 40).
