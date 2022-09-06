Require Import Category.Lib.
Require Import Category.Instance.Lambda.Lib.
Require Import Category.Instance.Lambda.Ltac.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Log.

Context {A : Type}.
Context `{L : HostExprs A}.
Context {Γ : Env}.

Variable P : ∀ {τ}, Exp Γ τ → Prop.

(** [ExpP] is a logical predicate that permits type-directed induction on
    expressions. *)
Equations ExpP `(e : Exp Γ τ) : Prop :=
  ExpP (τ:=_ ⟶ _) e := P e ∧ (∀ x, ExpP x → ExpP (APP e x));
  ExpP (τ:=_ × _) e := P e ∧ ExpP (Fst e) ∧ ExpP (Snd e);
  ExpP e := P e.

Inductive SubP : ∀ {Γ'}, Sub Γ Γ' → Prop :=
  | NoSubP : SubP (NoSub (Γ:=Γ))
  | PushP {Γ' τ} (e : Exp Γ τ) (s : Sub Γ Γ') :
    ExpP e → SubP s → SubP (Push e s).

Derive Signature for SubP.

Lemma ExpP_P {τ} {e : Γ ⊢ τ} : ExpP e → P e.
Proof. intros; induction τ; simpl in *; simp ExpP in H; now reduce. Qed.

Variable R : ∀ {τ}, Exp Γ τ → Exp Γ τ → Prop.

(** [ExpR] is a logical predicate that permits type-directed induction on
    expressions. *)
Equations ExpR {τ} (e1 e2 : Exp Γ τ) : Prop :=
  ExpR (τ:=_ ⟶ _) f1 f2 :=
    R f1 f2 ∧ (∀ x1 x2, ExpR x1 x2 → ExpR (APP f1 x1) (APP f1 x2));
  ExpR (τ:=_ × _) e1 e2 :=
    R e1 e2 ∧ ExpR (Fst e1) (Fst e2) ∧ ExpR (Snd e1) (Snd e2);
  ExpR e1 e2 := R e1 e2.

Lemma ExpR_R {τ} {e1 e2 : Γ ⊢ τ} : ExpR e1 e2 → R e1 e2.
Proof. intros; induction τ; simpl in *; simp ExpR in H; now reduce. Qed.

Inductive SubR : ∀ {Γ'}, Sub Γ Γ' → Prop :=
  | NoSubR : SubR (NoSub (Γ:=Γ))
  | PushR {Γ' τ} (e e' : Exp Γ τ) (s : Sub Γ Γ') :
    ExpR e e' → SubR s → SubR (Push e s).

Derive Signature for SubR.

End Log.
