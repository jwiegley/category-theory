Require Import Category.Lib.
Require Import Category.Instance.Lambda.Lib.
Require Import Category.Instance.Lambda.Ty.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Set Transparent Obligations.
Unset Uniform Inductive Parameters.

Section Exp.

Import ListNotations.

Open Scope Ty_scope.

Definition Env := list Ty.

Inductive Var : Env → Ty → Type :=
  | ZV {Γ τ}    : Var (τ :: Γ) τ
  | SV {Γ τ τ'} : Var Γ τ → Var (τ' :: Γ) τ.

Derive Signature NoConfusion EqDec for Var.

Inductive Exp Γ : Ty → Type :=
  | EUnit         : Exp Γ TyUnit

  | Pair {τ1 τ2}  : Exp Γ τ1 → Exp Γ τ2 → Exp Γ (TyPair τ1 τ2)
  | Fst {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ1
  | Snd {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ2

  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Derive Signature NoConfusionHom Subterm EqDec for Exp.

Fixpoint Exp_size {Γ τ} (e : Exp Γ τ) : nat :=
  match e with
  | EUnit _       => 1
  | Pair _ x y    => 1 + Exp_size x + Exp_size y
  | Fst _ p       => 1 + Exp_size p
  | Snd _ p       => 1 + Exp_size p
  | VAR _ v       => 1
  | LAM _ e       => 1 + Exp_size e
  | APP _ e1 e2   => 1 + Exp_size e1 + Exp_size e2
  end.

Corollary Exp_size_preserved {Γ τ} (e1 e2 : Exp Γ τ) :
  Exp_size e1 ≠ Exp_size e2 → e1 ≠ e2.
Proof. repeat intro; subst; contradiction. Qed.

End Exp.

Arguments EUnit {Γ}.
Arguments Pair {Γ τ1 τ2} _ _.
Arguments Fst {Γ τ1 τ2} _.
Arguments Snd {Γ τ1 τ2} _.
Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.

Notation "Γ ∋ τ" := (Var Γ τ) (at level 10).
Notation "Γ ⊢ τ" := (Exp Γ τ) (at level 10).
