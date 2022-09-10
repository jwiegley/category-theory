Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Instance.Lambda.Ty.
Require Import Category.Instance.Lambda.Exp.
Require Import Category.Instance.Lambda.Value.
Require Import Category.Instance.Lambda.Ren.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Set Transparent Obligations.

Section Eval.

Import ListNotations.

Inductive Closed : Ty → Type :=
  | Closure {Γ τ} : Exp Γ τ → ClEnv Γ → Closed τ

with ClEnv : Env → Type :=
  | NoCl : ClEnv []
  | AddCl {Γ τ} : Value τ → ClEnv Γ → ClEnv (τ :: Γ)

with Value : Ty → Type :=
  | Val {Γ τ} (x : Exp Γ τ) : ValueP x → ClEnv Γ → Value τ.

Derive Signature NoConfusion NoConfusionHom Subterm for ClEnv Closed Value.

Equations get_val `(s : ClEnv Γ) `(v : Var Γ τ) : Value τ :=
  get_val (AddCl x _)  ZV     := x;
  get_val (AddCl _ xs) (SV v) := get_val xs v.

Equations combine `(c1 : ClEnv Γ) `(c2 : ClEnv Γ') : ClEnv (Γ ++ Γ') :=
  combine NoCl         c2 := c2;
  combine (AddCl c c1) c2 := AddCl c (combine c1 c2).

Fixpoint snoc {a : Type} (x : a) (xs : list a) : list a :=
  match xs with
  | [] => [x]
  | x :: xs => x :: snoc x xs
  end.

Inductive EvalContext : Ty → Ty → Type :=
  | MT {τ} : EvalContext τ τ
  | AR {dom cod τ} :
    Closed dom → EvalContext cod τ → EvalContext (dom ⟶ cod) τ
  | FN {dom cod τ} :
    Value (dom ⟶ cod) → EvalContext cod τ → EvalContext dom τ
  | PAIR_FST {τ1 τ2 τ} : Closed τ1 → EvalContext (τ1 × τ2) τ → EvalContext τ2 τ
  | PAIR_SND {τ1 τ2 τ} : Closed τ2 → EvalContext (τ1 × τ2) τ → EvalContext τ1 τ
  | FST {τ1 τ2 τ} : EvalContext τ1 τ → EvalContext (τ1 × τ2) τ
  | SND {τ1 τ2 τ} : EvalContext τ2 τ → EvalContext (τ1 × τ2) τ.

Derive Signature NoConfusion NoConfusionHom Subterm for EvalContext.

Inductive Σ : Ty → Type :=
  | MkΣ {u    : Ty}
        (exp  : Closed u)
        {τ    : Ty}
        (knt  : EvalContext u τ) : Σ τ.

Derive Signature NoConfusion NoConfusionHom Subterm for Σ.

Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  (* Constants *)
  step (MkΣ (Closure EUnit _) (FN f κ)) with f := {
    | Val (LAM e) _ ρ' := MkΣ (Closure e (AddCl (Val EUnit UnitP NoCl) ρ')) κ;
  };

  step (MkΣ (Closure (Fst p) ρ) κ) := MkΣ (Closure p ρ) (FST κ);
  step (MkΣ (Closure (Snd p) ρ) κ) := MkΣ (Closure p ρ) (SND κ);

  step (MkΣ (Closure (Pair x y) ρ) (FST κ)) := MkΣ (Closure x ρ) κ;
  step (MkΣ (Closure (Pair x y) ρ) (SND κ)) := MkΣ (Closure y ρ) κ;

  step (MkΣ (Closure (Pair x y) ρ) κ) :=
    MkΣ (Closure x ρ) (PAIR_SND (Closure y ρ) κ);
  step (MkΣ x (PAIR_SND y κ)) := MkΣ y (PAIR_FST x κ);
  step (MkΣ (Closure y ρ) (PAIR_FST (Closure x ρ') κ)) :=
    MkΣ (Closure (Pair (liftL _ x) (liftR _ y)) (combine ρ' ρ)) κ;

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (Closure (VAR v) ρ) κ) with get_val ρ v := {
    | Val val _ ρ' := MkΣ (Closure val ρ') κ
  };

  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (Closure (LAM e) ρ) (AR a κ)) :=
    MkΣ a (FN (Val (LAM e) (LambdaP _) ρ) κ);
  step (MkΣ (Closure (LAM e) ρ) (FN (Val (LAM f) _ ρ') κ)) :=
    MkΣ (Closure f (AddCl (Val (LAM e) (LambdaP _) ρ) ρ')) κ;

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (Closure (APP f x) ρ) κ) :=
    MkΣ (Closure f ρ) (AR (Closure x ρ) κ);

  step (MkΣ c MT) := MkΣ c MT.

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop O s := s;
  loop (S gas') s := loop gas' (step s).

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ (Closure e NoCl) MT.

Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ τ := loop gas (inject e).

(*
Theorem cek_sound τ (e e' : Exp [] τ) :
  e --->* e' → ∃ gas, loop gas (inject e) = inject e'.
Proof.
  intros.
  apply all_exprs_complete in H.
  induction τ.
  exact (IHτ1 e e' H).
Qed.
*)

End Eval.
