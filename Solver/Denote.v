From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.

Section Denote.

Context `{Arrows}.

Open Scope nat_scope.

Definition lookup_arr (f : nat) dom :
  option (∃ cod, objD dom ~> objD cod) :=
  let cod := snd (List.nth f tys (0, 0)) in
  match ith_exact f (dom, cod) arrs with
  | Some f => Some (cod; f)
  | _ => None
  end.

Fixpoint termD_work dom (e : Term) :
  option (∃ cod, objD dom ~> objD cod) :=
  match e with
  | Ident => Some (dom; id)
  | Morph a => lookup_arr a dom
  | Comp f g =>
    match termD_work dom g with
    | Some (mid; g) =>
      match termD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Import EqNotations.

Definition termD dom cod (e : Term) :
  option (objD dom ~> objD cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left H => Some (rew [fun y => _ ~> objD y] H in f)
    | _ => None
    end
  | _ => None
  end.

Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top      => True
  | Bottom   => False
  | And p q  => exprD p ∧ exprD q
  | Or p q   => exprD p + exprD q
  | Impl p q => exprD p → exprD q

  | Equiv d c f g =>
    match termD d c f, termD d c g with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  end.

End Denote.
