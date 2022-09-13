Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.

Section Denote.

Context `{Arrows}.

Import ListNotations.

Open Scope nat_scope.

Definition helper {f} :
  (let '(dom, cod) := nth f tys (0, 0)
   in objD dom ~> objD cod)
    → objD (fst (nth f tys (0, 0))) ~>
      objD (snd (nth f tys (0, 0))).
Proof. destruct (nth f tys (0, 0)); auto. Defined.

Import EqNotations.

Program Definition lookup_arr (f : nat) dom :
  option (∃ cod, objD dom ~> objD cod) :=
  match eq_dec (fst (nth f tys (0, 0))) dom with
  | left H =>
      Some (snd (nth f tys (0, 0));
            rew [fun x => objD x ~> _] H in
              helper (ith f arrs _))
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

Definition termD dom cod (e : Term) :
  option (objD dom ~> objD cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left ecod =>
      Some (rew [fun y => objD dom ~> objD y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv d c f g =>
    match termD d c f, termD d c g with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p → exprD q
  end.

End Denote.
