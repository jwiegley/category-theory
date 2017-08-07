Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Expr.

Generalizable All Variables.

Section Denote.

Context {C : Category}.

Variable objs : obj_idx -> C.
(* jww (2017-08-06): Use FMapPositive for arrs, rather than this function *)
Variable arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Import EqNotations.

Fixpoint termD_work dom (e : Term) : option (∃ cod, objs dom ~{C}~> objs cod) :=
  match e with
  | Identity => Some (dom; @id _ (objs dom))
  | Morph a =>
    match arrs a with
    | Some (x; (y; f)) =>
      match Eq_eq_dec x dom with
      | left edom =>
        Some (y; rew [fun x => objs x  ~{ C }~> objs y] edom in f)
      | _ => None
      end
    | _ => None
    end
  | Compose f g =>
    match termD_work dom g with
    | Some (mid; g) =>
      match termD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition termD dom cod (e : Term) : option (objs dom ~{C}~> objs cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | left ecod =>
        Some (rew [fun y => objs dom ~{ C }~> objs y] ecod in f)
    | right _ => None
    end
  | _ => None
  end.

Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => termD x y f ≈ termD x y g
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

End Denote.
