Require Import Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.

Generalizable All Variables.
Set Transparent Obligations.

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

Module DenoteExamples.

Import ListNotations.

Section DenoteExamples.

Context (C : Category).
Variables x y z w : C.
Variable f : z ~> w.
Variable g : y ~> z.
Variable h : x ~> y.
Variable i : x ~> z.

Open Scope nat_scope.

#[local] Instance sample_objects : Objects C := {|
  def_obj := y;
  objs    := [w; x; z; y; y];
|}.

#[local] Instance sample_arrows : Arrows C := {|
  arrs :=
    icons (2, 0) f
      (icons (1, 2) i
         (icons (1, 3) h
            (icons (3, 2) g
               (icons (3, 2) g
                  inil))))
|}.

Example termD_SIdent_Some :
  termD 0 0 Ident = Some id.
Proof. reflexivity. Qed.

End DenoteExamples.

End DenoteExamples.
