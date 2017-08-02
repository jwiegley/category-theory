Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.

Generalizable All Variables.

Section Expr.

Definition obj_idx := positive.
Definition arr_idx := positive.

(* This describes the morphisms of a magmoid, which forms a quotient category
   under denotation. *)
Inductive Term : obj_idx -> obj_idx-> Set :=
  | Identity      (o : obj_idx) : Term o o
  | Morph    x y  (a : arr_idx) : Term x y
  | Compose x y z (f : Term y z) (g : Term x y) : Term x z.

Definition TermDom `(e : Term a b) : obj_idx := a.
Definition TermCod `(e : Term a b) : obj_idx := b.

Inductive Expr : Set :=
  | Top    : Expr
  | Bottom : Expr
  | Equiv  : ∀ a b, Term a b -> Term a b -> Expr
  | Not    : Expr -> Expr
  | And    : Expr -> Expr -> Expr
  | Or     : Expr -> Expr -> Expr
  | Impl   : Expr -> Expr -> Expr.

End Expr.

Arguments Identity o.
Arguments Morph {_ _} a.
Arguments Compose {_ _ _} f g.
