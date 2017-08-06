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

Inductive Term : Set :=
  | Identity : Term
  | Morph (a : arr_idx) : Term
  | Compose (f : Term) (g : Term) : Term.

Function term_beq (f g : Term) : bool :=
  match f, g with
  | Identity, Identity => true
  | Morph a, Morph a' => Eq_eqb a a'
  | Compose f g, Compose f' g' => term_beq f f' &&& term_beq g g'
  | _, _ => false
  end.

Lemma term_beq_eq (f g : Term) :
  term_beq f g = true -> f = g.
Proof.
  generalize dependent g.
  induction f, g; simpl; intros;
  equalities; try discriminate; auto.
  f_equal; intuition.
Qed.

Fixpoint term_size (t : Term) : nat :=
  match t with
  | Identity    => 1%nat
  | Morph _     => 1%nat
  | Compose f g => 1%nat + term_size f + term_size g
  end.

Inductive Expr : Set :=
  | Top
  | Bottom
  | Equiv (x y : obj_idx) (f g : Term)
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr).

Fixpoint expr_size (t : Expr) : nat :=
  match t with
  | Top           => 1%nat
  | Bottom        => 1%nat
  | Equiv _ _ f g => 1%nat + term_size f + term_size g
  | And p q       => 1%nat + expr_size p + expr_size q
  | Or p q        => 1%nat + expr_size p + expr_size q
  | Impl p q      => 1%nat + expr_size p + expr_size q
  end.

Remark all_exprs_have_size e : (0 < expr_size e)%nat.
Proof. induction e; simpl; omega. Qed.

End Expr.
