Set Warnings "-notation-overridden".

Require Import Category.Lib.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Denote.
Require Import Solver.Normal.

Generalizable All Variables.

Section Subst.

Definition subst_all_expr (x : Expr) (xs : list (Expr * Expr)) : Expr := x.

Lemma expr_size_subst q defs : expr_size (subst_all_expr q defs) = expr_size q.
Proof.
  reflexivity.
Qed.

End Subst.
