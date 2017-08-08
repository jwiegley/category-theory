Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.

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

Fixpoint substitute (from to arr : list arr_idx) : list arr_idx :=
  match arr with
  | nil => nil
  | cons x xs =>
    if list_beq Eq_eqb from (firstn (length from) arr)
    then to ++ skipn (length from) arr
    else x :: substitute from to xs
  end.

Lemma rewrite_arrows {C objs arrmap dom cod idom icod f g i j} :
  arrowsD objs arrmap idom icod f ≈ arrowsD objs arrmap idom icod g ->
  arrowsD objs arrmap dom cod (substitute f g i) ≈ arrowsD objs arrmap dom cod j ->
  @arrowsD C objs arrmap dom cod i ≈ arrowsD objs arrmap dom cod j.
Proof.
  unfold arrowsD; intros.
  generalize dependent j.
  generalize dependent cod.
  induction i; simpl; intros; auto.
Admitted.

End Subst.
