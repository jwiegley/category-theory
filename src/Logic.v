Set Warnings "-notation-overridden".

Require Import Coq.omega.Omega.
Require Import Coq.FSets.FMapPositive.

Module Import MP := FMapPositive.
Module M := MP.PositiveMap.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Env.
Require Import Solver.Partial.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.
(* Require Import Solver.Normal.Subst. *)
Require Import Solver.Normal.Sound.

Generalizable All Variables.

Section Logic.

Context `{Env}.

Open Scope partial_scope.

Program Fixpoint expr_forward (t : Expr) (hyp : Expr)
        (cont : [exprD t (* (subst_all_expr t defs') *)]) :
  [exprD hyp -> exprD t] :=
  match hyp with
  | Top           => Reduce cont
  | Bottom        => Yes
  | Equiv x y f g => Reduce cont (* jww (2017-08-02): TODO *)
  | And p q       => Reduce cont (* jww (2017-08-02): TODO *)
  | Or p q        => if expr_forward t p cont
                     then Reduce (expr_forward t q cont)
                     else No
  | Impl _ _      => Reduce cont
  end.
Next Obligation. contradiction. Defined.
Next Obligation. intuition. Defined.

Program Fixpoint expr_backward (t : Expr) {measure (expr_size t)} :
  [exprD t] :=
  match t with
  | Top => Yes
  | Bottom => No
  | Equiv x y f g => _
  | And p q       =>
    match expr_backward p with
    | Proved _ _  => Reduce (expr_backward q)
    | Uncertain _ => No
    end
  | Or p q        =>
    match expr_backward p with
    | Proved _ _  => Yes
    | Uncertain _ => Reduce (expr_backward q)
    end
  | Impl p q      =>
    expr_forward q p (expr_backward q (* (subst_all_expr q defs') *))
  end.
Next Obligation.
  destruct (termD x y f) eqn:?; [|apply Uncertain].
  destruct (termD x y g) eqn:?; [|apply Uncertain].
  destruct (list_beq Eq_eqb (arrows f) (arrows g)) eqn:?; [|apply Uncertain].
  apply Proved.
  eapply arrows_decide; eauto.
Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. omega. Defined.

Definition expr_tauto : forall t, [exprD t].
Proof.
  intros; refine (Reduce (expr_backward t)); auto.
Defined.

Lemma expr_sound t :
  (if expr_tauto t then True else False) -> exprD t.
Proof.
  unfold expr_tauto; destruct t, (expr_backward _); tauto.
Qed.

End Logic.
