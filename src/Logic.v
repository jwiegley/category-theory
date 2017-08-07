Set Warnings "-notation-overridden".

Require Import Coq.omega.Omega.
Require Import Coq.FSets.FMapPositive.

Module Import MP := FMapPositive.
Module M := MP.PositiveMap.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Normal.
Require Import Solver.Denote.
Require Import Solver.Decide.
Require Import Solver.Subst.

Generalizable All Variables.

Section Logic.

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrmap : M.t (∃ x y, objs x ~{C}~> objs y).

Definition arrs (a : arr_idx) := M.find a arrmap.

Open Scope partial_scope.

Program Fixpoint expr_forward (t : Expr) (hyp : Expr)
        (cont : forall defs', [exprD objs arrmap (subst_all_expr t defs')]) :
  [exprD objs arrmap hyp -> exprD objs arrmap t] :=
  match hyp with
  | Top           => Reduce (cont nil)
  | Bottom        => Yes
  | Equiv x y f g => No         (* jww (2017-08-02): TODO *)
  (* | Not p         => No *)
  | And p q       => No         (* jww (2017-08-02): TODO *)
  | Or p q        => if expr_forward t p cont
                     then Reduce (expr_forward t q cont)
                     else No
  | Impl _ _      => Reduce (cont nil)
  end.
Next Obligation. contradiction. Defined.
Next Obligation. intuition. Defined.

Program Fixpoint expr_backward (t : Expr) {measure (expr_size t)} :
  [exprD objs arrmap t] :=
  match t with
  | Top => Yes
  | Bottom => No
  | Equiv x y f g => _
  (* | Not p         => *)
  (*   match expr_backward objs arrmap p with *)
  (*   | Proved _ _  => No *)
  (*   | Uncertain _ => Yes *)
  (*   end *)
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
    expr_forward q p (fun defs' => expr_backward (subst_all_expr q defs'))
  end.
Next Obligation.
  destruct (termD objs arrmap x y f) eqn:?; [|apply Uncertain].
  destruct (termD objs arrmap x y g) eqn:?; [|apply Uncertain].
  destruct (list_beq Eq_eqb (arrows f) (arrows g)) eqn:?; [|apply Uncertain].
  apply Proved.
  eapply arrows_decide; eauto.
Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation. abstract omega. Defined.
Next Obligation.
  simpl; rewrite expr_size_subst; omega.
Defined.

Definition expr_tauto : forall t, [exprD objs arrmap t].
Proof.
  intros; refine (Reduce (expr_backward t)); auto.
Defined.

Lemma expr_sound t :
  (if expr_tauto t then True else False) -> exprD objs arrmap t.
Proof.
  unfold expr_tauto; destruct t, (expr_backward _); tauto.
Qed.

End Logic.
