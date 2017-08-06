Set Warnings "-notation-overridden".

Require Import Coq.omega.Omega.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Normal.
Require Import Solver.Denote.
Require Import Solver.Decide.

Generalizable All Variables.

Section Logic.

Open Scope partial_scope.

Definition subst_all_expr (x : Expr) (xs : list (Expr * Expr)) : Expr := x.

Lemma expr_size_subst q defs : expr_size (subst_all_expr q defs) = expr_size q.
Proof.
  reflexivity.
Qed.

Program Fixpoint expr_forward
        {C : Category}
        (objs : obj_idx -> C)
        (arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y))
        (t : Expr)
        (hyp : Expr)
        (cont : forall C objs' arrs' defs',
           [@exprD C objs' arrs' (subst_all_expr t defs')]) :
  [exprD objs arrs hyp -> exprD objs arrs t] :=
  match hyp with
  | Top           => Reduce (cont C objs arrs nil)
  | Bottom        => Yes
  | Equiv x y f g => No         (* jww (2017-08-02): TODO *)
  (* | Not p         => No *)
  | And p q       => No         (* jww (2017-08-02): TODO *)
  | Or p q        => if expr_forward objs arrs t p cont
                     then Reduce (expr_forward objs arrs t q cont)
                     else No
  | Impl _ _      => Reduce (cont C objs arrs nil)
  end.
Next Obligation. contradiction. Defined.
Next Obligation. intuition. Defined.

Program Fixpoint expr_backward
        {C : Category}
        (objs : obj_idx -> C)
        (arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y))
        (t : Expr)
        {measure (expr_size t)} : [exprD objs arrs t] :=
  match t with
  | Top => Yes
  | Bottom => No
  | Equiv x y f g => _
  (* | Not p         => *)
  (*   match expr_backward objs arrs p with *)
  (*   | Proved _ _  => No *)
  (*   | Uncertain _ => Yes *)
  (*   end *)
  | And p q       =>
    match expr_backward objs arrs p with
    | Proved _ _  => Reduce (expr_backward objs arrs q)
    | Uncertain _ => No
    end
  | Or p q        =>
    match expr_backward objs arrs p with
    | Proved _ _  => Yes
    | Uncertain _ => Reduce (expr_backward objs arrs q)
    end
  | Impl p q      =>
    expr_forward objs arrs q p
                 (fun C objs' arrs' defs' =>
                    @expr_backward C objs' arrs' (subst_all_expr q defs') _)
  end.
Next Obligation.
  destruct (termD objs arrs x y f) eqn:?; [|apply Uncertain].
  destruct (termD objs arrs x y g) eqn:?; [|apply Uncertain].
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

Definition expr_tauto : forall C objs arrs t, [@exprD C objs arrs t].
Proof.
  intros; refine (Reduce (expr_backward objs arrs t)); auto.
Defined.

Lemma expr_sound C objs arrs t :
  (if expr_tauto C objs arrs t then True else False) -> exprD objs arrs t.
Proof.
  unfold expr_tauto; destruct t, (expr_backward objs arrs _); tauto.
Qed.

End Logic.
