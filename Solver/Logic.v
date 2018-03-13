Set Warnings "-notation-overridden".

Require Export Category.Solver.Normal.
Require Import Category.Solver.Partial.

Generalizable All Variables.

Section Logic.

Context `{Env}.

Open Scope partial_scope.

Program Fixpoint expr_forward (t : Expr) (hyp : Expr) (cont : [exprD t]) :
  [exprD hyp -> exprD t] :=
  match hyp with
  | Top           => Reduce cont
  | Bottom        => Yes
  | Equiv x y f g => Reduce cont
  | And p q       => Reduce cont
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
    expr_forward q p (expr_backward q)
  end.
Next Obligation.
  destruct (Arrows_eq_dec (arrows f) (arrows g)) eqn:?; [|apply Uncertain].
  apply Proved.
  rewrite <- unarrows_arrows.
  symmetry.
  now rewrite <- unarrows_arrows, e.
Defined.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. intuition. Defined.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. intuition. Defined.

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
