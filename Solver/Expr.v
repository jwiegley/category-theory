Set Warnings "-notation-overridden".

Require Import Coq.PArith.PArith.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Solver.Env.

Generalizable All Variables.

(** Transform a 0-based [Fin.t] into a 1-based [positive]. *)
Fixpoint Fin_to_pos {n} (f : Fin.t n) : positive :=
  match f with
  | Fin.F1 => 1%positive
  | Fin.FS x => Pos.succ (Fin_to_pos x)
  end.

Definition Pos_to_fin {n} (p : positive) : option (Fin.t n).
Proof.
  generalize dependent n.
  induction p using Pos.peano_rect; intros.
    destruct n.
      exact None.
    exact (Some Fin.F1).
  destruct n.
    exact None.
  destruct (IHp n).
    exact (Some (Fin.FS t)).
  exact None.
Defined.

(** Weakly-typed terms, only correct in certain environments. *)

Inductive STerm : Set :=
  | SIdent : STerm
  | SMorph (a : positive) : STerm
  | SComp (f : STerm) (g : STerm) : STerm.

Derive NoConfusion NoConfusionHom Subterm EqDec for positive STerm.

Inductive SExpr : Set :=
  | STop
  | SBottom
  | SEquiv (x y : positive) (f g : STerm)
  | SAnd   (p q : SExpr)
  | SOr    (p q : SExpr)
  | SImpl  (p q : SExpr).

Derive NoConfusion NoConfusionHom Subterm for SExpr.
