Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.

Generalizable All Variables.

Section Denote.

Context `{Env}.

Import VectorNotations.

Corollary helper {f} :
  (let '(dom, cod) := tys[@f] in objs[@dom] ~> objs[@cod])
    -> objs[@(fst (tys[@f]))] ~> objs[@(snd (tys[@f]))].
Proof. destruct (tys[@f]); auto. Defined.

Import EqNotations.

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

Definition pos_obj (f : positive) dom : option (∃ cod, objs[@dom] ~> objs[@cod]) :=
  match Pos_to_fin f with
  | Some f =>
    match eq_dec (fst (tys[@f])) dom with
    | left H =>
      Some (snd (tys[@f]);
            rew [fun x => objs[@x] ~> _] H in helper (ith arrs f))
    | _ => None
    end
  | _ => None
  end.

Fixpoint stermD_work dom (e : STerm) :
  option (∃ cod, objs[@dom] ~> objs[@cod]) :=
  match e with
  | SIdent => Some (dom; @id _ (objs[@dom]))
  | SMorph a => pos_obj a dom
  | SComp f g =>
    match stermD_work dom g with
    | Some (mid; g) =>
      match stermD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition stermD dom cod (e : STerm) : option (objs[@dom] ~> objs[@cod]) :=
  match stermD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left ecod =>
      Some (rew [fun y => objs[@dom] ~> objs[@y]] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Program Fixpoint sexprD (e : SExpr) : Type :=
  match e with
  | STop           => True
  | SBottom        => False
  | SEquiv x y f g =>
    match Pos_to_fin x, Pos_to_fin y with
    | Some d, Some c =>
      match stermD d c f, stermD d c g with
      | Some f, Some g => f ≈ g
      | _, _ => False
      end
    | _, _ => False
    end
  | SAnd p q       => sexprD p ∧ sexprD q
  | SOr p q        => sexprD p + sexprD q
  | SImpl p q      => sexprD p → sexprD q
  end.

End Denote.
