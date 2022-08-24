Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IListVec.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Solver.Expr.

Generalizable All Variables.

Section Denote.

Context `{Env}.

Import VectorNotations.

Definition helper {f} :
  (let '(dom, cod) := tys[@f] in objD dom ~> objD cod)
    → objD (fst (tys[@f])) ~> objD (snd (tys[@f])).
Proof. destruct (tys[@f]); auto. Defined.

Import EqNotations.

Definition Pos_to_fin {n} (p : positive) : option (Fin.t n).
Proof.
  generalize dependent n.
  induction p using Pos.peano_rect; intros.
  - destruct n.
    + exact None.
    + exact (Some Fin.F1).
  - destruct n.
    + exact None.
    + destruct (IHp n).
      * exact (Some (Fin.FS t)).
      * exact None.
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

Fixpoint sobjD (x : SObj) : option (Obj num_objs) :=
  match x with
  | SOb x =>
    match Pos_to_fin x with
    | Some x' => Some (Ob x')
    | None => None
    end
  | SPair x y =>
      match sobjD x, sobjD y with
      | Some x', Some y' => Some (Pair x' y')
      | _, _ => None
      end
  end.

Fixpoint stermD_work dom (e : STerm) :
  option (∃ cod, objD dom ~> objD cod) :=
  match e with
  | SIdent => Some (dom; id)
  | SMorph a => pos_obj a dom
  | SFork f g => Some (dom; id)
  | SExl =>
      match dom with
      | Pair x y => Some (x; exl)
      | _ => None
      end
  | SExr =>
      match dom with
      | Pair x y => Some (y; exr)
      | _ => None
      end
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

Definition stermD dom cod (e : STerm) : option (objD dom ~> objD cod) :=
  match stermD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left ecod =>
      Some (rew [fun y => objD dom ~> objD y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Fixpoint sexprD (e : SExpr) : Type :=
  match e with
  | STop           => True
  | SBottom        => False
  | SEquiv x y f g =>
    match sobjD x, sobjD y with
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
