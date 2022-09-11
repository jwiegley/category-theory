Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IListVec.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.
Set Transparent Obligations.

Import VectorNotations.

Derive Signature NoConfusion NoConfusionHom EqDec Subterm for Fin.t.

Definition obj_idx (n : nat) : Set := Fin.t (S n).

Inductive Obj (n : nat) : Set :=
  | Ob : obj_idx n → Obj n
  | Pair : Obj n → Obj n → Obj n.

Derive NoConfusion NoConfusionHom Subterm EqDec for Obj.

Arguments Ob {_} _.
Arguments Pair {_} _ _.

Definition obj_pair (n : nat) : Set := Obj n * Obj n.

Fixpoint objD {C: Category} `{@Cartesian C} {n}
  (x : Obj n) (objs : Vector.t C (S n)) :=
  match x with
  | Ob n => objs[@n]
  | Pair x y => objD x objs × objD y objs
  end.

Definition arrD {C: Category} `{@Cartesian C} {n}
  (objs : Vector.t C (S n)) '(dom, cod) :=
  objD dom objs ~> objD cod objs.

Class Env := {
  cat      : Category;
  cart     :> @Cartesian cat;
  num_objs : nat;
  (* Note that we one extra object here (doubling the last), just for the
     convenience of always knowing by the type that there must be one more
     than [num_objs] available. This saves us from having to maintain
     [num_objs] as the "size minus one". *)
  objs     : Vector.t cat (S num_objs);
  num_arrs : nat;
  tys      : Vector.t (obj_pair num_objs) (S num_arrs);

  arrs : ilist (B:=arrD objs) tys
}.

Inductive SObj : Set :=
  | SOb : positive → SObj
  | SPair : SObj → SObj → SObj.

Derive NoConfusion NoConfusionHom Subterm EqDec for positive SObj.

Inductive STerm : Set :=
  | SIdent : STerm
  | SMorph (a : positive) : STerm
  | SComp (f g : STerm) : STerm

  (* Cartesian structure *)
  | SFork (f g : STerm) : STerm
  | SExl : STerm
  | SExr : STerm.

Derive NoConfusion NoConfusionHom Subterm EqDec for STerm.

Inductive SExpr : Set :=
  | STop
  | SBottom
  | SEquiv (x y : SObj) (f g : STerm)
  | SAnd   (p q : SExpr)
  | SOr    (p q : SExpr)
  | SImpl  (p q : SExpr).

Derive NoConfusion NoConfusionHom Subterm for SExpr.
