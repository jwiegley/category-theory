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

Definition obj_idx (n : nat) : Set := Fin.t n.

Inductive Obj (n : nat) : Set :=
  | Ob : obj_idx n → Obj n
  | Pair : Obj n → Obj n → Obj n.

Derive NoConfusion NoConfusionHom Subterm EqDec for Obj.

Arguments Ob {_} _.
Arguments Pair {_} _ _.

Definition obj_pair (n : nat) : Set := Obj n * Obj n.

Class Env := {
  cat      : Category;
  cart     :> @Cartesian cat;
  num_objs : nat;
  objs     : Vector.t cat num_objs;
  num_arrs : nat;
  tys      : Vector.t (obj_pair num_objs) num_arrs;

  objD (x : Obj num_objs) :=
    let fix go x :=
      match x with
      | Ob x => objs[@x]
      | Pair x y => go x × go y
      end in go x;

  arrD '(dom, cod) := objD dom ~> objD cod;

  arrs : ilist (B:=arrD) tys
}.

Inductive STerm : Set :=
  | SIdent : STerm
  | SMorph (a : positive) : STerm
  | SComp (f g : STerm) : STerm

  (* Cartesian structure *)
  | SFork (f g : STerm) : STerm
  | SExl : STerm
  | SExr : STerm.

Derive NoConfusion NoConfusionHom Subterm EqDec for positive STerm.

Inductive SObj : Set :=
  | SOb : positive → SObj
  | SPair : SObj → SObj → SObj.

Derive NoConfusion NoConfusionHom Subterm EqDec for SObj.

Inductive SExpr : Set :=
  | STop
  | SBottom
  | SEquiv (x y : SObj) (f g : STerm)
  | SAnd   (p q : SExpr)
  | SOr    (p q : SExpr)
  | SImpl  (p q : SExpr).

Derive NoConfusion NoConfusionHom Subterm for SExpr.
