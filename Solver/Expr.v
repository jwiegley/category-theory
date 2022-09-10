Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IListVec.
Require Import Category.Theory.Category.

Generalizable All Variables.
Set Transparent Obligations.

Import VectorNotations.

Derive Signature NoConfusion NoConfusionHom EqDec Subterm for Fin.t.

Definition obj_idx (n : nat) : Type := Fin.t n.
Definition obj_pair (n : nat) := obj_idx n * obj_idx n.

Definition dep_arr {C: Category} {n} (objs : Vector.t C n) '(dom, cod) :=
  objs[@dom] ~> objs[@cod].

Class Env := {
  cat      : Category;
  num_objs : nat;
  objs     : Vector.t cat num_objs;
  num_arrs : nat;
  tys      : Vector.t (obj_pair num_objs) num_arrs;
  arrs     : ilist (B:=dep_arr objs) tys
}.

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
