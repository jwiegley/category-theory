Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.

Import VectorNotations.

Derive Signature NoConfusion NoConfusionHom EqDec Subterm for Fin.t.

Definition obj_idx (n : nat) : Type := Fin.t n.
Definition arr_idx (n : nat) : Type := Fin.t n.

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
