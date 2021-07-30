Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Coq.Vectors.Vector.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.

Require Import Equations.Equations.
Require Import Equations.EqDec.

Generalizable All Variables.

Import VectorNotations.

Derive Signature EqDec for Fin.t.
Next Obligation. now apply Fin_eq_dec. Defined.

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

Instance obj_idx_Equality (n : nat) : Equality (obj_idx n) := {
  Eq_eqb         := Fin.eqb;
  Eq_eqb_refl    := Fin_eqb_refl n;

  Eq_eqb_eq x y  := proj1 (Fin_eqb_eq n x y);

  Eq_eq_dec      := Fin_eq_dec;
  Eq_eq_dec_refl := Fin_eq_dec_refl n
}.

Instance arr_idx_Equality (n : nat) : Equality (arr_idx n) := {
  Eq_eqb         := Fin.eqb;
  Eq_eqb_refl    := Fin_eqb_refl n;

  Eq_eqb_eq x y  := proj1 (Fin_eqb_eq n x y);

  Eq_eq_dec      := Fin_eq_dec;
  Eq_eq_dec_refl := Fin_eq_dec_refl n
}.
