Set Warnings "-notation-overridden".

Require Export Coq.Bool.Bool.
Require Export Coq.Vectors.Vector.
Require Export Coq.PArith.PArith.
Require Export Coq.omega.Omega.

Require Export Category.Lib.
Require Export Category.Lib.Equality.
Require Export Category.Lib.IList.
Require Export Category.Theory.Category.

Generalizable All Variables.

Import VectorNotations.

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
