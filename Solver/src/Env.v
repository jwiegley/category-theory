Set Warnings "-notation-overridden".

Require Export Coq.Bool.Bool.
Require Export Coq.Vectors.Vector.
Require Export Coq.PArith.PArith.
Require Export Coq.omega.Omega.

Require Export Category.Lib.
Require Export Category.Lib.Equality.
Require Export Category.Theory.Category.

Require Export Solver.IList.

Generalizable All Variables.

Definition obj_idx : Type := positive.
Definition arr_idx (n : nat) : Type := Fin.t n.

Definition obj_pair := obj_idx * obj_idx.
Definition dep_arr {C: Category}
           (objs : obj_idx -> C) (p : obj_pair) :=
  match p with (dom, cod) => objs dom ~> objs cod end.
Arguments dep_arr {C} objs p /.

Class Env := {
  cat : Category;
  objs : obj_idx -> cat;
  num_arrs : nat;
  tys : Vector.t (obj_idx * obj_idx) num_arrs;
  arrs : ilist (B:=dep_arr objs) tys
}.

Instance obj_idx_Equality : Equality obj_idx := {
  Eq_eqb         := Pos.eqb;
  Eq_eqb_refl    := Pos_eqb_refl;

  Eq_eqb_eq x y  := proj1 (Pos.eqb_eq x y);

  Eq_eq_dec      := Pos.eq_dec;
  Eq_eq_dec_refl := Pos_eq_dec_refl
}.

Program Instance arr_idx_Equality (n : nat) : Equality (arr_idx n) := {
  Eq_eqb         := Fin.eqb;
  Eq_eqb_refl    := Fin_eqb_refl n;

  Eq_eqb_eq x y  := proj1 (Fin_eqb_eq n x y);

  Eq_eq_dec      := Fin_eq_dec;
  Eq_eq_dec_refl := Fin_eq_dec_refl n
}.

Definition vec_size {A n} (l : Vector.t A n) : nat := n.
