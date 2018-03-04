Set Warnings "-notation-overridden".

Require Import Coq.PArith.PArith.
Require Import Coq.FSets.FMapPositive.

Module Import MP := FMapPositive.
Module M := MP.PositiveMap.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.

Generalizable All Variables.

Definition obj_idx := positive.
Definition arr_idx := positive.

Class Env := {
  cat : Category;
  objs : obj_idx -> cat;
  arrmap : M.t (∃ x y, objs x ~{cat}~> objs y);
  arrs (a : arr_idx) : option (∃ x y, objs x ~{cat}~> objs y) :=
    M.find a arrmap
}.
