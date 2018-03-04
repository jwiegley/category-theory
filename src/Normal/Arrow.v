Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.
Require Import Coq.FSets.FMapPositive.

Module Import MP := FMapPositive.
Module M := MP.PositiveMap.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.

Generalizable All Variables.

Function arrows (t : Term) : list arr_idx :=
  match t with
  | Identity    => nil
  | Morph a     => [a]
  | Compose f g => arrows f ++ arrows g
  end.

Definition unarrows (fs : list arr_idx) : Term :=
  fold_left (fun acc => Compose acc \o Morph) fs Identity.
