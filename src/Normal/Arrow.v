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
Require Import Solver.Normal.TList.

Generalizable All Variables.

Function arrows (t : Term) : list arr_idx :=
  match t with
  | Identity    => nil
  | Morph a     => [a]
  | Compose f g => arrows f ++ arrows g
  end.

Definition unarrows (fs : list arr_idx) : Term :=
  fold_right (fun f rest => Compose (Morph f) rest) Identity fs.

Section NormalArrow.

Context `{Env}.

Record Arrow (dom cod : obj_idx) : Type := {
  arr : arr_idx;
  mor : objs dom ~> objs cod;
  present : arrs arr = Some (dom; (cod; mor))
}.

(* With arrows, the types flow in the reverse direction *)
Definition ArrowList (dom cod : obj_idx) : Type :=
  tlist (fun i j => Arrow j i) cod dom.

End NormalArrow.

Arguments arr {H dom cod} _.
Arguments mor {H dom cod} _.
Arguments present {H dom cod} _.
