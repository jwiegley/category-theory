Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section ilist.

Context {A : Type}.

Variable B : A → Type.

Fixpoint ilist (l : list A) : Type :=
  match l with
  | []      => unit
  | x :: xs => B x * ilist xs
  end.

Equations iapp `(xs : ilist l) `(ys : ilist l') : ilist (l ++ l') :=
  iapp (l:=[]) tt ys := ys;
  iapp (x, xs) ys := (x, iapp xs ys).

Equations isplit `(xs : ilist (l ++ l')) : ilist l * ilist l'  :=
  isplit (l:=[]) xs := (tt, xs);
  isplit (x, xs) with isplit xs := {
    | (xs', ys) => ((x, xs'), ys)
  }.

End ilist.
