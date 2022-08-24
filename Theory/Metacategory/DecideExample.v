Set Warnings "-notation-overridden".

Require Import Coq.PArith.PArith.
Require Import Coq.NArith.NArith.

Require Import Category.Lib.
Require Import Category.Lib.MapDecide.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Metacategory.ArrowsOnly.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Open Scope N_scope.

Example formula_backward_example (x y z w : N) :
  if formula_backward
       (Impl (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty))
             (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty)))
       {| vars := fun p =>
           if (p =? 1)%positive then x else
           if (p =? 2)%positive then y else
           if (p =? 3)%positive then z else
           if (p =? 4)%positive then w else 9%N |}
  then True else False.
Proof. vm_compute; constructor. Qed.

Example map_decide_test  x y f :
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))) ->
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))).
Proof. solve_map. Qed.

Example problem3 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 3 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
(*
  destruct_maps; try nomega. (* takes 1.68s *)
  Undo.
*)
  map_decide.                (* takes 0.016s *)
Qed.

Example problem4 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 4 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. (* takes 30.15s *) *)
  (* Undo. *)
  map_decide.                (* takes 0.035s *)
Qed.

Example problem5 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 5 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. (* takes 2501s *) *)
  (* Undo. *)
  map_decide.                (* takes 0.085s *)
Qed.

Example problem100 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 10 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. *)
  (* Undo. *)
  map_decide.                (* takes 2.445s *)
Qed.
