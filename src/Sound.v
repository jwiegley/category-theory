Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Denote.
Require Import Solver.Normal.

Generalizable All Variables.

Section Normal.

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Theorem arrowsD_sound {p dom cod f} :
  arrowsD objs arrs dom cod (arrows p) = Some f ->
  ∃ f', f ≈ f' ∧ termD objs arrs dom cod p = Some f'.
Proof.
Admitted.

Lemma arrowsD_apply dom cod (f g : Term) :
  list_beq Eq_eqb (arrows f) (arrows g) = true ->
  arrowsD objs arrs dom cod (arrows f) ||| false = true ->
  arrowsD objs arrs dom cod (arrows f) = arrowsD objs arrs dom cod (arrows g) ->
  termD objs arrs dom cod f ≈ termD objs arrs dom cod g.
Proof.
  intros.
  destruct (arrowsD objs arrs dom cod (arrows f)) eqn:?; [|discriminate].
  destruct (arrowsD_sound Heqo), p.
  rewrite e0; clear e0.
  rewrite H1 in Heqo; clear H1.
Admitted.

Lemma exprAD_sound (e : Expr) : exprAD objs arrs e -> exprD objs arrs e.
Proof.
  destruct e; auto; intros.
  red in X; red.
  apply arrowsD_apply; auto.
Abort.

End Normal.
