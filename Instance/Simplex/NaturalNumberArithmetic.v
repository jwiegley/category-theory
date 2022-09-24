Require Import ssreflect.
Require Import ssrfun.
Require Import ssrbool.
Require Import mathcomp.ssreflect.fintype.
Require Import mathcomp.ssreflect.finfun.
Require Import mathcomp.ssreflect.ssrnat.

Global Create HintDb arith discriminated.
Global Hint Resolve leq_trans : arith. 
Global Hint Resolve ltn_ord : arith.
Global Hint Resolve leq_addr : arith.
(* This can cause infinite looping so it's better not to add it? *)
(* Global Hint Resolve ltnW : arith. *)
Global Hint Resolve leq_addr : arith.
Global Hint Resolve leq_addl : arith.

Proposition nltm_nltmk : forall n m k: nat, n <= m -> n <= m + k.
Proof.
  intros n m k ineq.
  apply: (@leq_trans m n (m + k)); [ exact: ineq | exact: leq_addr ].
Qed.

Proposition nltk_nltmk : forall n m k: nat, n <= k -> n <= m + k.
Proof.
  intros n m k ineq.
  apply (@leq_trans k n (m + k)); auto with arith.
Qed.


Global Hint Resolve nltm_nltmk : arith.
Global Hint Resolve nltk_nltmk : arith.
Global Hint Resolve addn0 : arith.
Global Hint Resolve addnA : arith.
Global Hint Unfold addn : arith.
Global Hint Rewrite leq_add2l : arith.
Global Hint Rewrite -> addn0 : arith.
Global Hint Rewrite -> add0n : arith.
