Set Warnings "-notation-overridden".

Require Import Coq.PArith.PArith.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
Require Import Category.Solver.Denote.

Generalizable All Variables.

Ltac desh :=
  repeat (
    repeat lazymatch goal with
    | [ H : match Pos_to_fin ?n with _ => _ end = _ |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match Pos_to_fin ?n with _ => _ end _ = _ |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match Pos_to_fin ?n with _ => _ end     |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match Pos_to_fin ?n with _ => _ end _   |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match Pos_to_fin ?n with _ => _ end _ _ |- _ ] => destruct (Pos_to_fin n) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end = _ |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end _ = _ |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end     |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end _   |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match stermD_work ?n ?s with _ => _ end _ _ |- _ ] => destruct (stermD_work n s) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end = _ |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _ = _ |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end     |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _   |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _ _ |- _ ] => destruct (Fin_eq_dec n m) eqn:?
    | [ H : match ?b with _ => _ end = _ |- _ ] => destruct b eqn:?
    | [ H : match ?b with _ => _ end _ = _ |- _ ] => destruct b eqn:?
    | [ H : match ?b with _ => _ end     |- _ ] => destruct b eqn:?
    | [ H : match ?b with _ => _ end _   |- _ ] => destruct b eqn:?
    | [ H : match ?b with _ => _ end _ _ |- _ ] => destruct b eqn:?
    end;
    try contradiction;
    try discriminate;
    let n := numgoals in guard n < 2;
    simpl_eq;
    try rewrite Fin_eq_dec_refl in *;
    try rewrite Pos_eq_dec_refl in *;
    repeat lazymatch goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; subst; try clear H
    | [ H : (?X; _) = (?X; _) |- _ ] =>
      apply Eqdep_dec.inj_pair2_eq_dec in H;
             [|solve [ apply Fin_eq_dec
                     | apply Pos.eq_dec ]]; subst
    | [ H : ∃ _, _ |- _ ] =>
      let x := fresh "x" in
      let e := fresh "e" in
      destruct H as [x e]
    | [ H : _ ∧ _ |- _ ] =>
      let x := fresh "x" in
      let e := fresh "e" in
      destruct H as [x e]
    end); auto; try solve cat.
