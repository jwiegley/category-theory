Set Warnings "-notation-overridden".


Require Import Coq.PArith.PArith.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
Require Import Category.Solver.Denote.

Generalizable All Variables.

Ltac desh :=
  repeat (
    repeat match goal with
    | [ H : match Pos_to_fin ?n with _ => _ end = _ |- _ ] =>
      destruct (Pos_to_fin n) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Pos_to_fin ?n with _ => _ end _ = _ |- _ ] =>
      destruct (Pos_to_fin n) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Pos_to_fin ?n with _ => _ end     |- _ ] =>
      destruct (Pos_to_fin n) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Pos_to_fin ?n with _ => _ end _   |- _ ] =>
      destruct (Pos_to_fin n) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Pos_to_fin ?n with _ => _ end _ _ |- _ ] =>
      destruct (Pos_to_fin n) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match @stermD_work ?h ?n ?s with _ => _ end = _ |- _ ] =>
      destruct (@stermD_work h n s) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match @stermD_work ?h ?n ?s with _ => _ end _ = _ |- _ ] =>
      destruct (@stermD_work h n s) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match @stermD_work ?h ?n ?s with _ => _ end     |- _ ] =>
      destruct (@stermD_work h n s) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match @stermD_work ?h ?n ?s with _ => _ end _   |- _ ] =>
      destruct (@stermD_work h n s) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match @stermD_work ?h ?n ?s with _ => _ end _ _ |- _ ] =>
      destruct (@stermD_work h n s) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end = _ |- _ ] =>
      destruct (Fin_eq_dec n m) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _ = _ |- _ ] =>
      destruct (Fin_eq_dec n m) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end     |- _ ] =>
      destruct (Fin_eq_dec n m) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _   |- _ ] =>
      destruct (Fin_eq_dec n m) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match Fin_eq_dec ?n ?m with _ => _ end _ _ |- _ ] =>
      destruct (Fin_eq_dec n m) eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match ?b with _ => _ end = _ |- _ ] =>
      destruct b eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match ?b with _ => _ end _ = _ |- _ ] =>
      destruct b eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match ?b with _ => _ end     |- _ ] =>
      destruct b eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match ?b with _ => _ end _   |- _ ] =>
      destruct b eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    | [ H : match ?b with _ => _ end _ _ |- _ ] =>
      destruct b eqn:?;
      try contradiction;
      try discriminate;
      let n := numgoals in guard n < 2
    end;
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
    end); auto; try solve [ cat ].
