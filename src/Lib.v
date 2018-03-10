Set Warnings "-notation-overridden".

Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Require Export Coq.PArith.PArith.
Require Export Coq.omega.Omega.

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Category.Lib.
Require Export Category.Lib.Equality.

Generalizable All Variables.

Instance positive_EqDec : EqDec.EqDec positive := {
  eq_dec := Eq_eq_dec
}.

Instance Equality_EqDec `{Equality A} : EqDec A := {
  eq_dec := Eq_eq_dec
}.

Program Instance option_EqDec `{EqDec A} : EqDec (option A).
Next Obligation.
  destruct x, y.
  - destruct (eq_dec a a0); subst.
      now left.
    right.
    intros.
    inversion H0.
    contradiction.
  - now right.
  - now right.
  - now left.
Defined.

Lemma option_map_Proper `{Setoid A} `{Setoid B} (f : A -> B) :
  Proper (equiv ==> equiv) f ->
  Proper (equiv ==> equiv) (option_map f).
Proof. proper; destruct x, y; simpl; auto. Defined.

(** Destruct in the hypothesis. *)

Ltac desh :=
  lazymatch goal with
  | [ H : match Pos.eq_dec ?n ?m with _ => _ end = _ |- _ ] =>
    destruct (Pos.eq_dec n m)
  | [ H : match Eq_eq_dec ?n ?m with _ => _ end = _ |- _ ] =>
    destruct (Eq_eq_dec n m)
  | [ H : match eq_dec ?n ?m with _ => _ end = _ |- _ ] =>
    destruct (eq_dec n m)
  | [ H : match ?t with _ => _ end = _ |- _ ] =>
    destruct t eqn:?
  | [ H : match ?t with _ => _ end _ _ = _ |- _ ] =>
    destruct t eqn:?
  | [ H : context[match Pos.eq_dec ?n ?m with _ => _ end] |- _ ] =>
    destruct (Pos.eq_dec n m)
  | [ H : context[match Eq_eq_dec ?n ?m with _ => _ end] |- _ ] =>
    destruct (Eq_eq_dec n m)
  | [ H : context[match eq_dec ?n ?m with _ => _ end] |- _ ] =>
    destruct (eq_dec n m)
  | [ H : context[match ?t with _ => _ end] |- _ ] =>
    destruct t eqn:?
  | [ H : context[match ?t with _ => _ end _ _] |- _ ] =>
    destruct t eqn:?
  end;
  repeat lazymatch goal with
  | [ H : Some _ = Some _ |- _ ] => inversion H; subst; try clear H
  | [ H : (?X; _) = (?X; _) |- _ ] =>
    try apply (Eqdep_dec.inj_pair2_eq_dec _ Eq_eq_dec) in H
  | [ H : { _ : _ & _ } |- _ ] =>
    let x := fresh "x" in
    let e := fresh "e" in
    destruct H as [x e]
  end;
  simpl; simplify; simpl_eq;
  try rewrite eq_dec_refl in *;
  try rewrite Eq_eq_dec_refl in *;
  try rewrite Pos_eq_dec_refl in *;
  subst;
  try (discriminate + contradiction).

(** Destruct in the goal. *)

Ltac desg :=
  lazymatch goal with
  | [ |- context[match Pos.eq_dec ?n ?m with _ => _ end = _] ] =>
    destruct (Pos.eq_dec n m)
  | [ |- context[match Eq_eq_dec ?n ?m with _ => _ end = _] ] =>
    destruct (Eq_eq_dec n m)
  | [ |- context[match eq_dec ?n ?m with _ => _ end = _] ] =>
    destruct (eq_dec n m)
  | [ |- context[match ?t with _ => _ end] ] =>
    destruct t eqn:?
  | [ |- context[match ?t with _ => _ end _ _] ] =>
    destruct t eqn:?
  end;
  repeat lazymatch goal with
  | [ H : { _ : _ & _ } |- _ ] =>
    let x := fresh "x" in
    let e := fresh "e" in
    destruct H as [x e]
  end;
  simpl; simplify; simpl_eq;
  try rewrite eq_dec_refl in *;
  try rewrite Eq_eq_dec_refl in *;
  try rewrite Pos_eq_dec_refl in *;
  subst;
  try (discriminate + contradiction).

Lemma app_eq_unit_type {A : Type} (x y : list A) (a : A) :
  (x ++ y)%list = [a]%list
    -> x = []%list ∧ y = [a]%list ∨ x = [a]%list ∧ y = []%list.
Proof.
  generalize dependent y.
  induction x; simpl; intuition idtac.
  inv H.
  rewrite H2.
  apply List.app_eq_nil in H2.
  destruct H2.
  now subst; right.
Qed.

Lemma list_equiv_eq `{Setoid A} (xs ys : list A) :
  (∀ x y, x ≈ y -> x = y) -> list_equiv xs ys -> xs = ys.
Proof.
  generalize dependent ys.
  induction xs; simpl; intros; desh; intuition auto.
  rewrite (H0 _ _ a1).
  f_equal.
  now apply IHxs.
Qed.
