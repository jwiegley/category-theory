Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Denote.
Require Import Solver.Normal.
Require Import Solver.Sound.

Generalizable All Variables.

Section Subst.

Definition subst_all_expr (x : Expr) (xs : list (Expr * Expr)) : Expr := x.

Lemma expr_size_subst q defs : expr_size (subst_all_expr q defs) = expr_size q.
Proof.
  reflexivity.
Qed.

Fixpoint substitute (from to arr : list arr_idx) : list arr_idx :=
  match arr with
  | nil => nil
  | cons x xs =>
    (fun len =>
       if list_beq Eq_eqb from (firstn len arr)
       then to ++ skipn len arr
       else x :: substitute from to xs) (length from)
  end.

Lemma substitute_idem f i : substitute f f i = i.
Proof.
  induction i; simpl; auto.
  destruct (list_beq _ _ _) eqn:?; [|now rewrite IHi].
  apply list_beq_eq in Heqb; [|apply BinPos.Pos.eqb_eq].
  rewrite Heqb at 1.
  now rewrite firstn_skipn.
Qed.

Local Obligation Tactic := program_simpl.

Polymorphic Program Instance Arr {C : Category} objs : Category := {
  obj := obj_idx;
  hom := fun dom cod => option (objs dom ~{C}~> objs cod);
  homset := fun _ _ => option_setoid;
  id := fun _ => Some id;
  compose := fun _ _ _ f g =>
               match f, g with
               | Some f, Some g => Some (f ∘ g)
               | _, _ => None
               end
}.
Next Obligation.
  proper.
  destruct x0, x1, y0, y1; auto.
  now rewrite X, X0.
Qed.
Next Obligation. destruct f; cat. Qed.
Next Obligation. destruct f; cat. Qed.
Next Obligation. destruct f, g, h; cat. Qed.
Next Obligation. destruct f, g, h; cat. Qed.

Lemma arrowsD_cons {C objs arrmap dom mid cod a a' f f'} :
  @arrs C objs arrmap a = Some (mid; (cod; a')) ->
  @arrowsD C objs arrmap dom mid f ≈ Some f' ->
  @arrowsD C objs arrmap dom cod (a :: f) ≈
  arrowsD objs arrmap mid cod [a] ∘[Arr objs] arrowsD objs arrmap dom mid f.
Proof.
  unfold arrowsD; simpl; intros.
  unfold arrs, Normal.arrs in *.
  rewrite H.
  destruct_arrows.
  destruct f.
    simpl in Heqo.
    inversion Heqo; subst.
    do 6 (equalities'; auto).
    repeat equalities; cat.
  do 6 (equalities'; auto).
  equalities.
  reflexivity.
Defined.

Lemma arrowsD_app {C objs arrmap dom mid cod f f' g g'} :
  @arrowsD C objs arrmap mid cod f = Some f' ->
  @arrowsD C objs arrmap dom mid g = Some g' ->
  @arrowsD C objs arrmap dom cod (f ++ g) ≈
  arrowsD objs arrmap mid cod f ∘[Arr objs] arrowsD objs arrmap dom mid g.
Proof.
  intros.
  unfold arrowsD in H, H0.
  do 2 destruct_arrows.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  destruct (@arrowsD_compose_r
              C objs arrmap f g dom mid cod f' g' Heqo0 Heqo), p.
  unfold arrowsD.
  rewrite e0.
  equalities.
  rewrite Heqo0.
  equalities.
  rewrite Heqo.
  equalities.
  cat.
Qed.

Lemma substitute_sound {C objs arrmap dom cod idom icod f f' g g' h i i'} :
  @arrowsD C objs arrmap idom icod f = Some f' ->
  @arrowsD C objs arrmap idom icod g = Some g' ->
  @arrowsD C objs arrmap idom icod f ≈ arrowsD objs arrmap idom icod g ->
  arrowsD objs arrmap dom cod i ≈ Some i' ->
  arrowsD objs arrmap dom cod (substitute h f i) ≈
  arrowsD objs arrmap dom cod (substitute h g i).
Proof.
  generalize dependent cod.
  induction i; intros.
    now simpl substitute.
  unfold substitute.
  destruct (list_beq _ _ _) eqn:?.
    assert (icod = cod).
      admit.
    subst.
    apply list_beq_eq in Heqb; [|apply Eq_eqb_eq].
    destruct (arrowsD objs arrmap dom idom (skipn (length h) (a :: i))) eqn:?.
      rewrite (arrowsD_app H Heqo).
      rewrite (arrowsD_app H0 Heqo).
      rewrite X.
      reflexivity.
    admit.
  fold substitute.
  replace (a :: i) with ([a] ++ i) in X0 by auto.
  unfold arrowsD in X0.
  destruct (arrowsD_work objs arrmap dom ([a] ++ i)) eqn:?; [|contradiction].
  destruct s.
  apply arrowsD_compose in Heqo.
  destruct (Eq_eq_dec x cod); [|contradiction]; simpl_eq; subst.
  red in X0.
  destruct Heqo, s, s, p, p.
  simpl in e0.
  destruct (Normal.arrs objs arrmap a) eqn:?; [|discriminate].
  destruct s, s.
  destruct (BinPos.Pos.eq_dec x2 x); [|discriminate]; simpl_eq; subst.
  pose proof (@arrowsD_cons).
Admitted.

Lemma rewrite_arrows {C objs arrmap dom cod idom icod f f' g g' i i' j} :
  @arrowsD C objs arrmap idom icod f = Some f' ->
  @arrowsD C objs arrmap idom icod g = Some g' ->
  arrowsD objs arrmap idom icod f ≈ arrowsD objs arrmap idom icod g ->
  arrowsD objs arrmap dom cod i ≈ Some i' ->
  arrowsD objs arrmap dom cod (substitute f g i) ≈ arrowsD objs arrmap dom cod j ->
  @arrowsD C objs arrmap dom cod i ≈ arrowsD objs arrmap dom cod j.
Proof.
  intros.
  erewrite (substitute_sound (g:=f) (i:=i)) in X1; eauto.
  - now rewrite substitute_idem in X1.
  - now symmetry.
Qed.

End Subst.
