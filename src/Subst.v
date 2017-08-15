Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.

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

Lemma substitute_app f i :
  incl f i
    -> ∃ l1 l2, ∀ g,
         substitute f g i = l1 ++ g ++ skipn (length f) l2
           ∧ ~ incl f l1
           ∧ f = firstn (length f) l2.
Proof.
Admitted.

Lemma substitute_not_incl f i : ~ incl f i -> ∀ g, substitute f g i = i.
Proof.
  intros.
  induction i; simpl; auto.
  destruct (list_beq _ _ _) eqn:?; [|rewrite IHi]; auto; clear IHi.
    apply list_beq_eq in Heqb; [|apply BinPos.Pos.eqb_eq].
    rewrite Heqb at 1.
    admit.
  intro.
  contradict H.
  right.
  now apply H0.
Admitted.

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

Lemma arrowsD_app_l {C objs arrmap dom mid cod f f' g g'} :
  arrowsD objs arrmap dom mid f = Some f' ->
  arrowsD objs arrmap dom mid g = Some g' ->
  arrowsD objs arrmap dom mid f ≈ arrowsD objs arrmap dom mid g ->
  ∀ x x', @arrowsD C objs arrmap mid cod x = Some x' ->
  arrowsD objs arrmap dom cod (x ++ f) ≈
  arrowsD objs arrmap dom cod (x ++ g).
Proof.
  intros.
  erewrite arrowsD_app; eauto.
  erewrite arrowsD_app; eauto.
  red.
  destruct (arrowsD objs arrmap mid cod x) eqn:?; [|discriminate].
  destruct (arrowsD objs arrmap dom mid f) eqn:?; [|discriminate].
  destruct (arrowsD objs arrmap dom mid g) eqn:?; [|discriminate].
  simpl.
  comp_left.
  now red in X.
Qed.

Lemma arrowsD_app_r {C objs arrmap dom mid cod f f' g g'} :
  arrowsD objs arrmap mid cod f = Some f' ->
  arrowsD objs arrmap mid cod g = Some g' ->
  arrowsD objs arrmap mid cod f ≈ arrowsD objs arrmap mid cod g ->
  ∀ x x', @arrowsD C objs arrmap dom mid x = Some x' ->
  arrowsD objs arrmap dom cod (f ++ x) ≈
  arrowsD objs arrmap dom cod (g ++ x).
Proof.
  intros.
  erewrite arrowsD_app; eauto.
  erewrite arrowsD_app; eauto.
  red.
  destruct (arrowsD objs arrmap dom mid x) eqn:?; [|discriminate].
  destruct (arrowsD objs arrmap mid cod f) eqn:?; [|discriminate].
  destruct (arrowsD objs arrmap mid cod g) eqn:?; [|discriminate].
  simpl.
  comp_right.
  now red in X.
Qed.

Lemma substitute_sound {C objs arrmap dom cod idom icod f f' g g' i i'} :
  @arrowsD C objs arrmap idom icod f = Some f' ->
  @arrowsD C objs arrmap idom icod g = Some g' ->
  @arrowsD C objs arrmap idom icod f ≈ arrowsD objs arrmap idom icod g ->
  arrowsD objs arrmap dom cod i ≈ Some i' ->
  arrowsD objs arrmap dom cod (substitute f g i) ≈ Some i'.
Proof.
  intros.
  destruct (incl_dec Eq_eq_dec f i).
    destruct (substitute_app f i i0), s.
    destruct (p g), p0; clear p.
    rewrite e.
    admit.
  now rewrite !(substitute_not_incl f _ n).
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
  rewrite X0, <- X1.
  symmetry.
  eapply substitute_sound; eauto.
Qed.

End Subst.
