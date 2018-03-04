Set Warnings "-notation-overridden".

Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Category.
(* Require Import Solver.Normal.Sound. *)

Generalizable All Variables.

Section Subst.

Context `{Env}.

Definition substitute dom cod (arr : ValidArrowEx dom cod)
           i j (from to : ValidArrowEx i j) :
  ValidArrowEx dom cod.
Proof.
Abort.
(*
  generalize dependent cod.
  induction 1; intros.
    destruct (getArrList from).
      destruct (Eq_eq_dec i dom); subst.
        destruct (Eq_eq_dec j dom); subst.
          exact to.
        exact f.
      exact f.
    exact f.
  destruct (Eq_eq_dec j cod); subst.
    pose (length (getArrList from)) as len.
    destruct (arr_break len h), s, s.
    destruct (list_beq Eq_eqb (getArrList x1)
                       (getArrList from)).
      destruct (Eq_eq_dec x0 i); subst.
        exact (to ∘[Valid objs arrmap] x2).
      exact (f ∘[Valid objs arrmap] IHarr).
    exact (f ∘[Valid objs arrmap] IHarr).
  exact (f ∘[Valid objs arrmap] IHarr).
Defined.
*)

(*
Definition subst_all_expr (x : Expr) (xs : list (Expr * Expr)) : Expr := x.

Lemma expr_size_subst q defs : expr_size (subst_all_expr q defs) = expr_size q.
Proof.
  reflexivity.
Qed.

Definition prefix {A} (Aeqb : A -> A -> bool) (xs ys : list A) : bool :=
  list_beq Aeqb xs (firstn (length xs) ys).

Function infix {A} (Aeqb : A -> A -> bool) (xs ys : list A) : option nat :=
  match ys with
  | nil =>
    match xs with
    | nil => Some 0%nat
    | cons _ _ => None
    end
  | cons y ys =>
    if prefix Aeqb xs (y :: ys)
    then Some 0%nat
    else match infix Aeqb xs ys with
         | Some n => Some (S n)
         | None => None
         end
  end.

Function substitute (from to arr : list arr_idx) : list arr_idx :=
  match arr with
  | nil =>
    match from with
    | nil => to
    | cons _ _ => arr
    end
  | cons x xs =>
    (fun len =>
       if list_beq Eq_eqb from (firstn len arr)
       then to ++ skipn len arr
       else x :: substitute from to xs) (length from)
  end.
*)

(*
Program Instance substitute_respects :
  Proper
    (forall_relation
       (fun dom =>
          forall_relation
            (fun cod =>
               @equiv _ (ValidArrow_Setoid dom cod) ==>
               (forall_relation
                  (fun i =>
                     forall_relation
                       (fun j =>
                          @equiv _ (ValidArrow_Setoid i j) ==>
                          @equiv _ (ValidArrow_Setoid i j) ==>
                          equiv)%signature)))%signature))
         substitute.
Next Obligation.
  proper.
Admitted.

Lemma substitute_idem dom cod (f : ValidArrow dom cod)
      i j (g : ValidArrow i j) :
  substitute dom cod f i j g g ≈ f.
Proof.
  induction f using @arr_rect; simpl; auto.
    destruct f; auto.
  destruct (list_beq _ _ _) eqn:?; [|now rewrite IHi].
  apply list_beq_eq in Heqb; [|apply BinPos.Pos.eqb_eq].
  rewrite Heqb at 1.
  now rewrite firstn_skipn.
Qed.

Lemma substitute_incl f i n : infix Eq_eqb f i = Some n ->
  ∀ g, substitute f g i = firstn n i ++ g ++ skipn (n + length f) i.
Proof.
  intros.
  generalize dependent n.
  generalize dependent g.
  induction i; simpl; intros; auto.
    destruct f; simpl; auto.
      admit.
    simpl in H.
    discriminate.
  destruct (list_beq _ _ _) eqn:?.
    admit.
  unfold arr_idx in *.
  destruct (prefix BinPos.Pos.eqb f (a :: i)) eqn:?.
    inversion_clear H; simpl in *.
    simpl in *.
Admitted.

Lemma substitute_not_incl f i : infix Eq_eqb f i = None ->
  ∀ g, substitute f g i = i.
Proof.
  intros.
  induction i; simpl; auto.
(*
  destruct (list_beq _ _ _) eqn:?; [|rewrite IHi]; auto; clear IHi.
    apply list_beq_eq in Heqb; [|apply BinPos.Pos.eqb_eq].
    elimtype False.
    rewrite Heqb in H; clear Heqb.
    contradict H.
    clear g.
    remember (a :: i) as l.
    remember (length f) as n.
    clear Heql a i Heqn f.
    generalize dependent l.
    induction n; simpl; intros.
      repeat intro.
      inversion H.
    destruct l.
      simpl in H.
      discriminate.
    apply incl_cons; auto.
      left; auto.
    apply incl_tl; auto.
  intro.
  contradict H.
  right.
  now apply H0.
Qed.
*)
Admitted.

Local Obligation Tactic := program_simpl.

Polymorphic Program Instance Arr {C : Category} objs : Category := {
  obj     := obj_idx;
  hom     := fun dom cod => option (objs dom ~{C}~> objs cod);
  homset  := fun _ _ => option_setoid;
  id      := fun _ => Some id;
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

Lemma arrowsD_cons {C dom mid cod a a' f f'} :
  arrs a = Some (mid; (cod; a')) ->
  arrowsD dom mid f ≈ Some f' ->
  arrowsD dom cod (a :: f) ≈
  @arrowsD C mid cod [a] ∘[Arr objs] arrowsD dom mid f.
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

Lemma arrowsD_app {C dom mid cod f f' g g'} :
  arrowsD mid cod f = Some f' ->
  arrowsD dom mid g = Some g' ->
  @arrowsD C dom cod (f ++ g)
    ≈ arrowsD mid cod f ∘[Arr objs] arrowsD dom mid g.
Proof.
  intros.
  unfold arrowsD in H, H0.
  do 2 destruct_arrows.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  destruct (@arrowsD_compose_r C f g dom mid cod f' g'
                               Heqo0 Heqo), p.
  unfold arrowsD.
  rewrite e0; equalities.
  rewrite Heqo0; equalities.
  rewrite Heqo; equalities; cat.
Qed.

Lemma arrowsD_app_l {C dom mid cod f f' g g'} :
  arrowsD dom mid f = Some f' ->
  arrowsD dom mid g = Some g' ->
  arrowsD dom mid f ≈ arrowsD dom mid g ->
  ∀ x x', @arrowsD C mid cod x = Some x' ->
  arrowsD dom cod (x ++ f) ≈
  arrowsD dom cod (x ++ g).
Proof.
  intros.
  erewrite arrowsD_app; eauto.
  erewrite arrowsD_app; eauto.
  red.
  destruct (arrowsD mid cod x) eqn:?; [|discriminate].
  destruct (arrowsD dom mid f) eqn:?; [|discriminate].
  destruct (arrowsD dom mid g) eqn:?; [|discriminate].
  simpl.
  comp_left.
  now red in X.
Qed.

Lemma arrowsD_app_r {C dom mid cod f f' g g'} :
  arrowsD mid cod f = Some f' ->
  arrowsD mid cod g = Some g' ->
  arrowsD mid cod f ≈ arrowsD mid cod g ->
  ∀ x x', @arrowsD C dom mid x = Some x' ->
  arrowsD dom cod (f ++ x) ≈ arrowsD dom cod (g ++ x).
Proof.
  intros.
  erewrite arrowsD_app; eauto.
  erewrite arrowsD_app; eauto.
  red.
  destruct (arrowsD dom mid x) eqn:?; [|discriminate].
  destruct (arrowsD mid cod f) eqn:?; [|discriminate].
  destruct (arrowsD mid cod g) eqn:?; [|discriminate].
  simpl.
  comp_right.
  now red in X.
Qed.

Lemma substitute_sound {C dom cod idom icod f f' g g' i i'} :
  arrowsD idom icod f = Some f' ->
  arrowsD idom icod g = Some g' ->
  arrowsD idom icod f ≈ arrowsD idom icod g ->
  arrowsD dom cod i = Some i' ->
  @arrowsD C dom cod (substitute f g i) ≈ Some i'.
Proof.
  intros.
  destruct (infix Eq_eqb f i) eqn:?.
    rewrite (substitute_incl f _ n Heqo).
    admit.
  rewrite !(substitute_not_incl f _ Heqo).
  rewrite H1.
  reflexivity.
Admitted.

Lemma rewrite_arrows {C dom cod idom icod} :
  ∀ f g (af : ValidArrow idom icod f)
        (ag : ValidArrow idom icod g), (f; af) ≈ (g; ag) ->
  ∀ i j (ai : ValidArrow dom cod i)
        (aj : ValidArrow dom cod j),
  arrowsD dom cod (substitute f g i) ≈ arrowsD dom cod j ->
  @arrowsD C dom cod i ≈ arrowsD dom cod j.
Proof.
  intros.
  rewrite H1.
  rewrite H2 in X0 |- *.
  rewrite <- X0.
  symmetry.
  eapply substitute_sound; eauto.
  simpl.
  now rewrite H, H0.
Qed.
*)

End Subst.
