Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Denote.
Require Import Solver.Normal.

Generalizable All Variables.

Section Decide.

Open Scope partial_scope.

Definition subst_all_expr (x : Expr) (xs : list (Expr * Expr)) : Expr := x.

Program Fixpoint expr_forward
        {C : Category}
        (objs : obj_idx -> C)
        (arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y))
        (t : Expr)
        (hyp : Expr)
        (cont : forall C objs' arrs' defs',
           [@expr_denote C objs' arrs' (subst_all_expr t defs')]) :
  [expr_denote objs arrs hyp -> expr_denote objs arrs t] :=
  match hyp with
  | Top           => Reduce (cont C objs arrs nil)
  | Bottom        => Yes
  | Equiv x y f g => No         (* jww (2017-08-02): TODO *)
  | Not p         => Reduce (cont C objs arrs nil)
  | And p q       => No         (* jww (2017-08-02): TODO *)
  | Or p q        => if expr_forward objs arrs t p cont
                     then Reduce (expr_forward objs arrs t q cont)
                     else No
  | Impl _ _      => Reduce (cont C objs arrs nil)
  end.
Next Obligation. contradiction. Defined.
Next Obligation. intuition. Defined.

Program Fixpoint expr_backward
        {C : Category}
        (objs : obj_idx -> C)
        (arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y))
        (t : Expr)
        {measure (expr_size t)} : [expr_denote objs arrs t] :=
  match t with
  | Top           => Yes
  | Bottom        => No
  | Equiv x y f g => match ArrowList_beq (normalize f) (normalize g) with
                     | true  => Yes
                     | false => No
                     end
  | Not p         => match expr_backward objs arrs p with
                     | Proved _ _  => No
                     | Uncertain _ => Yes
                     end
  | And p q       => match expr_backward objs arrs p with
                     | Proved _ _  => Reduce (expr_backward objs arrs q)
                     | Uncertain _ => No
                     end
  | Or p q        => match expr_backward objs arrs p with
                     | Proved _ _  => Yes
                     | Uncertain _ => Reduce (expr_backward objs arrs q)
                     end
  | Impl p q      => expr_forward objs arrs q p
                       (fun C objs' arrs' defs' =>
                          @expr_backward C objs' arrs' (subst_all_expr q defs') _)
  end.
Next Obligation.
  destruct f; simpl.
  destruct (term_denote _ _ f) eqn:?;
  destruct (term_denote _ _ g) eqn:?.
  destruct (term_denote _ _ _).
Admitted.
Next Obligation.
  induction p; simpl in *; auto.
Admitted.
Next Obligation.
  abstract omega.
Defined.

Theorem normalize_sound {p dom cod f} :
  Term_well_typed arrs dom cod p ->
  normalize_denote dom cod (normalize p) = Some f ->
  ∃ f', f ≈ f' ∧ denote dom cod p = Some f'.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; simpl in *; intros; equalities.
  - exists f; repeat equalities; reflexivity.
  - exists f.
    destruct (get_arr a); [|discriminate].
    repeat equalities; reflexivity.
  - apply normalize_compose in H0; equalities; subst.
    + destruct (Eq_eq_dec (ArrowList_dom arrs (normalize p1))
                          (TermCod arrs p2)).
      * rewrite <- e in *.
        destruct (IHp1 _ _ _ H1 a2), (IHp2 _ _ _ H2 b0).
        equalities.
        rewrite e3, e1.
        eexists; intuition.
        now rewrite <- e0, <- e2.
      * pose proof (ArrowList_normalize_dom_cod_sound arrs H2);
        equalities.
        now rewrite a1 in H3.
    + clear IHp1 IHp2.
      pose proof (ArrowList_normalize_dom_cod_sound arrs H1).
      pose proof (ArrowList_normalize_dom_cod_sound arrs H2).
      equalities.
      now rewrite H3.
Qed.

Theorem normalize_sound_r {p dom cod f} :
  Term_well_typed arrs dom cod p ->
  denote dom cod p = Some f ->
  ∃ f', f ≈ f' ∧ normalize_denote dom cod (normalize p) = Some f'.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; simpl in *; intros; equalities.
  - exists f; repeat equalities; reflexivity.
  - exists f.
    destruct (get_arr a); [|discriminate].
    repeat equalities; reflexivity.
  - destruct (denote (TermCod arrs p2) cod p1) eqn:?; [|discriminate].
    destruct (denote dom (TermCod arrs p2) p2) eqn:?; [|discriminate].
    destruct (IHp1 _ _ _ H1 Heqo), p; clear IHp1.
    destruct (IHp2 _ _ _ H2 Heqo0), p; clear IHp2.
    exists (x ∘ x0).
    split.
      inversion_clear H0; cat.
    admit.
Admitted.

Theorem denote_normalize {p dom cod} :
  (* Term_well_typed_bool arrs dom cod p = true -> *)
  denote dom cod p ≈ normalize_denote dom cod (normalize p).
Proof.
  destruct (denote dom cod p) eqn:?.
    destruct (normalize_denote dom cod (normalize p)) eqn:?.
      apply normalize_sound in Heqo0.
        destruct Heqo0.
        equalities.
        red.
        rewrite e0 in Heqo.
        rewrite e.
        now inversion_clear Heqo.
      now apply denote_well_typed in Heqo.
    admit.
  
  generalize dependent cod.
  generalize dependent dom.
  induction p as [o|a|]; intros.
  - repeat equalities; reflexivity.
  - simpl in *.
    destruct (get_arr a); auto.
    destruct s, s.
    simpl_eq.
    destruct p, p, e, e0.
    repeat destruct (Pos.eq_dec _ _); auto.
    destruct e, e0; cat.
  - simpl normalize.
    simpl denote.
    specialize (IHp1 (TermCod arrs p2) cod).
    specialize (IHp2 dom (TermCod arrs p2)).
    repeat destruct (denote _ _ _); symmetry.
Admitted.

Theorem normalize_apply dom cod : ∀ f g,
  Term_well_typed_bool arrs dom cod f = true ->
  Term_well_typed_bool arrs dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  denote dom cod f ≈ denote dom cod g.
Proof.
  intros.
  apply Term_well_typed_bool_sound in H.
  apply Term_well_typed_bool_sound in H0.
  pose proof (ArrowList_well_typed_sound arrs H).
  apply (ArrowList_beq_eq arrs) in H1.
  destruct (normalize_denote dom cod (normalize f)) eqn:?; try discriminate.
  destruct (normalize_sound H Heqo), p.
  rewrite e0; clear e0.
  rewrite H1 in Heqo; clear H1.
  destruct (normalize_sound H0 Heqo), p.
  rewrite e1; clear e1.
  red.
  rewrite <- e, <- e0.
  reflexivity.
Qed.

Corollary normalize_denote_terms dom cod : ∀ f g,
  Term_well_typed_bool arrs dom cod f = true ->
  Term_well_typed_bool arrs dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  normalize_denote dom cod (normalize f)
    ≈ normalize_denote dom cod (normalize g) ->
  denote dom cod f ≈ denote dom cod g.
Proof. intros; apply normalize_apply; auto. Qed.

Corollary normalize_denote_terms_impl dom cod : ∀ f g,
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f)
    ≈ normalize_denote dom cod (normalize g).
Proof.
  intros.
  apply (ArrowList_beq_eq arrs) in H.
  now rewrite H.
Qed.

Definition expr_tauto : forall env t, [expr_denote env t].
Proof.
  intros; refine (Reduce (expr_backward (andImpl t) env)); auto.
  assert (H : True \/ True \/ True \/ True \/ True) by admit.
  inversion H; limit 0.
Defined.

Lemma expr_sound env t :
  (if expr_tauto env t then True else False) -> expr_denote env t.
Proof.
  unfold expr_tauto; destruct t, (expr_backward _ env); tauto.
Qed.

End Decide.
