Set Warnings "-notation-overridden".

Require Import Category.Lib.TList.
Require Import Category.Lib.Tactics.
Require Import Category.Solver.Partial.
Require Import Category.Solver.SDenote.
Require Import Category.Solver.Arrows.

Generalizable All Variables.

Section Logic.

Context `{Env}.

Open Scope partial_scope.

Import EqNotations.

Fixpoint indices `(t : Arrows tys d c) : list (arr_idx num_arrs) :=
  match t with
  | tnil => List.nil
  | existT2 _ _ f _ _ ::: fs => f :: indices fs
  end.

Theorem indices_impl {d c} (x y : Arrows tys d c) :
  indices x = indices y -> x = y.
Proof.
  induction x; dependent elimination y;
  simpl; auto; intros.
  - destruct y0.
    inv H0.
  - destruct b.
    inv H0.
  - destruct b, y0.
    inv H0.
    f_equal; auto.
    f_equal; auto.
    apply eq_proofs_unicity.
Qed.

Theorem indices_app d m c (t1 : Arrows tys m c) (t2 : Arrows tys d m) :
  indices (t1 +++ t2) = (indices t1 ++ indices t2)%list.
Proof.
  induction t1; simpl in *; cat.
  destruct b; subst.
  destruct t2; simpl; cat.
    now rewrite List.app_nil_r.
  f_equal.
  apply IHt1.
Qed.

Fixpoint term_indices `(t : Term tys d c) : list (arr_idx num_arrs) :=
  match t with
  | Ident => []
  | Morph a => [a]
  | Comp f g => term_indices f ++ term_indices g
  end.

Theorem term_indices_consistent {d c} (x : Arrows tys d c) :
  term_indices (unarrows x) = indices x.
Proof.
  induction x; simpl; auto.
  destruct b; subst; simpl_eq; simpl.
  now rewrite IHx.
Qed.

Theorem term_indices_unarrows {d c} (x : Term tys d c) :
  term_indices (unarrows (arrows x)) = term_indices x.
Proof.
  induction x; simpl; auto.
  rewrite <- IHx1, <- IHx2; clear IHx1 IHx2.
  rewrite !term_indices_consistent.
  now rewrite indices_app.
Qed.

Theorem term_indices_equiv {d c} (x y : Term tys d c) :
  term_indices x = term_indices y -> termD x ≈ termD y.
Proof.
  intros.
  rewrite <- term_indices_unarrows in H0.
  symmetry in H0.
  rewrite <- term_indices_unarrows in H0.
  rewrite !term_indices_consistent in H0.
  rewrite <- unarrows_arrows.
  symmetry.
  rewrite <- unarrows_arrows.
  apply indices_impl in H0.
  now rewrite H0.
Qed.

Program Fixpoint sexpr_forward (t : SExpr positive) (hyp : SExpr positive)
        (cont : [sexprD t]) :
  [sexprD hyp -> sexprD t] :=
  match hyp with
  | STop           => Reduce cont
  | SBottom        => Yes
  | SEquiv x y f g => Reduce cont
  | SAnd p q       => Reduce cont
  | SOr p q        => if sexpr_forward t p cont
                      then Reduce (sexpr_forward t q cont)
                      else No
  | SImpl _ _      => Reduce cont
  end.
Next Obligation. contradiction. Defined.
Next Obligation. intuition. Defined.

Fixpoint Fin_to_pos {n} (f : Fin.t n) : positive :=
  match f with
  | Fin.F1 => 1%positive
  | Fin.FS x => Pos.succ (Fin_to_pos x)
  end.

Lemma Fin_to_pos_inj {n} (x y : Fin.t n) :
  Fin_to_pos x = Fin_to_pos y -> x = y.
Proof.
  destruct n.
    inversion x.
  generalize dependent y.
  induction x; intros;
  dependent elimination y; simpl in *; intros; auto.
  - destruct (Fin_to_pos y); inv H0.
  - destruct (Fin_to_pos x); inv H0.
  - f_equal.
    apply Pos.succ_inj in H0.
    apply IHx; auto.
Qed.

Ltac simpl_eq :=
  unfold eq_rect_r, eq_rect, eq_ind_r, eq_ind, eq_sym, prod_rect,
         EqdepFacts.internal_eq_rew_r_dep,
         EqdepFacts.internal_eq_sym_involutive,
         EqdepFacts.internal_eq_sym_internal in *.

Lemma Fin_to_pos_spec p n f :
  Fin.of_nat (Nat.pred (Pos.to_nat p)) n = inleft f
    -> p = Fin_to_pos f.
Proof.
  intros.
  destruct n.
    inversion f.
  induction p using Pos.peano_rect; simpl in *.
    dependent elimination f; simpl; auto.
    inv H0.
Admitted.

Lemma arrows_and_indices f dom cod (t : Term tys dom cod) :
  STerm_embed dom cod f = Some t
    -> SExpr.arrows f = List.map Fin_to_pos (term_indices t).
Proof.
  generalize dependent cod.
  generalize dependent dom.
  unfold STerm_embed in *; induction f; simpl in *; auto.
  - intros.
    repeat match goal with
             [ H : context[match ?b with _ => _ end] |- _ ] =>
             destruct b; [|discriminate]; cat
           end; subst.
    inv H0.
    reflexivity.
  - intros.
    repeat match goal with
             [ H : context[match ?b with _ => _ end] |- _ ] =>
             destruct b eqn:?; [|discriminate]; cat
           end; subst.
    inv H0.
    inv Heqo.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply eq_dec].
    subst; simpl.
    erewrite <- Fin_to_pos_spec; eauto.
  - intros.
    repeat match goal with
             [ H : context[match ?b with _ => _ end] |- _ ] =>
             destruct b eqn:?; [|discriminate]; cat
           end; subst.
    inv H0.
    inv Heqo.
    inv Heqo1.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply eq_dec].
    subst; simpl.
    specialize (IHf2 _ _ e1).
    specialize (IHf1 _ _ e2).
    rewrite Heqo0 in IHf2.
    rewrite H1 in IHf1.
    rewrite Fin_eq_dec_refl in *.
    simpl_eq.
    specialize (IHf2 eq_refl).
    specialize (IHf1 eq_refl).
    rewrite List.map_app.
    now rewrite IHf1, IHf2.
Qed.

Lemma map_inj {A B : Type} (f : A -> B)
      (f_inj : forall x y, f x = f y -> x = y) xs ys :
  List.map f xs = List.map f ys -> xs = ys.
Proof.
  generalize dependent ys.
  induction xs, ys; simpl; intros; auto; try inv H0.
  apply f_inj in H2; subst.
  f_equal.
  now apply IHxs.
Qed.

Program Fixpoint sexpr_backward (t : SExpr positive) {measure (sexpr_size t)} :
  [sexprD t] :=
  match t with
  | STop => Yes
  | SBottom => No
  | SEquiv x y f g => _
  | SAnd p q       =>
    match sexpr_backward p with
    | Proved _ _  => Reduce (sexpr_backward q)
    | Uncertain _ => No
    end
  | SOr p q        =>
    match sexpr_backward p with
    | Proved _ _  => Yes
    | Uncertain _ => Reduce (sexpr_backward q)
    end
  | SImpl p q      =>
    sexpr_forward q p (sexpr_backward q)
  end.
Next Obligation.
  destruct (list_beq Pos.eqb (SExpr.arrows f) (SExpr.arrows g)) eqn:?;
    [|apply Uncertain].
  destruct (Fin.of_nat _ num_objs); [|apply Uncertain].
  destruct (Fin.of_nat _ num_objs); [|apply Uncertain].
  destruct (stermD _ _ f) eqn:?; [|apply Uncertain].
  destruct (stermD _ _ g) eqn:?; [|apply Uncertain].
  apply Proved.
  destruct (stermD_embeds _ _ Heqo) eqn:?, p.
  destruct (stermD_embeds _ _ Heqo0) eqn:?, p.
  subst.
  apply list_beq_eq in Heqb; auto.
    apply term_indices_equiv.
    pose proof (arrows_and_indices _ _ _ _ e).
    pose proof (arrows_and_indices _ _ _ _ e1).
    rewrite Heqb in H0.
    rewrite H0 in H1.
    apply map_inj in H1; auto.
    apply Fin_to_pos_inj.
  apply Pos_eqb_eq.
Qed.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. intuition. Defined.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. intuition. Defined.

Definition sexpr_tauto : forall t, [sexprD t].
Proof. intros; refine (Reduce (sexpr_backward t)); auto. Defined.

Lemma sexpr_sound t :
  (if sexpr_tauto t then True else False) -> sexprD t.
Proof. unfold sexpr_tauto; destruct t, (sexpr_backward _); tauto. Qed.

End Logic.

Require Export Category.Solver.Reify.

Ltac categorical := reify_terms_and_then
  ltac:(fun env g => apply sexpr_sound; now vm_compute).

Example sample_1 :
  ∀ (C : Category) (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z),
    g ∘ id ∘ id ∘ id ∘ h ≈ i ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ h ≈ i ->
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  repeat match goal with | [ H : _ ≈ _ |- _ ] => revert H end.
  (* Set Ltac Profiling. *)
  Time categorical.
  (* Show Ltac Profile. *)
Qed.

Print Assumptions sample_1.
