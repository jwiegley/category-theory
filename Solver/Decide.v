Set Warnings "-notation-overridden".

Require Import Category.Lib.TList.
Require Import Category.Solver.Partial.
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

Program Fixpoint expr_forward (t : Expr) (hyp : Expr) (cont : [exprD t]) :
  [exprD hyp -> exprD t] :=
  match hyp with
  | Top           => Reduce cont
  | Bottom        => Yes
  | Equiv x y f g => Reduce cont
  | And p q       => Reduce cont
  | Or p q        => if expr_forward t p cont
                     then Reduce (expr_forward t q cont)
                     else No
  | Impl _ _      => Reduce cont
  end.
Next Obligation. contradiction. Defined.
Next Obligation. intuition. Defined.

Program Fixpoint expr_backward (t : Expr) {measure (expr_size t)} :
  [exprD t] :=
  match t with
  | Top => Yes
  | Bottom => No
  | Equiv x y f g => _
  | And p q       =>
    match expr_backward p with
    | Proved _ _  => Reduce (expr_backward q)
    | Uncertain _ => No
    end
  | Or p q        =>
    match expr_backward p with
    | Proved _ _  => Yes
    | Uncertain _ => Reduce (expr_backward q)
    end
  | Impl p q      =>
    expr_forward q p (expr_backward q)
  end.
Next Obligation.
  destruct (list_beq Fin.eqb (term_indices f) (term_indices g)) eqn:?;
    [|apply Uncertain].
  apply Proved.
  apply term_indices_equiv.
  apply list_beq_eq in Heqb; auto.
  apply Fin_eqb_eq.
Defined.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. intuition. Defined.
Next Obligation. simpl; abstract omega. Defined.
Next Obligation. intuition. Defined.

Definition expr_tauto : forall t, [exprD t].
Proof. intros; refine (Reduce (expr_backward t)); auto. Defined.

Lemma expr_sound t :
  (if expr_tauto t then True else False) -> exprD t.
Proof. unfold expr_tauto; destruct t, (expr_backward _); tauto. Qed.

End Logic.

Require Export Category.Solver.Reify.

Ltac categorical := reify_terms_and_then
  ltac:(fun env g => apply expr_sound; now vm_compute).

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
