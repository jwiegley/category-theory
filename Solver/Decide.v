Set Warnings "-notation-overridden".

Require Import Category.Lib.TList.
Require Import Category.Solver.Partial.
Require Import Category.Solver.Reflect.
Require Import Category.Solver.Arrows.

Generalizable All Variables.

Section Decide.

Context `{Env}.

Open Scope partial_scope.

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
  destruct (list_beq Pos.eqb (sarrows f) (sarrows g)) eqn:?;
    [|apply Uncertain].
  destruct (Pos_to_fin _); [|apply Uncertain].
  destruct (Pos_to_fin _); [|apply Uncertain].
  destruct (stermD _ _ f) eqn:?; [|apply Uncertain].
  destruct (stermD _ _ g) eqn:?; [|apply Uncertain].
  apply Proved.
  apply list_beq_eq in Heqb; auto; [|apply Pos_eqb_eq].
  destruct (stermD_embeds _ _ Heqo) eqn:?, p.
  destruct (stermD_embeds _ _ Heqo0) eqn:?, p.
  rewrite <- e0, <- e2.
  apply term_indices_equiv.
  pose proof (arrows_and_indices _ _ _ _ e).
  pose proof (arrows_and_indices _ _ _ _ e1).
  rewrite Heqb in H0.
  rewrite H0 in H1.
  apply map_inj in H1; auto.
  apply Fin_to_pos_inj.
Defined.
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

End Decide.

Require Export Category.Solver.Reify.

Ltac categorical := reify_terms_and_then
  ltac:(fun env g =>
          change (@sexprD env g);
          apply sexpr_sound;
          now vm_compute).

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
