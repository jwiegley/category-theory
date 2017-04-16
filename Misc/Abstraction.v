Require Import Category.Lib.
Require Export Category.Structure.BiCCC.
Require Export Category.Instance.Coq.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Abstraction.

Context `{C : Category}.
Context `{F : Coq ⟶ C}.
Context `{AF : @CartesianFunctor _ _ F _ HA}.
Context `{@ClosedFunctor _ _ F _ _ AF _ HC}.
Context `{TF : @TerminalFunctor _ _ F _ HT}.

Definition rel `(lam : a -> b) (ccc : F a ~> F b) : Prop :=
  fmap[F] lam ≈ ccc.

Infix "===>" := rel (at level 99) : category_scope.

Theorem ccc_id : ∀ (a : Type), (λ x : a, x) ===> id.
Proof.
  unfold rel; intros.
  rewrite <- fmap_id.
  reflexivity.
Qed.

Tactic Notation "step" constr(x) "=>" constr(y) :=
  replace x with y by auto.

(*
Theorem ccc_apply :
  ∀ (a b c : Type)
    (U : a -> b -> c) (U' : F a ~> F c ^ F b)
    (V : a -> b) (V' : F a ~> F b),
  U ===> exp_in ∘ U' ->
  V ===> V' ->
    (λ x, U x (V x)) ===> eval ∘ (U' △ V').
Proof.
  unfold rel; intros; subst.
  step (λ x, U x (V x)) => (λ x, @eval Coq _ _ b c (U x, V x)).
  step (λ x, @eval Coq _ _ b c (U x, V x))
    => (λ x, @eval Coq _ _ b c ((U △ V) x)).
  step (λ x, @eval Coq _ _ b c ((U △ V) x))
    => (@eval Coq _ _ b c ∘ (U △ V)).
  rewrite fmap_comp.
  rewrite fmap_eval.
  rewrite fmap_fork.
  rewrite comp_assoc.
  rewrite <- (comp_assoc _ prod_out).
  rewrite prod_out_in.
  rewrite id_right.
  generalize (proj2 (exp_out_inj (fmap U) (exp_in ∘ U')) H0).
  rewrite comp_assoc.
  rewrite exp_out_in.
  rewrite id_left.
  intros; subst.
  rewrite <- eval_curry.
  rewrite curry_uncurry.
  rewrite curry_eval.
  rewrite id_left.
  rewrite H1, H2.
  reflexivity.
Qed.
*)

Theorem ccc_curry :
  ∀ (a b c : Type)
    (U : a * b -> c) (U' : F a × F b ~> F c),
    U ===> U' ∘ prod_out ->
      (λ x, λ y, U (x, y)) ===> exp_in ∘ curry U'.
Proof.
  unfold rel; intros; subst.
  generalize (@fmap_curry Coq _ _ _ _ _ _ _ _ a b c U).
  simpl.
  intro H2; rewrite H2; clear H2.
  pose proof (@exp_in_inj Coq _ _ _ _ _ _ _ _ a b c) as H2.
  apply H2; clear H2.
  simpl in H0; rewrite H0; clear H0.
  rewrite <- comp_assoc.
  pose proof (@prod_out_in Coq _ _ _ _ _ a b) as H2.
  simpl in H2; rewrite H2; clear H2.
  rewrite id_right.
  reflexivity.
Qed.

Theorem ccc_terminal : ∀ (a : Type),
  (λ _ : a, tt) ===> map_one ∘ @one _ _ (F a).
Proof.
  unfold rel; intros.
  step (λ _ : a, tt) => (@one Coq _ a).
  pose proof (@fmap_one _ _ _ _ _ _) as H1.
  apply H1.
Qed.

End Abstraction.
