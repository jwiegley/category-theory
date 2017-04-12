Require Import Lib.
Require Export BiCCC.
Require Export Coq.

Generalizable All Variables.
Set Primitive Projection.
Set Universe Polymorphism.

Section Abstraction.

Variable ob : Type.
Context `{Closed ob}.
Context `{F : @ClosedFunctor Type _ ob _}.

Import EqNotations.

Definition rel `(lam : a -> b) (ccc : fobj a ~> fobj b) : Prop :=
  fmap (H:=terminal_category
          (Terminal:=cartesian_terminal
             (Cartesian:=closed_cartesian
                (Closed:=Coq_Closed)))) lam ≈ ccc.

Infix "===>" := rel (at level 99) : category_scope.

Theorem ccc_id : ∀ (a : Type), (λ x : a, x) ===> id.
Proof.
  unfold rel; intros.
  rewrite <- fmap_id.
  reflexivity.
Qed.

Tactic Notation "step" constr(x) "=>" constr(y) :=
  replace x with y by auto.

Theorem ccc_apply :
  ∀ (a b c : Type)
    (U : a -> b -> c) (U' : fobj a ~> fobj c ^ fobj b)
    (V : a -> b) (V' : fobj a ~> fobj b),
  U ===> exp_in ∘ U' ->
  V ===> V' ->
    (λ x, U x (V x)) ===> eval ∘ (U' △ V').
Proof.
  unfold rel; intros; subst.
  step (λ x, U x (V x)) => (λ x, @eval Type _ b c (U x, V x)).
  step (λ x, U x (V x)) => (λ x, @eval Type _ b c (U x, V x)).
  step (λ x, @eval Type _ b c (U x, V x))
    => (λ x, @eval Type _ b c ((U △ V) x)).
  step (λ x, @eval Type _ b c ((U △ V) x))
    => (@eval Type _ b c ∘ (U △ V)).
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

Theorem ccc_curry :
  ∀ (a b c : Type)
    (U : a * b -> c) (U' : fobj a × fobj b ~> fobj c),
    U ===> U' ∘ prod_out ->
      (λ x, λ y, U (x, y)) ===> exp_in ∘ curry U'.
Proof.
  unfold rel; intros; subst.
  generalize (@fmap_curry Type _ ob _ _ a b c U).
  simpl.
  unfold arrow.
  intro H1; rewrite H1; clear H1.
  pose proof (@exp_in_inj Type _ ob _ _ a b c) as H1.
  apply H1; clear H1.
  simpl in H0; rewrite H0; clear H0.
  rewrite <- comp_assoc.
  pose proof (@prod_out_in Type _ ob _ _ a b) as H1.
  simpl in H1; rewrite H1; clear H1.
  rewrite id_right.
  reflexivity.
Qed.

Theorem ccc_terminal : ∀ (a : Type),
  (λ _ : a, tt) ===> map_one ∘ @one _ _ (fobj a).
Proof.
  unfold rel; intros.
  step (λ _ : a, tt) => (@one _ _ a).
  pose proof @fmap_one.
  simpl in H0.
  rewrite H0.
  reflexivity.
Qed.

End Abstraction.
