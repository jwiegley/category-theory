Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.BiCCC.
Require Export Category.Functor.Structure.Cartesian.
Require Export Category.Functor.Structure.Closed.
Require Export Category.Functor.Structure.Terminal.
Require Export Category.Instance.Coq.
Require Export Category.Instance.AST.
Require Export Category.Tools.Represented.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Abstraction.

Definition rel `{Repr a} `{Repr b}
           (lam : a -> b) (ccc : repr a ~{AST}~> repr b) : Type :=
  ∀ x : a, convert (lam x) ≈ ccc ∘ convert x.

Definition rel2 `{Repr a} `{Repr b} `{Repr c}
           (lam : a -> b -> c) (ccc : repr a ~{AST}~> repr c ^ repr b) : Type :=
  ∀ (x : a) (y : b), convert (lam x y) ≈ uncurry ccc ∘ convert (x, y).

Infix ">==>" := rel (at level 99) : category_scope.
Infix ">===>" := rel2 (at level 99) : category_scope.

Corollary ccc_id : ∀ `{Repr a}, (λ x : a, x) >==> id.
Proof. unfold rel; intros; cat. Qed.

Tactic Notation "step" constr(x) "=>" constr(y) :=
  replace x with y by auto.

Corollary convert_fork `{Repr a} `{Repr b} (x : a) (y : b) :
  convert x △ convert y ≈ convert (x, y).
Proof. reflexivity. Qed.

Theorem ccc_apply :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a -> b -> c) (U' : repr a ~{AST}~> repr c ^ repr b)
    (V : a -> b) (V' : repr a ~{AST}~> repr b),
  U >===> U' ->
  V >==> V' ->
    (λ x, U x (V x)) >==> eval ∘ U' △ V'.
Proof.
  unfold rel, rel2; repeat intros.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- X0; clear X0.
  rewrite X; clear X.
  rewrite <- eval_first.
  comp_left.
  unfold first.
  rewrite <- fork_comp.
  rewrite <- comp_assoc.
  rewrite <- convert_fork; cat.
Qed.

Theorem ccc_apply_pair :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a * b -> c) (U' : repr a × repr b ~{AST}~> repr c)
    (V : a -> b) (V' : repr a ~{AST}~> repr b),
  U >==> U' ->
  V >==> V' ->
    (λ x, U (x, V x)) >==> U' ∘ id △ V'.
Proof.
  unfold rel; intros ??????? U' V; subst; intros.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite id_left.
  rewrite <- X0; clear X0.
  rewrite convert_fork.
  apply X.
Qed.

Theorem ccc_curry :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a * b -> c) (U' : repr a × repr b ~> repr c),
    U >==> U' ->
      (λ x, λ y, U (x, y)) >===> curry U'.
Proof.
  unfold rel, rel2; repeat intros.
  rewrite uncurry_curry.
  apply X.
Qed.

Theorem ccc_terminal : ∀ `{Repr a},
  (λ _ : a, tt) >==> map_one ∘ @one _ _ (repr a).
Proof.
  unfold rel; simpl; intros; cat.
Qed.

End Abstraction.
