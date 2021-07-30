Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.BiCCC.
Require Export Category.Functor.Structure.Cartesian.
Require Export Category.Functor.Structure.Cartesian.Closed.
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
  rewrites.
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
  rewrites.
  rewrite convert_fork.
  reflexivity.
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
  (λ _ : a, tt) >==> one.
Proof.
  unfold rel; simpl; intros; cat.
Qed.

Lemma distribute_forall : ∀ a {X} P, (a → ∀ (x : X), P x) → (∀ x, a → P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

Lemma forall_distribute : ∀ a {X} P, (∀ x, a → P x) → (a → ∀ (x : X), P x).
Proof.
  intros.
  apply X0.
  assumption.
Qed.

End Abstraction.

Class Numerical (C : Category) `{@Cartesian C} := {
  numerical_obj : obj;
  add : numerical_obj × numerical_obj ~> numerical_obj
}.

Section NumericalFunctor.

Context `{F : C ⟶ D}.
Context `{@Cartesian C}.
Context `{@Numerical C _}.
Context `{@Cartesian D}.
Context `{@Numerical D _}.
Context `{@CartesianFunctor _ _ F _ _}.

Class NumericalFunctor := {
  map_num : numerical_obj ≅ F numerical_obj;

  fmap_add :
    fmap add ≈ map_num ∘ @add D _ _ ∘ split (map_num⁻¹) (map_num⁻¹)
                       ∘ @prod_out _ _ F _ _ _ numerical_obj numerical_obj
}.

End NumericalFunctor.

Instance Coq_Numerical : @Numerical Coq Coq_Cartesian := {
  numerical_obj := nat;
  add := prod_curry Nat.add
}.

Section Example.

Infix ">==>" := rel (at level 99) : category_scope.

(*
Theorem ccc_arity2 :
  ∀ (a b c : Type)
    (f : a -> b) (f' : F a ~> F b)
    (g : a -> b) (g' : F a ~> F b)
    (p : b -> b -> c) (p' : F b ~> F c ^ F b),
  f >==> f' ->
  g >==> g' ->
  p >==> exp_in ∘ p' ->
  (λ x : a, p (f x) (g x)) >==> uncurry p' ∘ f' △ g'.
Proof.
Admitted.

Theorem ccc_plus :
  ∀ (f : nat -> nat) (f' : F nat ~> F nat)
    (g : nat -> nat) (g' : F nat ~> F nat),
  f >==> f' ->
  g >==> g' ->
  (λ x : nat, (f x + g x)%nat)
    >==> map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹) ∘ f' △ g'.
Proof.
  intros.
  pose proof (ccc_arity2 nat nat nat f f' g g' Nat.add
                         (curry (map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹)))
                         X X0).
  simpl in X1.
  unfold rel in *; repeat intros.
  rewrite uncurry_curry in X1.
  rewrites; [reflexivity|]; clear X1.
  pose proof (@fmap_add Coq _ _ _ _ _ _ _ _) as HA.
  simpl in HA.
  assert (Nat.add = prod_uncurry (λ p : nat * nat, (fst p + snd p)%nat)) by auto.
  rewrites.
Admitted.
*)

(* f : A -->[Setoid] R *)
(* g : A -->[Setoid] R *)
(* + : R * R -->[Setoid] R *)
(* ============== *)
(* lambda x. f x + g x  : A -->[Setoid] R *)

(* Definition generic_add := fmap Nat.add. *)

End Example.

(* Eval simpl in @generic_add. *)
