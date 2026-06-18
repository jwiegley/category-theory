Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Instance.Coq.
Require Import Category.Instance.AST.
Require Import Category.Tools.Represented.

Generalizable All Variables.

(** * Compiling Coq functions to cartesian-closed combinators *)

(* nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   Conal Elliott, "Compiling to Categories", Proc. ACM Program. Lang. 1, ICFP
   (2017), 27:1–27:27. http://conal.net/papers/compiling-to-categories/

   By the Curry–Howard–Lambek correspondence the simply-typed lambda calculus is
   the internal language of cartesian closed categories: types are objects,
   pairing is the product, the function type is the exponential [z^y], lambda
   abstraction is [curry], and application is [eval]. A closed term of type
   [a → b] therefore denotes a morphism [repr a ~> repr b] in the free CCC
   ([AST]), and Elliott's "compiling to categories" is exactly this translation
   read as a program transformation.

   This file makes the translation's *correctness* explicit. Via [Repr] (see
   Tools/Represented) each Coq type [a] is represented by an object [repr a] and
   each value [x : a] by a global element [convert x : 1 ~> repr a]. A lambda
   term [lam : a → b] is correctly compiled to a combinator [ccc] when [convert]
   intertwines them — when applying [lam] then representing the result agrees
   with representing the argument then applying [ccc]:

       lam >==> ccc  :=  ∀ x, convert (lam x) ≈ ccc ∘ convert x

   i.e. [convert] is a homomorphism from the function [lam] to the arrow [ccc].
   The lemmas below are the per-construct compilation rules of [Compiling to
   Categories]: [ccc_id] (variable), [ccc_terminal] (unit introduction),
   [ccc_curry] (abstraction), and [ccc_apply]/[ccc_apply_pair] (application),
   each proving that the categorical combinator it names refines the source
   lambda. Composing these rules over the structure of a term compiles the whole
   term while preserving meaning. *)

Section Abstraction.

(* The correctness relation for compiling a unary function [lam : a → b] to a
   combinator [ccc : repr a ~> repr b]: [convert] carries [lam] to [ccc]. *)
Definition rel `{Repr a} `{Repr b}
           (lam : a → b) (ccc : repr a ~{AST}~> repr b) : Type :=
  ∀ x : a, convert (lam x) ≈ ccc ∘ convert x.

(* The curried, binary variant: a function [lam : a → b → c] is compiled to an
   arrow into the exponential [repr c ^ repr b], and correctness is checked
   after [uncurry] against the represented pair [convert (x, y)]. *)
Definition rel2 `{Repr a} `{Repr b} `{Repr c}
           (lam : a → b → c) (ccc : repr a ~{AST}~> repr c ^ repr b) : Type :=
  ∀ (x : a) (y : b), convert (lam x y) ≈ uncurry ccc ∘ convert (x, y).

Infix ">==>" := rel (at level 99) : category_scope.
Infix ">===>" := rel2 (at level 99) : category_scope.

(* Variable rule: the identity lambda [λx, x] compiles to the identity arrow. *)
Corollary ccc_id : ∀ `{Repr a}, (λ x : a, x) >==> id.
Proof. unfold rel; intros; cat. Qed.

Tactic Notation "step" constr(x) "=>" constr(y) :=
  replace x with y by auto.

(* Pairing of global elements is the represented pair: this is the [convert] of
   [prod_Repr] (see Tools/Represented) holding definitionally. *)
Corollary convert_fork `{Repr a} `{Repr b} (x : a) (y : b) :
  convert x △ convert y ≈ convert (x, y).
Proof. reflexivity. Qed.

(* Application rule: when [U] compiles to a curried arrow [U'] and [V] to [V'],
   the application [λx, U x (V x)] compiles to [eval ∘ U' △ V'] — feed the paired
   results of [U'] and [V'] to evaluation, exactly Elliott's [apply]. *)
Theorem ccc_apply :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a → b → c) (U' : repr a ~{AST}~> repr c ^ repr b)
    (V : a → b) (V' : repr a ~{AST}~> repr b),
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

(* Application rule with an uncurried callee [U : a * b → c]: the argument is
   paired with the input via [id △ V'] before applying [U']. *)
Theorem ccc_apply_pair :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a * b → c) (U' : repr a × repr b ~{AST}~> repr c)
    (V : a → b) (V' : repr a ~{AST}~> repr b),
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

(* Abstraction rule: an inner lambda [λy, U (x, y)] compiles by currying the
   uncurried combinator [U'], so [λx, λy, U (x, y)] compiles to [curry U']. *)
Theorem ccc_curry :
  ∀ `{Repr a} `{Repr b} `{Repr c}
    (U : a * b → c) (U' : repr a × repr b ~> repr c),
    U >==> U' ->
      (λ x, λ y, U (x, y)) >===> curry U'.
Proof.
  unfold rel, rel2; repeat intros.
  rewrite uncurry_curry.
  apply X.
Qed.

(* Unit-introduction rule: the constant [tt] map compiles to the unique arrow
   [one] into the terminal object, by [one_unique]. *)
Theorem ccc_terminal : ∀ `{Repr a},
  (λ _ : a, tt) >==> one.
Proof.
  unfold rel; simpl; intros; cat.
  apply one_unique.
Qed.

(* Logical bookkeeping: a non-dependent hypothesis [a] commutes past a universal
   quantifier in both directions (the curry/uncurry of implications). *)
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

(* A cartesian category equipped with a distinguished "numbers" object and an
   addition arrow on it — the minimal structure needed to compile arithmetic
   expressions. [Coq_Numerical] below realises it with [nat] and [Nat.add], and
   any model interpreting [AST] into such a category gives meaning to numeric
   programs. *)
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

(* A (cartesian) functor preserving the numerical structure: it identifies the
   source and target number objects ([map_num]) and carries source addition to
   target addition coherently with the product comparison [prod_out]. This lets
   addition be transported along [F], so [fmap add] is computed in the target. *)
Class NumericalFunctor := {
  map_num : numerical_obj ≅ F numerical_obj;

  fmap_add :
    fmap add ≈ map_num ∘ @add D _ _ ∘ split (map_num⁻¹) (map_num⁻¹)
                       ∘ @prod_out _ _ F _ _ _ numerical_obj numerical_obj
}.

End NumericalFunctor.

#[export]
Instance Coq_Numerical : @Numerical Coq Coq_Cartesian := {
  numerical_obj := nat;
  add := Datatypes.uncurry Nat.add
}.

Section Example.

Infix ">==>" := rel (at level 99) : category_scope.

(*
Theorem ccc_arity2 :
  ∀ (a b c : Type)
    (f : a → b) (f' : F a ~> F b)
    (g : a → b) (g' : F a ~> F b)
    (p : b → b → c) (p' : F b ~> F c ^ F b),
  f >==> f' ->
  g >==> g' ->
  p >==> exp_in ∘ p' ->
  (λ x : a, p (f x) (g x)) >==> uncurry p' ∘ f' △ g'.
Proof.
Abort.

Theorem ccc_plus :
  ∀ (f : nat → nat) (f' : F nat ~> F nat)
    (g : nat → nat) (g' : F nat ~> F nat),
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
Abort.
*)

(* f : A -->[Setoid] R *)
(* g : A -->[Setoid] R *)
(* + : R * R -->[Setoid] R *)
(* ============== *)
(* lambda x. f x + g x  : A -->[Setoid] R *)

(* Definition generic_add := fmap Nat.add. *)

End Example.

(* Eval simpl in @generic_add. *)
