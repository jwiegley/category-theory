Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reify.
Require Import Category.Solver.Normal.

Generalizable All Variables.

Section Decide.

Context `{Arrows}.

(** This code is from Certified Programming with Dependent Types (CPDT). *)

Inductive partial (P : Type) : Type :=
| Proved : P → partial
| Uncertain : partial.

Notation "[ P ]" := (partial P) : type_scope.

Declare Scope partial_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.

Program Fixpoint expr_forward (t : Expr) (hyp : Expr)
        (cont : [exprD t]) :
  [exprD hyp → exprD t] :=
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
Next Obligation. tauto. Defined.

#[local] Obligation Tactic := cat_simpl; intuition.

Program Fixpoint expr_backward (t : Expr) {measure t Expr_subterm} :
  [exprD t] :=
  match t with
  | Top           => Yes
  | Bottom        => No
  | Equiv x y f g => _
  | And p q       => expr_backward p && expr_backward q
  | Or p q        => expr_backward p || expr_backward q
  | Impl p q      => expr_forward q p (expr_backward q)
  end.
Next Obligation.
  destruct (morphism_eq_dec (to_morphism f) (to_morphism g)) eqn:?;
    [|apply Uncertain].
  destruct (termD _ _ f) eqn:?; [|apply Uncertain].
  destruct (termD _ _ g) eqn:?; [|apply Uncertain].
  apply Proved.
  apply from_morphism_to_morphism_r in Heqo.
  apply from_morphism_to_morphism_r in Heqo0.
  rewrite e in Heqo.
  rewrite Heqo in Heqo0.
  now simpl in Heqo0.
Defined.
Next Obligation. apply well_founded_Expr_subterm. Defined.

Definition expr_tauto : ∀ t, [exprD t].
Proof. intros; refine (Reduce (expr_backward t)); auto. Defined.

Lemma expr_sound t :
  (if expr_tauto t then True else False) → exprD t.
Proof. unfold expr_tauto; destruct t, (expr_backward _); tauto. Qed.

End Decide.

Ltac categorical := reify_terms_and_then
  ltac:(fun env g =>
          change (@exprD env g);
          apply expr_sound;
          now vm_compute).

Example ex_categorical (C : Category) `{@Cartesian C} (x y z w : C)
  (f : z ~> w) (g : y ~> z) (h : x ~> y) (i : x ~> z) :
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
  now categorical.
Qed.
