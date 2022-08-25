Set Warnings "-notation-overridden".

Require Import Coq.PArith.PArith.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reify.
Require Import Category.Solver.Normal.

Generalizable All Variables.

Section Decide.

Context `{Env}.

(** This code is from Certified Programming with Dependent Types (CPDT). *)

Inductive partial (P : Type) : Type :=
| Proved : P → partial P
| Uncertain : partial P.

Notation "[ P ]" := (partial P) : type_scope.

Declare Scope partial_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.

Program Fixpoint sexpr_forward (t : SExpr) (hyp : SExpr)
        (cont : [sexprD t]) :
  [sexprD hyp → sexprD t] :=
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
Next Obligation. tauto. Defined.
Next Obligation. intuition. Defined.

Program Fixpoint sexpr_backward (t : SExpr) {measure t SExpr_subterm} :
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
  destruct (list_eqdec _ (sindices f) (sindices g)) eqn:?;
    [|apply Uncertain].
  destruct (Pos_to_fin _); [|apply Uncertain].
  destruct (Pos_to_fin _); [|apply Uncertain].
  destruct (stermD _ _ f) eqn:?; [|apply Uncertain].
  destruct (stermD _ _ g) eqn:?; [|apply Uncertain].
  apply Proved.
  apply unsindices_sindices_r in Heqo.
  apply unsindices_sindices_r in Heqo0.
  rewrite e in Heqo.
  rewrite Heqo in Heqo0.
  now simpl in Heqo0.
Defined.
Next Obligation. intuition. Defined.
Next Obligation. intuition. Defined.
Next Obligation. intuition. Defined.
Next Obligation. intuition. Defined.
Next Obligation. intuition. Defined.
Next Obligation. apply well_founded_SExpr_subterm. Defined.

Definition sexpr_tauto : ∀ t, [sexprD t].
Proof. intros; refine (Reduce (sexpr_backward t)); auto. Defined.

Lemma sexpr_sound t :
  (if sexpr_tauto t then True else False) → sexprD t.
Proof. unfold sexpr_tauto; destruct t, (sexpr_backward _); tauto. Qed.

End Decide.

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
  now categorical.
Qed.
