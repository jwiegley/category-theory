From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reify.
Require Import Category.Solver.Normal.

Section Decide.

Context `{Arrows}.

(** This code is from Certified Programming with Dependent Types (CPDT). *)

Inductive partial (P : Type) : Type :=
| Proved : P → partial
| Uncertain : partial.

#[local] Notation "'Yes'" := (Proved _ _).
#[local] Notation "'No'" := (Uncertain _).

#[local] Notation "'Reduce' v" := (if v then Yes else No)
  (at level 100).
#[local] Notation "x || y" := (if x then Yes else Reduce y).
#[local] Notation "x && y" := (if x then Reduce y else No).

Program Fixpoint expr_forward (t : Expr) (hyp : Expr)
        (cont : partial (exprSD t)) :
  partial (exprSD hyp → exprSD t) :=
  match hyp with
  | Top           => Reduce cont
  | Bottom        => Yes
  | Equiv x y f g => Reduce cont
  | And p q       => Reduce cont
  | Or p q        => expr_forward t p cont && expr_forward t q cont
  | Impl _ _      => Reduce cont
  end.
Next Obligation. tauto. Defined.
Next Obligation. intuition. Defined.

#[local] Obligation Tactic := cat_simpl; intuition.

Program Fixpoint expr_backward (t : Expr) :
  partial (exprSD t) :=
  match t with
  | Top           => Yes
  | Bottom        => No
  | Equiv x y f g => Reduce (eq_dec (to_morphism f) (to_morphism g))
  | And p q       => expr_backward p && expr_backward q
  | Or p q        => expr_backward p || expr_backward q
  | Impl p q      => expr_forward q p (expr_backward q)
  end.

Definition expr_tauto t : partial (exprSD t).
Proof.
  intros; refine (Reduce (expr_backward t)); auto.
Defined.

#[export]
Program Instance Term_Setoid : Setoid Term := {
  equiv f g := ∀ d c,
    if expr_tauto (Equiv d c f g) then True else False
}.
Next Obligation.
  unfold expr_tauto.
  construct; repeat intro; simpl.
  - now rewrite peq_dec_refl.
  - destruct (eq_dec _ _).
    + destruct (eq_dec _ _); auto.
    + destruct (eq_dec _ _); auto.
  - destruct (eq_dec _ _).
    + destruct (eq_dec _ _); auto.
      * destruct (eq_dec _ _); auto.
        rewrite e, e0 in n.
        tauto.
      * destruct (eq_dec _ _); auto.
    + destruct (eq_dec _ _); auto.
      * destruct (eq_dec _ _); auto.
      * destruct (eq_dec _ _); auto.
Qed.

#[export]
Program Instance Comp_respects :
  Proper (equiv ==> equiv ==> equiv) Comp.
Next Obligation.
  proper.
  unfold expr_tauto in *.
  simpl in *.
  repeat destruct (eq_dec _ _); auto.
  rewrite e, e0 in n.
  contradiction.
Qed.

Lemma expr_sound {d c f g h} :
  termD d c f = Some h → f ≈ g → exprD (Equiv d c f g).
Proof.
  intros.
  simple apply exprAD_sound'.
  specialize (X d c).
  revert X.
  unfold expr_tauto.
  destruct (expr_backward _); intuition.
  simple eapply exprSD_enough; eauto.
Qed.

End Decide.

Ltac categorify := reify_terms_and_then
  ltac:(fun env g =>
          change (@exprD _ env g);
          simple eapply expr_sound;
            [now vm_compute|eauto];
          clear).

Ltac categorical := reify_terms_and_then
  ltac:(fun env g =>
          change (@exprD _ env g);
          simple eapply expr_sound;
            [now vm_compute|eauto];
          clear;
          now vm_compute).

Example ex_categorical (C : Category) (x y z w : C)
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
  categorical.
  (* normalize. *)
  (* categorify. *)
  (* assert (Comp (Morph 2) (Comp (Morph 1) (Morph 0)) ≈ *)
  (*           Comp (Comp (Morph 2) (Morph 1)) (Morph 0)). { *)
  (*   now vm_compute. *)
  (* } *)
  (* rewrite X. *)
  (* now vm_compute. *)
Qed.
