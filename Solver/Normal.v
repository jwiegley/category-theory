Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Category.Lib.TList.
Require Export Category.Lib.NETList.
Require Export Category.Solver.Denote.
Require Export Category.Solver.NArrows.

Generalizable All Variables.

Import VectorNotations.

Section Normal.

Context `{Env}.

Import EqNotations.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv d _ f g =>
    match winnow (arrows f), winnow (arrows g) with
    | inright H1, inright H2 => True
    | inleft f, inright H2 =>
      narrowsD f ≈ rew [fun x => _ ~> objs x] H2 in @id cat (objs d)
    | inright H1, inleft g =>
      rew [fun x => _ ~> objs x] H1 in @id cat (objs d) ≈ narrowsD g
    | inleft f, inleft g => narrowsD f ≈ narrowsD g
    end
  | And p q       => exprAD p ∧ exprAD q
  | Or p q        => exprAD p + exprAD q
  | Impl p q      => exprAD p -> exprAD q
  end.

Theorem exprAD_sound (e : Expr) : exprAD e ↔ exprD e.
Proof.
  induction e; split; simpl in *; intuition.
  - rewrite term_narrows.
    symmetry.
    rewrite term_narrows.
    symmetry.
    destruct (winnow (arrows f)), (winnow (arrows g)); auto.
    simpl_eq.
    dependent elimination e.
    dependent elimination e0; simpl.
    reflexivity.
  - rewrite term_narrows in X.
    symmetry in X.
    rewrite term_narrows in X.
    symmetry in X.
    destruct (winnow (arrows f)), (winnow (arrows g)); auto.
Defined.

End Normal.

Require Export Category.Solver.Reify.

Ltac normalize := reify_terms_and_then
  ltac:(fun env g => apply exprAD_sound; vm_compute).

Example sample_2 :
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
  Time normalize.               (* 1.23s *)
  intros; cat.
Time Qed.                       (* 3.783s *)

Print Assumptions sample_2.
