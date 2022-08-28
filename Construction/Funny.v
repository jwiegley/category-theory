Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Structure.Pullback.
Require Export Category.Structure.Cartesian.
Require Export Category.Construction.Discrete.
Require Export Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Bifunctor.
Require Export Category.Instance.Cat.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

Definition left_inclusion {C D : Category} :
  C ₀ ∏ D ₀ ⟶ C ∏ D ₀.
Proof.
  construct; auto.
  - destruct x, y, f as [d ?]; simpl in *.
    destruct d.
    split; auto.
    exact id.
  - proper; simpl in *; subst;
    destruct y0; cat.
  - destruct x; cat.
  - destruct x, y, z, f as [d ?], g as [d1 ?]; simpl in *.
    destruct d, d1; cat.
Defined.

Definition right_inclusion {C D : Category} :
  C ₀ ∏ D ₀ ⟶ C ₀ ∏ D.
Proof.
  construct; auto.
  - destruct x, y, f as [? d]; simpl in *.
    destruct d.
    split; auto.
    exact id.
  - proper; simpl in *; subst;
    destruct y0; cat.
  - destruct x; cat.
  - destruct x, y, z, f as [? d], g as [? d1]; simpl in *.
    destruct d, d1; cat.
Defined.

(* This definition is taken from "Free Products of Higher Operad Algebras" by
   Mark Weber *)
Program Definition Funny (A B : Category) : Category := {|
  obj := A ∏ B;
  hom := λ '(a₁,b₁) '(a₂, b₂),
    ∃ (α : a₁ ~{A}~> a₂) (β : b₁ ~{B}~> b₂),
      bimap α id ∘ bimap id β ≈ bimap id β ∘ bimap α id;
  homset := λ '(_, _) '(_, _), {|
    equiv := λ '(α₁; (β₁; _)) '(α₂; (β₂; _)), α₁ ≈ α₂ ∧ β₁ ≈ β₂
  |};
  id := λ '(_, _), (id; (id; _));
  compose := λ '(_, _) '(_, _) '(_, _) '(fα; (fβ; _)) '(gα; (gβ; _)),
    (fα ∘ gα; (fβ ∘ gβ; _))
|}.
Next Obligation. equivalence. Defined.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Notation "C □ D" := (Funny C D)
  (at level 8, right associativity) : category_scope.

Program Definition FunnyCategory {C D : Category} :
  @Pushout Cat (C ∏ D ₀) (C ₀ ∏ D) (C ₀ ∏ D ₀)
    left_inclusion right_inclusion := {|
  Pull := C □ D;
  pullback_fst := {|
    fobj := Datatypes.id;
    fmap := λ '(a₁, b₁) '(a₂, b₂) '(α, β), (α; (_; _));
  |};
  pullback_snd := {|
    fobj := Datatypes.id;
    fmap := λ '(a₁, b₁) '(a₂, b₂) '(α, β), (_; (β; _));
  |};
|}.
Next Obligation.
  destruct d.
  exact id.
Defined.
Next Obligation.
  simpl; simpl_eq.
  destruct d.
  cat.
Qed.
Next Obligation.
  destruct x, y, H; simpl in *; simpl_eq.
  destruct d.
  dependent destruction d0; cat.
Qed.
Next Obligation.
  simpl; simpl_eq; cat.
Qed.
Next Obligation.
  simpl; simpl_eq.
  destruct d0; simpl.
  destruct d; cat.
Defined.
Next Obligation.
  destruct d.
  exact id.
Defined.
Next Obligation.
  simpl; simpl_eq.
  destruct d.
  cat.
Qed.
Next Obligation.
  destruct x, y, H; simpl in *; simpl_eq.
  destruct d.
  dependent destruction d0; cat.
Qed.
Next Obligation.
  simpl; simpl_eq; cat.
Qed.
Next Obligation.
  simpl; simpl_eq.
  destruct d0, d; simpl; simpl_eq; cat.
Defined.
Next Obligation.
  construct; auto; simpl.
  destruct x, y, f; simpl in *.
  destruct d0, d; simpl; simpl_eq; cat.
Defined.
Next Obligation.
  unshelve eexists.
  - (* C □ D ⟶ Q *)
    construct.
    + now apply q1.
    + apply q1; simpl.
      destruct x, y, f, s; simpl in *.
      specialize (X0 (o, o0) (o, o0) (DiscId _, DiscId _));
      simpl in X0.
      split; auto.
      admit.
    + admit.
    + admit.
    + admit.
  - split.
    + unshelve eexists.
      * (* ∀ x : obj[C] ∧ obj[D], fobj[?u] x ≅ fobj[q1] x *)
        admit.
      * intros.
        admit.
    + unshelve eexists.
      * (* ∀ x : obj[C] ∧ obj[D], fobj[?u] x ≅ fobj[q2] x *)
        admit.
      * intros.
        admit.
  - intros.
    (* ?u ≈ v *)
    admit.
Admitted.
