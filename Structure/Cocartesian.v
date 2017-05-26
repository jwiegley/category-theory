Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Initial.
Require Export Category.Construction.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* To be cocartesian is just to be cartesian in the opposite category; but to
   avoid confusion, we'd like a set of notations specific to categories with
   cocartesian structure. *)

Notation "'Cocartesian' C" := (@Cartesian (C^op))
  (at level 9) : category_theory_scope.
Notation "@Cocartesian C" := (@Cartesian (C^op))
  (at level 9) : category_theory_scope.

Section Cocartesian_.

Context `{O : @Cocartesian C}.

Definition Coprod : C -> C -> C := @Prod _ O.

Infix "+" := Coprod : category_scope.

Definition merge {X Y Z : C} (f : Y ~> X) (g : Z ~> X) : Y + Z ~{C}~> X :=
  @fork _ O _ _ _ f g.

Infix "▽" := merge (at level 26) : category_scope.

Global Program Instance merge_respects {X Y Z} :
  Proper (equiv ==> equiv ==> equiv) (@merge X Y Z).
Next Obligation. apply (@fork_respects _ O). Qed.

Definition inl {X Y : C} : X ~{C}~> X + Y := @exl _ O _ _.
Definition inr {X Y : C} : Y ~{C}~> X + Y := @exr _ O _ _.

Definition left  {X Y Z : C} (f : X ~> Y) : X + Z ~{C}~> Y + Z :=
  (inl ∘ f) ▽ inr.

Definition right  {X Y Z : C} (f : X ~> Y) : Z + X ~{C}~> Z + Y :=
  inl ▽ (inr ∘ f).

Definition cover  {X Y Z W : C} (f : X ~> Y) (g : Z ~> W) :
  X + Z ~{C}~> Y + W :=
  (inl ∘ f) ▽ (inr ∘ g).

Global Program Instance parametric_morphism_left {a b c : C} :
  Proper (equiv ==> equiv) (@left a b c).
Next Obligation. apply (@parametric_morphism_first _ O). Qed.

Global Program Instance parametric_morphism_right {a b c : C} :
  Proper (equiv ==> equiv) (@right a b c).
Next Obligation. apply (@parametric_morphism_second _ O). Qed.

Global Program Instance parametric_morphism_cover {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@cover a b c d).
Next Obligation.
  proper.
  unfold cover.
  rewrite X, X0.
  reflexivity.
Qed.

Definition paws {X Y : C} : X + Y ~{C}~> Y + X := @swap _ O _ _.

Lemma inl_merge {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inl ≈ f.
Proof. apply (@exl_fork _ O). Qed.

Hint Rewrite @inl_merge : categories.

Lemma inr_merge {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inr ≈ g.
Proof. apply (@exr_fork _ O). Qed.

Hint Rewrite @inr_merge : categories.

Corollary merge_inl_inr {X Y : C} :
  inl ▽ inr ≈ @id C (X + Y).
Proof. apply (@fork_exl_exr _ O). Qed.

Hint Rewrite @merge_inl_inr : categories.

Corollary merge_inv {X Y Z : C} (f h : Y ~> X) (g i : Z ~> X) :
  f ▽ g ≈ h ▽ i <--> (f ≈ h) * (g ≈ i).
Proof. apply (@fork_inv _ O). Qed.

Corollary merge_comp {X Y Z W : C} (f : Y ~> Z) (h : W ~> Z) (g : Z ~> X) :
  (g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h.
Proof. apply (@fork_comp _ O). Qed.

Theorem left_comp {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  left (Z:=W) (f ∘ g) ≈ left f ∘ left g.
Proof. apply (@first_comp _ O). Qed.

Theorem left_fork {X Y Z W : C} (f : Y ~> X) (g : Z ~> X) (h : W ~> Y) :
  f ▽ g ∘ left h ≈ (f ∘ h) ▽ g.
Proof. apply (@first_fork _ O). Qed.

Theorem right_comp {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  right (Z:=W) (f ∘ g) ≈ right f ∘ right g.
Proof. apply (@second_comp _ O). Qed.

Theorem right_fork {X Y Z W : C} (f : Y ~> X) (g : Z ~> X) (h : W ~> Z) :
  f ▽ g ∘ right h ≈ f ▽ (g ∘ h).
Proof. apply (@second_fork _ O). Qed.

Corollary inl_left {X Y Z : C} (f : X ~> Y) :
  left f ∘ @inl X Z ≈ inl ∘ f.
Proof. apply (@exl_first _ O). Qed.

Hint Rewrite @inl_left : categories.

Corollary inr_left {X Y Z : C} (f : X ~> Y) :
  left f ∘ @inr X Z ≈ inr.
Proof. apply (@exr_first _ O). Qed.

Hint Rewrite @inr_left : categories.

Corollary inl_right {X Y Z : C} (f : X ~> Y) :
  right f ∘ @inl Z X ≈ inl.
Proof. apply (@exl_second _ O). Qed.

Hint Rewrite @inl_right : categories.

Corollary inr_right {X Y Z : C} (f : X ~> Y) :
  right f ∘ @inr Z X ≈ inr ∘ f.
Proof. apply (@exr_second _ O). Qed.

Hint Rewrite @inr_right : categories.

Theorem paws_left {X Y Z : C} (f : X ~> Y) :
  paws ∘ left (Z:=Z) f ≈ right f ∘ paws.
Proof. symmetry; apply (@swap_second _ O Y X Z f). Qed.

Theorem paws_right {X Y Z : C} (f : X ~> Y) :
  paws ∘ right f ≈ left (Z:=Z) f ∘ paws.
Proof. symmetry; apply (@swap_first _ O Y X Z f). Qed.

Theorem left_right {X Y Z W : C} (f : X ~> Y) (g : Z ~> W) :
  left f ∘ right g ≈ right g ∘ left f.
Proof. symmetry; apply (@first_second _ O). Qed.

Theorem paws_fork {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
  f ▽ g ∘ paws ≈ g ▽ f.
Proof. apply (@swap_fork _ O). Qed.

Context `{I : @Initial C}.

Global Program Instance coprod_zero_l {X : C} :
  0 + X ≅ X := {
  to   := zero ▽ id;
  from := inr
}.
Next Obligation. apply (@prod_one_l _ _ I). Qed.

Hint Rewrite @coprod_zero_l : isos.

Global Program Instance coprod_zero_r {X : C} :
  X + 0 ≅ X := {
  to   := id ▽ zero;
  from := inl
}.
Next Obligation. apply (@prod_one_r _ _ I). Qed.

Hint Rewrite @coprod_zero_r : isos.

Global Program Instance coprod_assoc  {X Y Z : C} :
  (X + Y) + Z ≅ X + (Y + Z) := {
  to   := (inl ▽ (inr ∘ inl)) ▽ (inr ∘ inr);
  from := (inl ∘ inl) ▽ ((inl ∘ inr) ▽ inr)
}.
Next Obligation. apply (@prod_assoc _ O). Qed.
Next Obligation. apply (@prod_assoc _ O). Qed.

End Cocartesian_.

Infix "+" := Coprod : category_scope.
Infix "▽" := merge (at level 26) : category_scope.

Hint Rewrite @inl_merge : categories.
Hint Rewrite @inr_merge : categories.
Hint Rewrite @merge_inl_inr : categories.
Hint Rewrite @coprod_zero_r : isos.
Hint Rewrite @coprod_zero_l : isos.
