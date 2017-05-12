Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Reserved Infix "×" (at level 40, left associativity).

Section Cartesian.

Context `{C : Category}.

Class Cartesian:= {
  Prod : ob -> ob -> ob
    where "X × Y" := (Prod X Y);

  fork {X Y Z} (f : X ~> Y) (g : X ~> Z) : X ~> Y × Z;
  exl  {X Y} : X × Y ~> X;
  exr  {X Y} : X × Y ~> Y;

  fork_respects :> ∀ X Y Z,
    Proper (equiv ==> equiv ==> equiv) (@fork X Y Z);

  ump_products {X Y Z} (f : X ~> Y) (g : X ~> Z) (h : X ~> Y × Z) :
    h ≈ fork f g <--> (exl ∘ h ≈ f) * (exr ∘ h ≈ g)
}.

Infix "×" := Prod : category_scope.
Infix "△" := fork (at level 28) : category_scope.

Context `{@Cartesian}.

Definition first  {X Y Z : C} (f : X ~> Y) : X × Z ~> Y × Z :=
  (f ∘ exl) △ exr.

Definition second  {X Y Z : C} (f : X ~> Y) : Z × X ~> Z × Y :=
  exl △ (f ∘ exr).

Definition split  {X Y Z W : C} (f : X ~> Y) (g : Z ~> W) :
  X × Z ~> Y × W :=
  first f ∘ second g.

Global Program Instance parametric_morphism_first {a b c : C} :
  Proper (equiv ==> equiv) (@first a b c).
Next Obligation.
  proper.
  unfold first.
  rewrite X.
  reflexivity.
Qed.

Global Program Instance parametric_morphism_second {a b c : C} :
  Proper (equiv ==> equiv) (@second a b c).
Next Obligation.
  proper.
  unfold second.
  rewrite X.
  reflexivity.
Qed.

Global Program Instance parametric_morphism_split {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@split a b c d).
Next Obligation.
  proper.
  unfold split.
  rewrite X, X0.
  reflexivity.
Qed.

Definition swap {X Y : C} : X × Y ~> Y × X := exr △ exl.

Corollary exl_fork {X Z W : C} (f : X ~> Z) (g : X ~> W) :
  exl ∘ f △ g ≈ f.
Proof.
  intros.
  apply (ump_products f g (f △ g)).
  reflexivity.
Qed.

Hint Rewrite @exl_fork : categories.

Corollary exr_fork {X Z W : C} (f : X ~> Z) (g : X ~> W) :
  exr ∘ f △ g ≈ g.
Proof.
  intros.
  apply (ump_products f g (f △ g)).
  reflexivity.
Qed.

Hint Rewrite @exr_fork : categories.

Corollary fork_exl_exr {X Y : C} :
  exl △ exr ≈ @id C (X × Y).
Proof.
  intros.
  symmetry.
  apply ump_products; split; cat.
Qed.

Hint Rewrite @fork_exl_exr : categories.

Corollary fork_inv {X Y Z : C} (f h : X ~> Y) (g i : X ~> Z) :
  f △ g ≈ h △ i <--> (f ≈ h) * (g ≈ i).
Proof.
  pose proof (ump_products h i (f △ g)) as HA;
  simplify; intuition.
  - rewrite <- a; cat.
  - rewrite <- b; cat.
  - apply X0; cat.
Qed.

Corollary fork_comp {X Y Z W : C}
          (f : Y ~> Z) (h : Y ~> W) (g : X ~> Y) :
  (f ∘ g) △ (h ∘ g) ≈ f △ h ∘ g.
Proof.
  intros.
  symmetry.
  apply ump_products; split;
  rewrite !comp_assoc; cat.
Qed.

Definition swap_invol {X Y : C} :
  swap ∘ swap ≈ @id C (X × Y).
Proof.
  unfold swap.
  rewrite <- fork_comp; cat.
Qed.

Hint Rewrite @swap_invol : categories.

Definition swap_inj_l {X Y Z : C} (f g : X ~> Y × Z) :
  swap ∘ f ≈ swap ∘ g -> f ≈ g.
Proof.
  intro HA.
  rewrite <- id_left.
  rewrite <- (id_left g).
  rewrite <- swap_invol.
  rewrite <- comp_assoc.
  rewrite HA.
  rewrite comp_assoc.
  reflexivity.
Qed.

Definition swap_inj_r {X Y Z : C} (f g : X × Y ~> Z) :
  f ∘ swap ≈ g ∘ swap -> f ≈ g.
Proof.
  intro HA.
  rewrite <- id_right.
  rewrite <- (id_right g).
  rewrite <- swap_invol.
  rewrite comp_assoc.
  rewrite HA.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

Theorem first_id {X Y : C} :
  first (id[X]) ≈ id[X × Y].
Proof. unfold first; cat. Qed.

Hint Rewrite @first_id : categories.

Theorem first_comp {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  first (Z:=W) (f ∘ g) ≈ first f ∘ first g.
Proof.
  unfold first.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem first_fork {X Y Z W : C} (f : X ~> Y) (g : X ~> Z) (h : Y ~> W) :
  first h ∘ f △ g ≈ (h ∘ f) △ g.
Proof.
  unfold first.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem second_id {X Y : C} :
  second (id[Y]) ≈ id[X × Y].
Proof. unfold second; cat. Qed.

Hint Rewrite @second_id : categories.

Theorem second_comp {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  second (Z:=W) (f ∘ g) ≈ second f ∘ second g.
Proof.
  unfold second.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem second_fork {X Y Z W : C} (f : X ~> Y) (g : X ~> Z) (h : Z ~> W) :
  second h ∘ f △ g ≈ f △ (h ∘ g).
Proof.
  unfold second.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Corollary exl_first {X Y Z : C} (f : X ~> Y) :
  @exl _ Y Z ∘ first f ≈ f ∘ exl.
Proof. unfold first; cat. Qed.

Hint Rewrite @exl_first : categories.

Corollary exr_first {X Y Z : C} (f : X ~> Y) :
  @exr _ Y Z ∘ first f ≈ exr.
Proof. unfold first; cat. Qed.

Hint Rewrite @exr_first : categories.

Corollary exl_second {X Y Z : C} (f : X ~> Y) :
  @exl _ Z Y ∘ second f ≈ exl.
Proof. unfold second; cat. Qed.

Hint Rewrite @exl_second : categories.

Corollary exr_second {X Y Z : C} (f : X ~> Y) :
  @exr _ Z Y ∘ second f ≈ f ∘ exr.
Proof. unfold second; cat. Qed.

Hint Rewrite @exr_second : categories.

Theorem swap_first {X Y Z : C} (f : X ~> Y) :
  swap ∘ first (Z:=Z) f ≈ second f ∘ swap.
Proof.
  unfold first, second, swap.
  rewrite <- fork_comp; cat.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem swap_second {X Y Z : C} (f : X ~> Y) :
  swap ∘ second f ≈ first (Z:=Z) f ∘ swap.
Proof.
  unfold first, second, swap.
  rewrite <- fork_comp; cat.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem first_second {X Y Z W : C} (f : X ~> Y) (g : Z ~> W) :
  first f ∘ second g ≈ second g ∘ first f.
Proof.
  unfold second.
  rewrite first_fork.
  unfold first.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
Qed.

Theorem swap_fork {X Y Z : C} (f : X ~> Y) (g : X ~> Z) :
  swap ∘ f △ g ≈ g △ f.
Proof.
  unfold swap.
  rewrite <- fork_comp; cat.
Qed.

Theorem split_id {X Y : C} :
  split (id[X]) (id[Y]) ≈ id[X × Y].
Proof.
  unfold split.
  rewrite first_id, second_id; cat.
Qed.

Hint Rewrite @split_id : categories.

Corollary fork_comp_hetero {X Y Z W : C}
          (f : Y ~> Z) (h : Y ~> W) (g i : X ~> Y) :
  (f ∘ g) △ (h ∘ i) ≈ split f h ∘ g △ i.
Proof.
  unfold split; intros.
  unfold first, second.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Context `{@Terminal C}.

Global Program Instance prod_one_l  {X : C} :
  1 × X ≅ X := {
  to   := exr;
  from := one △ id
}.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
Qed.

Hint Rewrite @prod_one_l : isos.

Global Program Instance prod_one_r  {X : C} :
  X × 1 ≅ X := {
  to   := exl;
  from := id △ one
}.
Next Obligation.
  rewrite <- fork_comp; cat.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
Qed.

Hint Rewrite @prod_one_r : isos.

Global Program Instance prod_assoc  {X Y Z : C} :
  (X × Y) × Z ≅ X × (Y × Z) := {
  to   := (exl ∘ exl) △ ((exr ∘ exl) △ exr);
  from := (exl △ (exl ∘ exr)) △ (exr ∘ exr)
}.
Next Obligation.
  rewrite <- !fork_comp; cat;
  rewrite <- comp_assoc; cat;
  rewrite <- comp_assoc; cat;
  rewrite fork_comp; cat.
Qed.
Next Obligation.
  rewrite <- !fork_comp; cat;
  rewrite <- comp_assoc; cat;
  rewrite <- comp_assoc; cat;
  rewrite fork_comp; cat.
Qed.

End Cartesian.

Infix "×" := (@Prod _ _) : category_scope.
Notation "X ×[ C ] Y" := (@Prod C _ X Y)
  (at level 40, only parsing) : category_scope.
Infix "△" := (@fork _ _ _ _ _) (at level 28) : category_scope.

Hint Rewrite @exl_fork : categories.
Hint Rewrite @exr_fork : categories.
Hint Rewrite @fork_exl_exr : categories.
Hint Rewrite @swap_invol : categories.
Hint Rewrite @prod_one_l : isos.
Hint Rewrite @prod_one_r : isos.
