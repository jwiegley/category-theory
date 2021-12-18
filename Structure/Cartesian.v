Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

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
  product_obj : obj -> obj -> obj
    where "x × y" := (product_obj x y);

  fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y × z;
  exl  {x y} : x × y ~> x;
  exr  {x y} : x × y ~> y;

  fork_respects :> ∀ x y z,
    Proper (equiv ==> equiv ==> equiv) (@fork x y z);

  ump_products {x y z} (f : x ~> y) (g : x ~> z) (h : x ~> y × z) :
    h ≈ fork f g ↔ (exl ∘ h ≈ f) * (exr ∘ h ≈ g)
}.

Infix "×" := product_obj (at level 40, left associativity) : object_scope.
Infix "△" := fork (at level 28) : morphism_scope.

Context `{@Cartesian}.

Definition first  {x y z : C} (f : x ~> y) : x × z ~> y × z :=
  (f ∘ exl) △ exr.

Definition second  {x y z : C} (f : x ~> y) : z × x ~> z × y :=
  exl △ (f ∘ exr).

Definition split  {x y z w : C} (f : x ~> y) (g : z ~> w) :
  x × z ~> y × w :=
  (f ∘ exl) △ (g ∘ exr).

Global Program Instance parametric_morphism_first {a b c : C} :
  Proper (equiv ==> equiv) (@first a b c).
Next Obligation.
  proper.
  unfold first.
  rewrites.
  reflexivity.
Qed.

Global Program Instance parametric_morphism_second {a b c : C} :
  Proper (equiv ==> equiv) (@second a b c).
Next Obligation.
  proper.
  unfold second.
  rewrites.
  reflexivity.
Qed.

Global Program Instance split_respects {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@split a b c d).
Next Obligation.
  proper.
  unfold split.
  rewrites.
  reflexivity.
Qed.

Definition swap {x y : C} : x × y ~> y × x := exr △ exl.

Corollary exl_fork {x z w : C} (f : x ~> z) (g : x ~> w) :
  exl ∘ f △ g ≈ f.
Proof.
  intros.
  apply (ump_products f g (f △ g)).
  reflexivity.
Qed.

Hint Rewrite @exl_fork : categories.

Corollary exr_fork {x z w : C} (f : x ~> z) (g : x ~> w) :
  exr ∘ f △ g ≈ g.
Proof.
  intros.
  apply (ump_products f g (f △ g)).
  reflexivity.
Qed.

Hint Rewrite @exr_fork : categories.

Corollary fork_exl_exr {x y : C} :
  exl △ exr ≈ @id C (x × y).
Proof.
  intros.
  symmetry.
  apply ump_products; split; cat.
Qed.

Hint Rewrite @fork_exl_exr : categories.

Corollary fork_inv {x y z : C} (f h : x ~> y) (g i : x ~> z) :
  f △ g ≈ h △ i ↔ f ≈ h ∧ g ≈ i.
Proof.
  pose proof (ump_products h i (f △ g)) as HA;
  simplify; intuition.
  - rewrite exl_fork in a.
    assumption.
  - rewrite exr_fork in b.
    assumption.
  - apply X0; cat.
Qed.

Corollary fork_comp {x y z w : C}
          (f : y ~> z) (h : y ~> w) (g : x ~> y) :
  (f ∘ g) △ (h ∘ g) ≈ f △ h ∘ g.
Proof.
  intros.
  symmetry.
  apply ump_products; split;
  rewrite !comp_assoc; cat.
Qed.

Ltac unfork :=
  unfold swap, split, first, second; simpl;
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).

Ltac fork_simpl :=
  match goal with
  | |- _ ∘ _ ∘ _ ≈ _ =>
    rewrite comp_assoc_sym
  | |- id{_} ∘ _ ≈ _ =>
    rewrite id_left
  | |- _ ∘ id{_} ≈ _ =>
    rewrite id_right
  | |- exl ∘ exl △ _ ≈ _ =>
    apply exl_fork
  | |- exl ∘ exr △ _ ≈ _ =>
    apply exl_fork
  | |- exl ∘ _ △ _ ≈ _ =>
    rewrite exl_fork
  | |- exr ∘ _ △ _ ≈ _ =>
    rewrite exr_fork
  | |- _ △ _ ∘ _ ≈ _ =>
    rewrite <- fork_comp
  | |- (exl △ exr) △ _ ≈ _ =>
    etransitivity;
      [apply fork_respects; [apply fork_exl_exr|reflexivity]|]
  | |- _ △ (exl △ exr) ≈ _ =>
    etransitivity;
      [apply fork_respects; [reflexivity|apply fork_exl_exr]|]
  | |- _ △ _ ≈ _ △ _ => apply fork_respects
  end.

Local Obligation Tactic := cat_simpl; try unfork.

Definition swap_invol {x y : C} :
  swap ∘ swap ≈ @id C (x × y).
Proof.
  unfold swap. repeat fork_simpl.
  etransitivity.
  { apply fork_respects; fork_simpl.
    reflexivity.
  }
  apply fork_exl_exr.
Qed.

Hint Rewrite @swap_invol : categories.

Definition swap_inj_l {x y z : C} (f g : x ~> y × z) :
  swap ∘ f ≈ swap ∘ g -> f ≈ g.
Proof.
  intro HA.
  rewrite <- id_left.
  rewrite <- (id_left g).
  rewrite <- swap_invol.
  rewrite <- !comp_assoc.
  apply compose_respects; try reflexivity.
  assumption.
Qed.

Definition swap_inj_r {x y z : C} (f g : x × y ~> z) :
  f ∘ swap ≈ g ∘ swap -> f ≈ g.
Proof.
  intro HA.
  rewrite <- id_right.
  rewrite <- (id_right g).
  rewrite <- swap_invol.
  rewrite !comp_assoc.
  apply compose_respects; try reflexivity.
  assumption.
Qed.

Theorem first_id {x y : C} :
  first (id[x]) ≈ id[x × y].
Proof. unfold first; cat. Qed.

Hint Rewrite @first_id : categories.

Theorem first_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  first (z:=w) (f ∘ g) ≈ first f ∘ first g.
Proof.
  unfold first.
  symmetry.
  repeat fork_simpl; [|reflexivity].
  symmetry.
  fork_simpl.
  apply compose_respects; [reflexivity|].
  symmetry.
  fork_simpl.
  reflexivity.
Qed.

Theorem first_fork {x y z w : C} (f : x ~> y) (g : x ~> z) (h : y ~> w) :
  first h ∘ f △ g ≈ (h ∘ f) △ g.
Proof.
  unfold first.
  repeat fork_simpl; [|reflexivity].
  apply compose_respects; [reflexivity|].
  repeat fork_simpl.
  reflexivity.
Qed.

Theorem second_id {x y : C} :
  second (id[y]) ≈ id[x × y].
Proof. unfold second; cat. Qed.

Hint Rewrite @second_id : categories.

Theorem second_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  second (z:=w) (f ∘ g) ≈ second f ∘ second g.
Proof.
  unfold second.
  symmetry.
  repeat fork_simpl.
  symmetry.
  repeat fork_simpl.
  apply compose_respects; [reflexivity|].
  symmetry.
  repeat fork_simpl.
  reflexivity.
Qed.

Theorem second_fork {x y z w : C} (f : x ~> y) (g : x ~> z) (h : z ~> w) :
  second h ∘ f △ g ≈ f △ (h ∘ g).
Proof.
  unfold second.
  repeat fork_simpl; [reflexivity|].
  repeat fork_simpl.
  apply compose_respects; [reflexivity|].
  repeat fork_simpl.
  reflexivity.
Qed.

Corollary exl_first {x y z : C} (f : x ~> y) :
  @exl _ y z ∘ first f ≈ f ∘ exl.
Proof. unfold first; cat. Qed.

Hint Rewrite @exl_first : categories.

Corollary exr_first {x y z : C} (f : x ~> y) :
  @exr _ y z ∘ first f ≈ exr.
Proof. unfold first; cat. Qed.

Hint Rewrite @exr_first : categories.

Corollary exl_second {x y z : C} (f : x ~> y) :
  @exl _ z y ∘ second f ≈ exl.
Proof. unfold second; cat. Qed.

Hint Rewrite @exl_second : categories.

Corollary exr_second {x y z : C} (f : x ~> y) :
  @exr _ z y ∘ second f ≈ f ∘ exr.
Proof. unfold second; cat. Qed.

Hint Rewrite @exr_second : categories.

Theorem swap_first {x y z : C} (f : x ~> y) :
  swap ∘ first (z:=z) f ≈ second f ∘ swap.
Proof.
  unfold swap, first, second.
  repeat fork_simpl.
  symmetry.
  repeat fork_simpl.
  - symmetry.
    fork_simpl.
    reflexivity.
  - symmetry. fork_simpl.
    apply compose_respects; [reflexivity|].
    symmetry. fork_simpl.
    reflexivity.
Qed.

Theorem swap_second {x y z : C} (f : x ~> y) :
  swap ∘ second f ≈ first (z:=z) f ∘ swap.
Proof.
  unfold swap, first, second.
  repeat fork_simpl.
  symmetry.
  repeat fork_simpl.
  - symmetry.
    fork_simpl.
    apply compose_respects; [reflexivity|].
    symmetry. fork_simpl.
  - symmetry. fork_simpl.
Qed.

Theorem first_second {x y z w : C} (f : x ~> y) (g : z ~> w) :
  first f ∘ second g ≈ second g ∘ first f.
Proof.
  unfold first, second.
  repeat fork_simpl.
  symmetry.
  repeat fork_simpl.
  - symmetry.
    repeat fork_simpl.
    apply compose_respects; [reflexivity|].
    repeat fork_simpl.
  - symmetry.
    repeat fork_simpl.
    apply compose_respects; [reflexivity|].
    symmetry. repeat fork_simpl.
    reflexivity.
Qed.

Theorem swap_fork {x y z : C} (f : x ~> y) (g : x ~> z) :
  swap ∘ f △ g ≈ g △ f.
Proof.
  unfold swap.
  repeat fork_simpl; reflexivity.
Qed.

Theorem split_id {x y : C} :
  split (id[x]) (id[y]) ≈ id[x × y].
Proof.
  unfold split.
  etransitivity.
  { apply fork_respects; apply id_left. }
  apply fork_exl_exr.
Qed.

Hint Rewrite @split_id : categories.

Theorem split_comp {x y z w v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) (i : w ~> v) :
  split f g ∘ split h i ≈ split (f ∘ h) (g ∘ i).
Proof.
  unfold split.
  repeat fork_simpl; symmetry; fork_simpl.
  all: apply compose_respects; [reflexivity|].
  all: symmetry.
  all: fork_simpl.
  all: reflexivity.
Qed.

Theorem split_first {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  split f g ∘ first h ≈ split (f ∘ h) g.
Proof.
  unfold split, first.
  repeat fork_simpl; symmetry; try fork_simpl.
  all: apply compose_respects; [reflexivity|].
  all: symmetry.
  all: fork_simpl.
  all: reflexivity.
Qed.

Theorem first_split {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  first f ∘ split h g ≈ split (f ∘ h) g.
Proof.
  unfold split, first.
  repeat fork_simpl; [|reflexivity].
  symmetry; fork_simpl.
  apply compose_respects; [reflexivity|].
  symmetry. fork_simpl.
  reflexivity.
Qed.

Theorem split_second {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  split g f ∘ second h ≈ split g (f ∘ h).
Proof. unfork. Qed.

Theorem second_split {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  second f ∘ split g h ≈ split g (f ∘ h).
Proof. unfork. Qed.

Theorem exl_split {x y z w : C} (f : x ~> y) (g : z ~> w):
  exl ∘ split f g ≈ f ∘ exl.
Proof. unfork; cat. Qed.

Theorem exr_split {x y z w : C} (f : x ~> y) (g : z ~> w):
  exr ∘ split f g ≈ g ∘ exr.
Proof. unfork; cat. Qed.

Theorem split_fork {x y z w v : C}
          (f : y ~> w) (h : z ~> v) (g : x ~> y) (i : x ~> z):
  split f h ∘ g △ i ≈ (f ∘ g) △ (h ∘ i).
Proof. unfold split; intros; unfork. Qed.

Global Program Instance prod_respects_iso :
  Proper (Isomorphism ==> Isomorphism ==> Isomorphism) product_obj.
Next Obligation.
  proper.
  construct.
  - exact (split (to X) (to X0)).
  - exact (split (from X) (from X0)).
  - now rewrite split_comp, !iso_to_from, split_id.
  - now rewrite split_comp, !iso_from_to, split_id.
Defined.

Context `{@Terminal C}.

Global Program Instance prod_one_l  {x : C} :
  1 × x ≅ x := {
  to   := exr;
  from := one △ id
}.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
Qed.

Hint Rewrite @prod_one_l : isos.

Global Program Instance prod_one_r  {x : C} :
  x × 1 ≅ x := {
  to   := exl;
  from := id △ one
}.
Next Obligation.
  rewrite <- fork_comp; cat.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
Qed.

Hint Rewrite @prod_one_r : isos.

Global Program Instance prod_comm  {x y : C} :
  x × y ≅ y × x := {
  to   := swap;
  from := swap
}.

Global Program Instance prod_assoc  {x y z : C} :
  (x × y) × z ≅ x × (y × z) := {
  to   := (exl ∘ exl) △ ((exr ∘ exl) △ exr);
  from := (exl △ (exl ∘ exr)) △ (exr ∘ exr)
}.
Next Obligation. rewrite fork_comp; cat. Qed.
Next Obligation. rewrite fork_comp; cat. Qed.

Definition toggle {x y : C} : (x × y) × (x × y) ~> (x × x) × (y × y) :=
  split exl exl △ split exr exr.

(* Theorem toggle_fork_fork : *)
(*   toggle ∘ (f △ g) △ (h △ i) ≈  *)

End Cartesian.

Infix "×" := (@product_obj _ _) (at level 40, left associativity) : object_scope.
Notation "x ×[ C ] y" := (@product_obj C _ x y)
  (at level 40, left associativity, only parsing) : object_scope.
Infix "△" := (@fork _ _ _ _ _) (at level 28) : morphism_scope.

#[global]
Hint Rewrite @exl_fork : categories.
#[global]
Hint Rewrite @exr_fork : categories.
#[global]
Hint Rewrite @fork_exl_exr : categories.
#[global]
Hint Rewrite @swap_invol : categories.
#[global]
Hint Rewrite @prod_one_l : isos.
#[global]
Hint Rewrite @prod_one_r : isos.

Ltac unfork :=
  unfold swap, split, first, second; simpl;
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).

Ltac fork_simpl :=
  match goal with
  | |- _ ∘ _ ∘ _ ≈ _ =>
    rewrite comp_assoc_sym
  | |- id{_} ∘ _ ≈ _ =>
    rewrite id_left
  | |- _ ∘ id{_} ≈ _ =>
    rewrite id_right
  | |- exl ∘ exl △ _ ≈ _ =>
    apply exl_fork
  | |- exl ∘ exr △ _ ≈ _ =>
    apply exl_fork
  | |- exl ∘ _ △ _ ≈ _ =>
    rewrite exl_fork
  | |- exr ∘ _ △ _ ≈ _ =>
    rewrite exr_fork
  | |- _ △ _ ∘ _ ≈ _ =>
    rewrite <- fork_comp
  | |- (exl △ exr) △ _ ≈ _ =>
    eapply transitivity;
      [apply fork_respects; [apply fork_exl_exr|reflexivity]|]
  | |- _ △ (exl △ exr) ≈ _ =>
    eapply transitivity;
      [apply fork_respects; [reflexivity|apply fork_exl_exr]|]
  | |- _ △ _ ≈ _ △ _ => apply fork_respects
  end.
