Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

Reserved Infix "×" (at level 41, right associativity).

Section Cartesian.

Context `{C : Category}.

Class IsCartesianProduct (x y z : C) := {
    exl : z ~> x;
    exr : z ~> y;
    fork {a} (f : a ~> x) (g : a ~> y) : a ~> z;
    fork_respects : ∀ a,
      Proper (equiv ==> equiv ==> equiv) (@fork a);    
    ump_products {a} (f : a ~> x) (g : a ~> y) (h : a ~> z) :
    h ≈ fork f g ↔ (exl ∘ h ≈ f) * (exr ∘ h ≈ g)
  }.

#[refine]
Instance CartesianProductStructureEquiv x y z : Setoid (IsCartesianProduct x y z) :=
  Build_Setoid _
    (fun p q => (@exl _ _ _ p ≈ @exl _ _ _ q) * (@exr _ _ _ p ≈ @exr _ _ _ q))
    (Build_Equivalence
      _ _ _ _ ).
Proof.
  all: try(typeclasses eauto).
  + abstract(intro; split; reflexivity).
  + abstract(cat_simpl).
  + abstract(cat_simpl).
Defined.

Arguments fork {x y z _ a}.
Class Cartesian := {
  product_obj : obj → obj → obj
    where "x × y" := (product_obj x y);

  isCartesianProduct {x y} : IsCartesianProduct x y (x × y)
  
  (* fork {x y z} (f : x ~> y) (g : x ~> z) : x ~> y × z; *)

  (* exl {x y} : x × y ~> x; *)
  (* exr {x y} : x × y ~> y; *)

  (* fork_respects : ∀ x y z, *)
  (*   Proper (equiv ==> equiv ==> equiv) (@fork x y z); *)

  (* ump_products {x y z} (f : x ~> y) (g : x ~> z) (h : x ~> y × z) : *)
  (*   h ≈ fork f g ↔ (exl ∘ h ≈ f) * (exr ∘ h ≈ g) *)
}.

#[export] Existing Instance fork_respects.
#[export] Existing Instance isCartesianProduct.

Infix "×" := product_obj (at level 41, right associativity) : object_scope.
Infix "△" := fork (at level 28) : morphism_scope.

Context `{@Cartesian}.

Definition first  {x y z : C} (f : x ~> y) : x × z ~> y × z :=
  (f ∘ exl) △ exr.

Definition second  {x y z : C} (f : x ~> y) : z × x ~> z × y :=
  exl △ (f ∘ exr).

Definition split  {x y z w : C} (f : x ~> y) (g : z ~> w) :
  x × z ~> y × w :=
  (f ∘ exl) △ (g ∘ exr).

#[export] Program Instance first_respects {a b c : C} :
  Proper (equiv ==> equiv) (@first a b c).
Next Obligation.
  proper.
  unfold first.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance second_respects {a b c : C} :
  Proper (equiv ==> equiv) (@second a b c).
Next Obligation.
  proper.
  unfold second.
  rewrites.
  reflexivity.
Qed.

#[export] Program Instance split_respects {a b c d : C} :
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
  now apply (ump_products f g (f △ g)).
Qed.

#[local] Hint Rewrite @exl_fork : categories.

Corollary exr_fork {x z w : C} (f : x ~> z) (g : x ~> w) :
  exr ∘ f △ g ≈ g.
Proof.
  intros.
  now apply (ump_products f g (f △ g)).
Qed.

#[local] Hint Rewrite @exr_fork : categories.

Corollary exl_fork_assoc {x y z w} (f : x ~> z) (g : z ~> w) (h : x ~> y) :
  g ∘ exl ∘ (f △ h) ≈ g ∘ f.
Proof.
  rewrite <- comp_assoc.
  apply compose_respects; try reflexivity.
  apply exl_fork.
Qed.

Corollary exr_fork_assoc {x y z w} (f : x ~> z) (g : y ~> w) (h : x ~> y) :
  g ∘ exr ∘ (f △ h) ≈ g ∘ h.
Proof.
  rewrite <- comp_assoc.
  apply compose_respects; try reflexivity.
  apply exr_fork.
Qed.

Corollary exl_fork_comp {x y z w} (f : x ~> y) (g : x ~> z) (h : w ~> x) :
  exl ∘ ((f △ g) ∘ h) ≈ f ∘ h.
Proof.
  rewrite comp_assoc.
  rewrite exl_fork.
  reflexivity.
Qed.

Corollary exr_fork_comp {x y z w} (f : x ~> y) (g : x ~> z) (h : w ~> x) :
  exr ∘ ((f △ g) ∘ h) ≈ g ∘ h.
Proof.
  rewrite comp_assoc.
  rewrite exr_fork.
  reflexivity.
Qed.

Corollary fork_exl_exr {x y : C} :
  exl △ exr ≈ @id C (x × y).
Proof.
  intros.
  symmetry.
  apply ump_products; split; cat.
Qed.

#[local] Hint Rewrite @fork_exl_exr : categories.

Corollary fork_inv {x y z : C} (f h : x ~> y) (g i : x ~> z) :
  f △ g ≈ h △ i ↔ f ≈ h ∧ g ≈ i.
Proof.
  pose proof (ump_products h i (f △ g)) as HA;
  simplify; intuition.
  - now rewrite exl_fork in a.
  - now rewrite exr_fork in b.
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

#[local] Obligation Tactic := cat_simpl; unfork.

Definition swap_invol {x y : C} :
  swap ∘ swap ≈ @id C (x × y).
Proof. unfork. Qed.

#[local] Hint Rewrite @swap_invol : categories.

Definition swap_inj_l {x y z : C} (f g : x ~> y × z) :
  swap ∘ f ≈ swap ∘ g → f ≈ g.
Proof.
  intro HA.
  rewrite <- id_left.
  rewrite <- (id_left g).
  rewrite <- swap_invol.
  rewrite <- !comp_assoc.
  now apply compose_respects.
Qed.

Definition swap_inj_r {x y z : C} (f g : x × y ~> z) :
  f ∘ swap ≈ g ∘ swap → f ≈ g.
Proof.
  intro HA.
  rewrite <- id_right.
  rewrite <- (id_right g).
  rewrite <- swap_invol.
  rewrite !comp_assoc.
  now apply compose_respects.
Qed.

Theorem first_id {x y : C} :
  first (id[x]) ≈ id[x × y].
Proof. unfold first; cat. Qed.

#[local] Hint Rewrite @first_id : categories.

Theorem first_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  first (z:=w) (f ∘ g) ≈ first f ∘ first g.
Proof. unfork. Qed.

Theorem first_fork {x y z w : C} (f : x ~> y) (g : x ~> z) (h : y ~> w) :
  first h ∘ f △ g ≈ (h ∘ f) △ g.
Proof. unfork. Qed.

Theorem second_id {x y : C} :
  second (id[y]) ≈ id[x × y].
Proof. unfold second; cat. Qed.

#[local] Hint Rewrite @second_id : categories.

Theorem second_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  second (z:=w) (f ∘ g) ≈ second f ∘ second g.
Proof. unfork. Qed.

Theorem second_fork {x y z w : C} (f : x ~> y) (g : x ~> z) (h : z ~> w) :
  second h ∘ f △ g ≈ f △ (h ∘ g).
Proof. unfork. Qed.

Corollary exl_first {x y z : C} (f : x ~> y) :
  @exl y z _ _  ∘ first f ≈ f ∘ exl.
Proof. unfold first; cat. Qed.

#[local] Hint Rewrite @exl_first : categories.

Corollary exr_first {x y z : C} (f : x ~> y) :
  @exr y z _ _ ∘ first f ≈ exr.
Proof. unfold first; cat. Qed.

#[local] Hint Rewrite @exr_first : categories.

Corollary exl_second {x y z : C} (f : x ~> y) :
  @exl z y _ _ ∘ second f ≈ exl.
Proof. unfold second; cat. Qed.

#[local] Hint Rewrite @exl_second : categories.

Corollary exr_second {x y z : C} (f : x ~> y) :
  @exr z y _ _ ∘ second f ≈ f ∘ exr.
Proof. unfold second; cat. Qed.

#[local] Hint Rewrite @exr_second : categories.

Theorem swap_first {x y z : C} (f : x ~> y) :
  swap ∘ first (z:=z) f ≈ second f ∘ swap.
Proof. unfork. Qed.

Theorem swap_second {x y z : C} (f : x ~> y) :
  swap ∘ second f ≈ first (z:=z) f ∘ swap.
Proof. unfork. Qed.

Theorem first_second {x y z w : C} (f : x ~> y) (g : z ~> w) :
  first f ∘ second g ≈ second g ∘ first f.
Proof. unfork. Qed.

Theorem swap_fork {x y z : C} (f : x ~> y) (g : x ~> z) :
  swap ∘ f △ g ≈ g △ f.
Proof. unfork. Qed.

Theorem split_id {x y : C} :
  split (id[x]) (id[y]) ≈ id[x × y].
Proof. unfork; cat. Qed.

#[local] Hint Rewrite @split_id : categories.

Theorem split_comp {x y z w v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) (i : w ~> v) :
  split f g ∘ split h i ≈ split (f ∘ h) (g ∘ i).
Proof. unfork. Qed.

Theorem split_first {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  split f g ∘ first h ≈ split (f ∘ h) g.
Proof. unfork. Qed.

Theorem first_split {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  first f ∘ split h g ≈ split (f ∘ h) g.
Proof. unfork. Qed.

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
Proof. unfork. Qed.

#[export] Program Instance prod_respects_iso :
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

#[export] Program Instance prod_one_l  {x : C} :
  1 × x ≅ x := {
  to   := exr;
  from := one △ id
}.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
  apply one_unique.
Qed.

#[local] Hint Rewrite @prod_one_l : isos.

#[export] Program Instance prod_one_r  {x : C} :
  x × 1 ≅ x := {
  to   := exl;
  from := id △ one
}.
Next Obligation.
  rewrite <- fork_comp; cat.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
  apply one_unique.
Qed.

#[local] Hint Rewrite @prod_one_r : isos.

#[export] Program Instance prod_comm  {x y : C} :
  x × y ≅ y × x := {
  to   := swap;
  from := swap
}.

#[export] Program Instance prod_assoc  {x y z : C} :
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

Infix "×" := (@product_obj _ _) (at level 41, right associativity) : object_scope.
Notation "x ×[ C ] y" := (@product_obj C _ x y)
  (at level 41, right associativity, only parsing) : object_scope.

Infix "△" := (@fork _ _ _ _ _ _) (at level 28) : morphism_scope.

#[export] Hint Rewrite @exl_fork : categories.
#[export] Hint Rewrite @exr_fork : categories.
#[export] Hint Rewrite @fork_exl_exr : categories.
#[export] Hint Rewrite @swap_invol : categories.
#[export] Hint Rewrite @prod_one_l : isos.
#[export] Hint Rewrite @prod_one_r : isos.

Ltac unfork :=
  unfold swap, split, first, second; simpl;
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
