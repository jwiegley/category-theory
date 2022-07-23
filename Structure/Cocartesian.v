Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

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

Definition Coprod : C -> C -> C := @product_obj _ O.

Infix "+" := Coprod (at level 50, left associativity) : object_scope.

Definition merge {x y z : C} (f : y ~> x) (g : z ~> x) : y + z ~{C}~> x :=
  @fork _ O _ _ _ f g.

Infix "▽" := merge (at level 26) : morphism_scope.

#[global] Program Instance merge_respects {x y z} :
  Proper (equiv ==> equiv ==> equiv) (@merge x y z).
Next Obligation. apply (@fork_respects _ O). Qed.

Definition inl {x y : C} : x ~{C}~> x + y := @exl _ O _ _.
Definition inr {x y : C} : y ~{C}~> x + y := @exr _ O _ _.

Definition left  {x y z : C} (f : x ~> y) : x + z ~{C}~> y + z :=
  (inl ∘ f) ▽ inr.

Definition right  {x y z : C} (f : x ~> y) : z + x ~{C}~> z + y :=
  inl ▽ (inr ∘ f).

Definition cover  {x y z w : C} (f : x ~> y) (g : z ~> w) :
  x + z ~{C}~> y + w :=
  (inl ∘ f) ▽ (inr ∘ g).

#[global] Program Instance parametric_morphism_left {a b c : C} :
  Proper (equiv ==> equiv) (@left a b c).
Next Obligation. apply (@parametric_morphism_first _ O). Qed.

#[global] Program Instance parametric_morphism_right {a b c : C} :
  Proper (equiv ==> equiv) (@right a b c).
Next Obligation. apply (@parametric_morphism_second _ O). Qed.

#[global] Program Instance parametric_morphism_cover {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@cover a b c d).
Next Obligation.
  proper.
  unfold cover.
  rewrites.
  reflexivity.
Qed.

Definition paws {x y : C} : x + y ~{C}~> y + x := @swap _ O _ _.

Lemma inl_merge {x z w : C} (f : z ~> x) (g : w ~> x) :
  f ▽ g ∘ inl ≈ f.
Proof. apply (@exl_fork _ O). Qed.

#[local] Hint Rewrite @inl_merge : categories.

Lemma inr_merge {x z w : C} (f : z ~> x) (g : w ~> x) :
  f ▽ g ∘ inr ≈ g.
Proof. apply (@exr_fork _ O). Qed.

#[local] Hint Rewrite @inr_merge : categories.

Corollary merge_inl_inr {x y : C} :
  inl ▽ inr ≈ @id C (x + y).
Proof. apply (@fork_exl_exr _ O). Qed.

#[local] Hint Rewrite @merge_inl_inr : categories.

Corollary merge_inv {x y z : C} (f h : y ~> x) (g i : z ~> x) :
  f ▽ g ≈ h ▽ i ↔ (f ≈ h) * (g ≈ i).
Proof. apply (@fork_inv _ O). Qed.

Corollary merge_comp {x y z w : C} (f : y ~> z) (h : w ~> z) (g : z ~> x) :
  (g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h.
Proof. apply (@fork_comp _ O). Qed.

Ltac unmerge :=
  unfold paws, cover, left, right; simpl;
  repeat (rewrite <- !merge_comp; cat;
          rewrite <- !comp_assoc; cat).

#[local] Obligation Tactic := cat_simpl; unmerge.

Theorem left_id {x y : C} :
  left (id[x]) ≈ id[x + y].
Proof. unfold left; cat. Qed.

#[local] Hint Rewrite @left_id : categories.

Theorem left_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  left (z:=w) (f ∘ g) ≈ left f ∘ left g.
Proof. apply (@first_comp _ O). Qed.

Theorem left_fork {x y z w : C} (f : y ~> x) (g : z ~> x) (h : w ~> y) :
  f ▽ g ∘ left h ≈ (f ∘ h) ▽ g.
Proof. apply (@first_fork _ O). Qed.

Theorem right_id {x y : C} :
  right (id[y]) ≈ id[x + y].
Proof. unfold right; cat. Qed.

#[local] Hint Rewrite @right_id : categories.

Theorem right_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  right (z:=w) (f ∘ g) ≈ right f ∘ right g.
Proof. apply (@second_comp _ O). Qed.

Theorem right_fork {x y z w : C} (f : y ~> x) (g : z ~> x) (h : w ~> z) :
  f ▽ g ∘ right h ≈ f ▽ (g ∘ h).
Proof. apply (@second_fork _ O). Qed.

Corollary inl_left {x y z : C} (f : x ~> y) :
  left f ∘ @inl x z ≈ inl ∘ f.
Proof. apply (@exl_first _ O). Qed.

#[local] Hint Rewrite @inl_left : categories.

Corollary inr_left {x y z : C} (f : x ~> y) :
  left f ∘ @inr x z ≈ inr.
Proof. apply (@exr_first _ O). Qed.

#[local] Hint Rewrite @inr_left : categories.

Corollary inl_right {x y z : C} (f : x ~> y) :
  right f ∘ @inl z x ≈ inl.
Proof. apply (@exl_second _ O). Qed.

#[local] Hint Rewrite @inl_right : categories.

Corollary inr_right {x y z : C} (f : x ~> y) :
  right f ∘ @inr z x ≈ inr ∘ f.
Proof. apply (@exr_second _ O). Qed.

#[local] Hint Rewrite @inr_right : categories.

Theorem paws_left {x y z : C} (f : x ~> y) :
  paws ∘ left (z:=z) f ≈ right f ∘ paws.
Proof. symmetry; apply (@swap_second _ O y x z f). Qed.

Theorem paws_right {x y z : C} (f : x ~> y) :
  paws ∘ right f ≈ left (z:=z) f ∘ paws.
Proof. symmetry; apply (@swap_first _ O y x z f). Qed.

Theorem left_right {x y z w : C} (f : x ~> y) (g : z ~> w) :
  left f ∘ right g ≈ right g ∘ left f.
Proof. symmetry; apply (@first_second _ O). Qed.

Theorem paws_fork {x y z : C} (f : y ~> x) (g : z ~> x) :
  f ▽ g ∘ paws ≈ g ▽ f.
Proof. apply (@swap_fork _ O). Qed.

Definition paws_invol {x y : C} :
  paws ∘ paws ≈ @id C (x + y).
Proof. unfold paws; apply (@swap_invol _ O). Qed.

#[local] Hint Rewrite @paws_invol : categories.

Theorem cover_id {x y : C} :
  cover (id[x]) (id[y]) ≈ id[x + y].
Proof. now unmerge; cat. Qed.

#[local] Hint Rewrite @cover_id : categories.

Theorem cover_comp {x y z w v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) (i : w ~> v) :
  cover f g ∘ cover h i ≈ cover (f ∘ h) (g ∘ i).
Proof.
  unmerge.
  rewrite !comp_assoc.
  rewrite <- merge_comp.
  unfold cover.
  rewrite !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem cover_left {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  cover f g ∘ left h ≈ cover (f ∘ h) g.
Proof.
  unmerge.
  rewrite <- merge_comp.
  rewrite inr_merge.
  rewrite comp_assoc.
  rewrite inl_merge.
  rewrite comp_assoc.
  reflexivity.
Qed.

Theorem left_cover {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  left f ∘ cover h g ≈ cover (f ∘ h) g.
Proof.
  unmerge.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem cover_right {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  cover g f ∘ right h ≈ cover g (f ∘ h).
Proof.
  unmerge.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem right_cover {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  right f ∘ cover g h ≈ cover g (f ∘ h).
Proof.
  unmerge.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem cover_inl {x y z w : C} (f : x ~> y) (g : z ~> w):
  cover f g ∘ inl ≈ inl ∘ f.
Proof. unmerge; cat. Qed.

Theorem cover_inr {x y z w : C} (f : x ~> y) (g : z ~> w):
  cover f g ∘ inr ≈ inr ∘ g.
Proof. unmerge; cat. Qed.

#[global] Program Instance coprod_respects_iso :
  Proper (Isomorphism ==> Isomorphism ==> Isomorphism) Coprod.
Next Obligation.
  proper.
  construct.
  - exact (cover (to X) (to X0)).
  - exact (cover (from X) (from X0)).
  - now rewrite cover_comp, !iso_to_from, cover_id.
  - now rewrite cover_comp, !iso_from_to, cover_id.
Defined.

Context `{I : @Initial C}.

#[global] Program Instance coprod_zero_l {x : C} :
  0 + x ≅ x := {
  to   := zero ▽ id;
  from := inr
}.
Next Obligation. apply (@prod_one_l _ _ I). Qed.

#[local] Hint Rewrite @coprod_zero_l : isos.

#[global] Program Instance coprod_zero_r {x : C} :
  x + 0 ≅ x := {
  to   := id ▽ zero;
  from := inl
}.
Next Obligation. apply (@prod_one_r _ _ I). Qed.

#[local] Hint Rewrite @coprod_zero_r : isos.

#[global] Program Instance coprod_comm  {x y : C} :
  x + y ≅ y + x := {
  to   := paws;
  from := paws
}.

#[global] Program Instance coprod_assoc  {x y z : C} :
  (x + y) + z ≅ x + (y + z) := {
  to   := (inl ▽ (inr ∘ inl)) ▽ (inr ∘ inr);
  from := (inl ∘ inl) ▽ ((inl ∘ inr) ▽ inr)
}.
Next Obligation. apply (@prod_assoc _ O). Qed.
Next Obligation. apply (@prod_assoc _ O). Qed.

End Cocartesian_.

Infix "+" := Coprod (at level 50, left associativity) : object_scope.
Infix "▽" := merge (at level 26) : morphism_scope.

#[export] Hint Rewrite @inl_merge : categories.
#[export] Hint Rewrite @inr_merge : categories.
#[export] Hint Rewrite @merge_inl_inr : categories.
#[export] Hint Rewrite @coprod_zero_r : isos.
#[export] Hint Rewrite @coprod_zero_l : isos.

Ltac unmerge :=
  unfold paws, cover, left, right; simpl;
  repeat (rewrite <- !merge_comp; cat;
          rewrite <- !comp_assoc; cat).
