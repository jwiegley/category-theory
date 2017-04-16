Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Structure.Initial.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Cocartesian.

Context `{C : Category}.

Class Cocartesian := {
  Coprod : ob -> ob -> ob
    where "X + Y" := (Coprod X Y);

  merge {X Y Z} (f : Y ~> X) (g : Z ~> X) : Y + Z ~> X;
  inl   {X Y} : X ~> X + Y;
  inr   {X Y} : Y ~> X + Y;

  merge_respects {X Y Z} :> Proper (equiv ==> equiv ==> equiv) (@merge X Y Z);

  ump_coproducts {X Y Z} (f : Y ~> X) (g : Z ~> X) (h : Y + Z ~> X) :
    h ≈ merge f g <<>> h ∘ inl ≈ f //\\ h ∘ inr ≈ g
}.

Infix "+" := Coprod : category_scope.
Infix "▽" := merge (at level 26) : category_scope.

Context `{@Cocartesian}.

Definition left  {X Y Z : C} (f : X ~> Y) : X + Z ~> Y + Z :=
  (inl ∘ f) ▽ inr.

Definition right  {X Y Z : C} (f : X ~> Y) : Z + X ~> Z + Y :=
  inl ▽ (inr ∘ f).

Definition cover  {X Y Z W : C} (f : X ~> Y) (g : Z ~> W) :
  X + Z ~> Y + W :=
  (inl ∘ f) ▽ (inr ∘ g).

Global Program Instance parametric_morphism_left {a b c : C} :
  Proper (equiv ==> equiv) (@left a b c).
Obligation 1.
  intros ?? HA.
  unfold left.
  rewrite HA.
  reflexivity.
Qed.

Global Program Instance parametric_morphism_right {a b c : C} :
  Proper (equiv ==> equiv) (@right a b c).
Obligation 1.
  intros ?? HA.
  unfold right.
  rewrite HA.
  reflexivity.
Qed.

Global Program Instance parametric_morphism_cover {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@cover a b c d).
Obligation 1.
  intros ?? HA ?? HB.
  unfold cover.
  rewrite HA, HB.
  reflexivity.
Qed.

Definition twist {X Y : C} : X + Y ~> Y + X := inr ▽ inl.

Corollary inl_merge {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inl ≈ f.
Proof.
  intros.
  apply (ump_coproducts f g (f ▽ g)).
  reflexivity.
Qed.

Hint Rewrite @inl_merge : categories.

Corollary inr_merge {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inr ≈ g.
Proof.
  intros.
  apply (ump_coproducts f g (f ▽ g)).
  reflexivity.
Qed.

Hint Rewrite @inr_merge : categories.

Corollary merge_inl_inr {X Y : C} :
  inl ▽ inr ≈ @id C (X + Y).
Proof.
  intros.
  symmetry.
  apply ump_coproducts; split; cat.
Qed.

Hint Rewrite @merge_inl_inr : categories.

Corollary merge_inv {X Y Z : C} (f h : Y ~> X) (g i : Z ~> X) :
  f ▽ g ≈ h ▽ i <<>> f ≈ h //\\ g ≈ i.
Proof.
  pose proof (ump_coproducts h i (f ▽ g)) as Huniv.
  firstorder.
  - rewrite <- H0; cat.
  - rewrite <- H3; cat.
  - rewrite H2, H3; reflexivity.
Qed.

Corollary merge_comp {X Y Z W : C} (f : Y ~> Z) (h : W ~> Z) (g : Z ~> X) :
  (g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h.
Proof.
  intros.
  symmetry.
  apply ump_coproducts; split;
  rewrite <- !comp_assoc; cat.
Qed.

Theorem left_comp {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  left (Z:=W) (f ∘ g) ≈ left f ∘ left g.
Proof.
  unfold left.
  rewrite <- merge_comp; cat.
  rewrite !comp_assoc; cat.
Qed.

Theorem left_fork {X Y Z W : C} (f : Y ~> X) (g : Z ~> X) (h : W ~> Y) :
  f ▽ g ∘ left h ≈ (f ∘ h) ▽ g.
Proof.
  unfold left.
  rewrite <- merge_comp; cat.
  rewrite !comp_assoc; cat.
Qed.

Theorem right_comp {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  right (Z:=W) (f ∘ g) ≈ right f ∘ right g.
Proof.
  unfold right.
  rewrite <- merge_comp; cat.
  rewrite !comp_assoc; cat.
Qed.

Theorem right_fork {X Y Z W : C} (f : Y ~> X) (g : Z ~> X) (h : W ~> Z) :
  f ▽ g ∘ right h ≈ f ▽ (g ∘ h).
Proof.
  unfold right.
  rewrite <- merge_comp; cat.
  rewrite !comp_assoc; cat.
Qed.

Corollary inl_left {X Y Z : C} (f : X ~> Y) :
  left f ∘ @inl _ X Z ≈ inl ∘ f.
Proof. unfold left; cat. Qed.

Hint Rewrite @inl_left : categories.

Corollary inr_left {X Y Z : C} (f : X ~> Y) :
  left f ∘ @inr _ X Z ≈ inr.
Proof. unfold left; cat. Qed.

Hint Rewrite @inr_left : categories.

Corollary inl_right {X Y Z : C} (f : X ~> Y) :
  right f ∘ @inl _ Z X ≈ inl.
Proof. unfold right; cat. Qed.

Hint Rewrite @inl_right : categories.

Corollary inr_right {X Y Z : C} (f : X ~> Y) :
  right f ∘ @inr _ Z X ≈ inr ∘ f.
Proof. unfold right; cat. Qed.

Hint Rewrite @inr_right : categories.

Theorem twist_left {X Y Z : C} (f : X ~> Y) :
  twist ∘ left (Z:=Z) f ≈ right f ∘ twist.
Proof.
  unfold left, right, twist.
  rewrite <- merge_comp; cat.
  rewrite <- merge_comp; cat.
  rewrite !comp_assoc; cat.
Qed.

Theorem twist_right {X Y Z : C} (f : X ~> Y) :
  twist ∘ right f ≈ left (Z:=Z) f ∘ twist.
Proof.
  unfold left, right, twist.
  rewrite <- merge_comp; cat.
  rewrite <- merge_comp; cat.
  rewrite !comp_assoc; cat.
Qed.

Theorem left_right {X Y Z W : C} (f : X ~> Y) (g : Z ~> W) :
  left f ∘ right g ≈ right g ∘ left f.
Proof.
  unfold right.
  rewrite left_fork.
  unfold left.
  rewrite <- merge_comp; cat.
  rewrite comp_assoc; cat.
Qed.

Theorem twist_fork {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
  f ▽ g ∘ twist ≈ g ▽ f.
Proof.
  unfold twist.
  rewrite <- merge_comp; cat.
Qed.

Context `{@Initial C}.

Notation "0 + X" := (Coprod Zero X) (at level 30).
Notation "X + 0" := (Coprod X Zero) (at level 30).

Global Program Instance coprod_zero_l {X : C} :
  0 + X ≅ X := {
  to   := zero ▽ id;
  from := inr
}.
Next Obligation. cat. Qed.
Next Obligation.
  rewrite <- merge_comp; cat.
  rewrite <- merge_inl_inr.
  apply merge_respects; cat.
Qed.

Hint Rewrite @coprod_zero_l : isos.

Global Program Instance coprod_zero_r {X : C} :
  X + 0 ≅ X := {
  to   := id ▽ zero;
  from := inl
}.
Next Obligation. cat. Qed.
Next Obligation.
  rewrite <- merge_comp; cat.
  rewrite <- merge_inl_inr.
  apply merge_respects; cat.
Qed.

Hint Rewrite @coprod_zero_r : isos.

Global Program Instance coprod_assoc  {X Y Z : C} :
  (X + Y) + Z ≅ X + (Y + Z) := {
  to   := (inl ▽ (inr ∘ inl)) ▽ (inr ∘ inr);
  from := (inl ∘ inl) ▽ ((inl ∘ inr) ▽ inr)
}.
Next Obligation.
  rewrite <- !merge_comp; cat;
  rewrite comp_assoc; cat;
  rewrite comp_assoc; cat;
  rewrite merge_comp; cat.
Qed.
Next Obligation.
  rewrite <- !merge_comp; cat;
  rewrite comp_assoc; cat;
  rewrite comp_assoc; cat;
  rewrite merge_comp; cat.
Qed.

End Cocartesian.

Infix "+" := Coprod : category_scope.
Infix "▽" := merge (at level 26) : category_scope.

Notation "0 + X" := (Coprod Zero X) (at level 30).
Notation "X + 0" := (Coprod X Zero) (at level 30).

Hint Rewrite @inl_merge : categories.
Hint Rewrite @inr_merge : categories.
Hint Rewrite @merge_inl_inr : categories.
Hint Rewrite @coprod_zero_r : isos.
Hint Rewrite @coprod_zero_l : isos.

Section CocartesianFunctor.

Context `{F : C ⟶ D}.
Context `{@Cocartesian C}.
Context `{@Cocartesian D}.

Class CocartesianFunctor := {
  fobj_coprod_iso {X Y : C} : F (X + Y) ≅ F X + F Y;

  coprod_in  := fun X Y => from (@fobj_coprod_iso X Y);
  coprod_out := fun X Y => to   (@fobj_coprod_iso X Y);

  fmap_inl {X Y : C} : fmap (@inl C _ X Y) ≈ coprod_in _ _ ∘ inl;
  fmap_inr {X Y : C} : fmap (@inr C _ X Y) ≈ coprod_in _ _ ∘ inr;
  fmap_merge {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
    fmap (f ▽ g) ≈ fmap f ▽ fmap g ∘ coprod_out _ _
}.

Arguments coprod_in {_ _ _} /.
Arguments coprod_out {_ _ _} /.

Context `{@CocartesianFunctor}.

Corollary coprod_in_out {X Y : C} :
  coprod_in ∘ coprod_out ≈ @id _ (F (X + Y)).
Proof. apply iso_from_to. Qed.

Hint Rewrite @coprod_in_out : functors.

Corollary coprod_out_in {X Y : C} :
  coprod_out ∘ coprod_in ≈ @id _ (F X + F Y).
Proof. apply iso_to_from. Qed.

Hint Rewrite @coprod_out_in : functors.

Corollary coprod_in_surj {X Y Z : C} (f g : F (X + Y) ~> F X) :
  f ∘ coprod_in ≈ g ∘ coprod_in <<>> f ≈ g.
Proof.
  split; intros Hcoprod.
    rewrite <- id_right.
    rewrite <- coprod_in_out.
    rewrite comp_assoc.
    rewrite Hcoprod.
    rewrite <- comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hcoprod.
  reflexivity.
Qed.

Corollary coprod_out_inj {X Y Z : C} (f g : F Y + F Z ~> F X) :
  f ∘ coprod_out ≈ g ∘ coprod_out <<>> f ≈ g.
Proof.
  split; intros Hcoprod.
    rewrite <- id_right.
    rewrite <- coprod_out_in.
    rewrite comp_assoc.
    rewrite Hcoprod.
    rewrite <- comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hcoprod.
  reflexivity.
Qed.

End CocartesianFunctor.

Arguments coprod_in {_ _ _ _ _ _ _ _} /.
Arguments coprod_out {_ _ _ _ _ _ _ _} /.

Hint Rewrite @coprod_in_out : functors.
Hint Rewrite @coprod_out_in : functors.
