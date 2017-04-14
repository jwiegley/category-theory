Require Import Lib.
Require Export Initial.
Require Export Iso.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Cocartesian.

Context `{C : Category}.

Class Cocartesian := {
  Coprod : ob -> ob -> ob
    where "X + Y" := (Coprod X Y);

  merge {X Z W} (f : Z ~> X) (g : W ~> X) : Z + W ~> X;
  inl   {X Y} : X ~> X + Y;
  inr   {X Y} : Y ~> X + Y;

  merge_respects : ∀ X Z W,
    Proper (@eqv _ Z X ==> @eqv _ W X ==> @eqv _ (Z + W) X) merge;

  univ_coproducts {X Y Z} (f : Y ~> X) (g : Z ~> X) (h : Y + Z ~> X) :
    h ≈ merge f g <-> h ∘ inl ≈ f ∧ h ∘ inr ≈ g
}.

Infix "+" := Coprod : category_scope.
Infix "▽" := merge (at level 26) : category_scope.

Context `{@Cocartesian}.

Global Program Instance parametric_morphism_merge (a b c : C) :
  Proper (eqv ==> eqv ==> eqv) merge := merge_respects a b c.

Corollary inl_merge {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inl ≈ f.
Proof.
  intros.
  apply (proj1 (univ_coproducts f g (f ▽ g))).
  reflexivity.
Qed.

Hint Rewrite @inl_merge : categories.

Corollary inr_merge {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inr ≈ g.
Proof.
  intros.
  apply (proj1 (univ_coproducts f g (f ▽ g))).
  reflexivity.
Qed.

Hint Rewrite @inr_merge : categories.

Corollary merge_inl_inr {X Y : C} :
  inl ▽ inr ≈ @id C (X + Y).
Proof.
  intros.
  symmetry.
  apply univ_coproducts; cat.
Qed.

Hint Rewrite @merge_inl_inr : categories.

Corollary merge_inv {X Y Z : C} (f h : Y ~> X) (g i : Z ~> X) :
  f ▽ g ≈ h ▽ i <-> (f ≈ h ∧ g ≈ i).
Proof.
  pose proof (univ_coproducts h i (f ▽ g)) as Huniv.
  rewrite inl_merge in Huniv.
  rewrite inr_merge in Huniv.
  apply Huniv.
Qed.

Corollary merge_comp {X Y Z W : C} (f : Y ~> Z) (h : W ~> Z) (g : Z ~> X) :
  (g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h.
Proof.
  intros.
  symmetry.
  apply univ_coproducts.
  rewrite <- !comp_assoc; cat.
Qed.

Context `{@Initial C}.

Notation "0 + X" := (Coprod Zero X) (at level 30).
Notation "X + 0" := (Coprod X Zero) (at level 30).

Global Program Instance coprod_zero_l {X : C} :
  0 + X ≅ X := {
  iso_to   := zero ▽ id;
  iso_from := inr
}.
Obligation 1.
  constructor; simpl; intros; cat.
  rewrite <- merge_comp; cat.
  rewrite <- merge_inl_inr.
  apply merge_respects; cat.
Qed.

Hint Rewrite @coprod_zero_l : isos.

Global Program Instance coprod_zero_r {X : C} :
  X + 0 ≅ X := {
  iso_to   := id ▽ zero;
  iso_from := inl
}.
Obligation 1.
  constructor; simpl; intros; cat.
  rewrite <- merge_comp; cat.
  rewrite <- merge_inl_inr.
  apply merge_respects; cat.
Qed.

Hint Rewrite @coprod_zero_r : isos.

Global Program Instance coprod_assoc  {X Y Z : C} :
  (X + Y) + Z ≅ X + (Y + Z) := {
  iso_to   := (inl ▽ (inr ∘ inl)) ▽ (inr ∘ inr);
  iso_from := (inl ∘ inl) ▽ ((inl ∘ inr) ▽ inr)
}.
Next Obligation.
  constructor; simpl; intros;
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

  coprod_in  := fun X Y => iso_from (@fobj_coprod_iso X Y);
  coprod_out := fun X Y => iso_to   (@fobj_coprod_iso X Y);

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
Proof.
  intros.
  exact (iso_from_to (iso_witness fobj_coprod_iso)).
Qed.

Hint Rewrite @coprod_in_out : functors.

Corollary coprod_out_in {X Y : C} :
  coprod_out ∘ coprod_in ≈ @id _ (F X + F Y).
Proof.
  intros.
  exact (iso_to_from (iso_witness fobj_coprod_iso)).
Qed.

Hint Rewrite @coprod_out_in : functors.

Corollary coprod_in_surj {X Y Z : C} (f g : F (X + Y) ~> F X) :
  f ∘ coprod_in ≈ g ∘ coprod_in <-> f ≈ g.
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
  f ∘ coprod_out ≈ g ∘ coprod_out <-> f ≈ g.
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
