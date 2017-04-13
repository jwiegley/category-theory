Require Import Lib.
Require Export Initial.
Require Export Iso.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Class Cocartesian `(_ : Initial ob) := {
  Coprod : ob -> ob -> ob
    where "X + Y" := (Coprod X Y);

  merge {X Z W} (f : Z ~> X) (g : W ~> X) : Z + W ~> X;
  inl   {X Y} : X ~> X + Y;
  inr   {X Y} : Y ~> X + Y;

  merge_respects : ∀ X Z W,
    Proper (@eqv _ _ Z X ==> @eqv _ _ W X ==> @eqv _ _ (Z + W) X) merge;

  univ_coproducts {X Y Z} (f : Y ~> X) (g : Z ~> X) (h : Y + Z ~> X) :
    h ≈ merge f g <-> h ∘ inl ≈ f ∧ h ∘ inr ≈ g
}.

Arguments Cocartesian ob {_ _}.

Infix "+" := Coprod : category_scope.
Infix "▽" := merge (at level 26) : category_scope.

Program Instance parametric_morphism_merge
       `(H : Category ob)
       `(J : @Initial ob H)
       `(O : @Cocartesian ob H J) (a b c : ob) :
  Proper (eqv ==> eqv ==> eqv) (@merge ob H J O a b c) := merge_respects a b c.

Corollary inl_merge `{Cocartesian C} {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inl ≈ f.
Proof.
  intros.
  apply (proj1 (univ_coproducts f g (f ▽ g))).
  reflexivity.
Qed.

Hint Rewrite @inl_merge : categories.

Corollary inr_merge `{Cocartesian C} {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inr ≈ g.
Proof.
  intros.
  apply (proj1 (univ_coproducts f g (f ▽ g))).
  reflexivity.
Qed.

Hint Rewrite @inr_merge : categories.

Corollary merge_inl_inr `{Cocartesian C} {X Y : C} :
  inl ▽ inr ≈ @id C _ (X + Y).
Proof.
  intros.
  symmetry.
  apply univ_coproducts; cat.
Qed.

Hint Rewrite @merge_inl_inr : categories.

Corollary merge_inv `{Cocartesian C} {X Y Z : C} (f h : Y ~> X) (g i : Z ~> X) :
  f ▽ g ≈ h ▽ i <-> f ≈ h ∧ g ≈ i.
Proof.
  pose proof (univ_coproducts h i (f ▽ g)).
  rewrite inl_merge in H2.
  rewrite inr_merge in H2.
  apply H2.
Qed.

Corollary merge_comp `{Cocartesian C}
          {X Y Z W : C} (f : Y ~> Z) (h : W ~> Z) (g : Z ~> X) :
  (g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h.
Proof.
  intros.
  symmetry.
  apply univ_coproducts.
  rewrite <- !comp_assoc; cat.
Qed.

Notation "0 + X" := (Coprod Zero X) (at level 30).
Notation "X + 0" := (Coprod X Zero) (at level 30).

Program Instance coprod_zero_l `{Cocartesian C} {X : C} :
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

Program Instance coprod_zero_r `{Cocartesian C} {X : C} :
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

Class CocartesianFunctor `(_ : Cocartesian C) `(_ : Cocartesian D) := {
  initial_functor :> InitialFunctor C D;

  fobj_coprod_iso {X Y : C} : fobj (X + Y) ≅ fobj X + fobj Y;

  coprod_in  := fun X Y => iso_from (@fobj_coprod_iso X Y);
  coprod_out := fun X Y => iso_to   (@fobj_coprod_iso X Y);

  fmap_inl {X Y : C} : fmap (@inl C _ _ _ X Y) ≈ coprod_in _ _ ∘ inl;
  fmap_inr {X Y : C} : fmap (@inr C _ _ _ X Y) ≈ coprod_in _ _ ∘ inr;
  fmap_merge {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
    fmap (f ▽ g) ≈ fmap f ▽ fmap g ∘ coprod_out _ _
}.

Arguments CocartesianFunctor C {_ _ _} D {_ _ _}.

Arguments coprod_in {C _ _ _ D _ _ _ _ _ _} /.
Arguments coprod_out {C _ _ _ D _ _ _ _ _ _} /.

Notation "coprod_in[ C -> D | X ~> Y  ]" := (@coprod_in C _ _ _ D _ _ _ _ X Y).
Notation "coprod_out[ C -> D | X ~> Y  ]" := (@coprod_out C _ _ _ D _ _ _ _ X Y).

Corollary coprod_in_out `{CocartesianFunctor C D} {X Y : C} :
  coprod_in ∘ coprod_out ≈ @id _ _ (fobj (X + Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_coprod_iso _ _ _ _ _ _ _ _ _ X Y))).
Qed.

Hint Rewrite @coprod_in_out : functors.

Corollary coprod_out_in `{CocartesianFunctor C D} {X Y : C} :
  coprod_out ∘ coprod_in ≈ @id _ _ (fobj X + fobj Y).
Proof.
  intros.
  exact (iso_to_from (iso_witness (@fobj_coprod_iso _ _ _ _ _ _ _ _ _ X Y))).
Qed.

Hint Rewrite @coprod_out_in : functors.

Corollary coprod_in_surj `{CocartesianFunctor C D}
          {X Y Z : C} (f g : fobj (X + Y) ~> fobj X) :
  f ∘ coprod_in ≈ g ∘ coprod_in <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_right.
    rewrite <- coprod_in_out.
    rewrite comp_assoc.
    rewrite H6.
    rewrite <- comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite H6.
  reflexivity.
Qed.

Corollary coprod_out_inj `{CocartesianFunctor C D}
          {X Y Z : C} (f g : fobj Y + fobj Z ~> fobj X) :
  f ∘ coprod_out ≈ g ∘ coprod_out <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_right.
    rewrite <- coprod_out_in.
    rewrite comp_assoc.
    rewrite H6.
    rewrite <- comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite H6.
  reflexivity.
Qed.
