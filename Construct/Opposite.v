Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Reserved Notation "C ^op" (at level 90).

Program Instance Opposite `(C : Category) : Category := {
  ob      := @ob C;
  hom     := fun x y => @hom C y x;
  homset  := fun x y => @homset C y x;
  id      := @id C;
  compose := fun _ _ _ f g => g ∘ f;

  compose_respects := fun X Y Z f g fg h i hi =>
    @compose_respects C Z Y X h i hi f g fg;

  id_left  := fun X Y (f : Y ~{ C }~> X) => @id_right C Y X f;
  id_right := fun X Y f => @id_left C Y X f;

  comp_assoc := fun X Y Z W (f : W ~> Z) (g : Z ~> Y) (h : Y ~> X) =>
                  symmetry (@comp_assoc C W Z Y X h g f)
}.

Notation "C ^op" := (@Opposite C)
  (at level 90, format "C ^op") : category_scope.

Open Scope equiv_scope.

Lemma op_involutive `{C : Category} : (C^op)^op = C.
Proof.
  unfold Opposite; simpl.
  destruct C; simpl.
  f_equal.
  extensionality X.
  extensionality Y.
  extensionality Z.
  extensionality W.
  extensionality f.
  extensionality g.
  extensionality h.
Abort.

Definition op `{C : Category} : ∀ {X Y : C},
  (X ~{C^op}~> Y) → (Y ~{C}~> X).
Proof. intros; assumption. Defined.

Definition unop `{C : Category} : ∀ {X Y : C},
  (Y ~{C}~> X) → (X ~{C^op}~> Y).
Proof. auto. Defined.

Program Instance Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op := {
    fobj := @fobj C D F;
    fmap := fun X Y f => @fmap C D F Y X (op f)
}.
Next Obligation.
  repeat intro.
  apply fmap_respects.
  unfold op.
  assumption.
Defined.
Next Obligation. unfold op; apply fmap_id. Qed.
Next Obligation. unfold op; apply fmap_comp. Qed.

Program Instance Reverse_Opposite_Functor `(F : C^op ⟶ D^op) : C ⟶ D := {
    fobj := @fobj _ _ F;
    fmap := fun X Y f => unop (@fmap _ _ F Y X f)
}.
Next Obligation.
  repeat intros ?? HA; unfold unop.
  rewrite HA; reflexivity.
Defined.
Next Obligation.
  unfold unop.
  unfold fmap. simpl.
  pose (@fmap_id _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e X). auto.
Defined.
Next Obligation.
  unfold unop.
  unfold fmap. simpl.
  pose (@fmap_comp _ _ F).
  unfold fmap in e. simpl in e.
  specialize (e Z Y X g f).
  auto.
Defined.

Lemma op_functor_involutive `(F : Functor) :
  Reverse_Opposite_Functor (Opposite_Functor F) ≈ F.
Proof.
  unfold Reverse_Opposite_Functor.
  unfold Opposite_Functor.
  destruct F; simpl;
  unfold functor_equiv; simpl; intros.
  reflexivity.
Defined.
