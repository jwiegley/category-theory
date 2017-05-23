Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Reserved Notation "C ^op" (at level 7).

Definition Opposite `(C : Category) : Category := {|
  ob      := @ob C;
  hom     := fun x y => @hom C y x;
  homset  := fun x y => @homset C y x;
  id      := @id C;
  compose := fun _ _ _ f g => g ∘ f;

  compose_respects := fun X Y Z f g fg h i hi =>
    @compose_respects C Z Y X h i hi f g fg;

  id_left  := fun X Y f => @id_right C Y X f;
  id_right := fun X Y f => @id_left C Y X f;

  comp_assoc := fun X Y Z W f g h => @comp_assoc_sym C W Z Y X h g f;
  comp_assoc_sym := fun X Y Z W f g h => @comp_assoc C W Z Y X h g f
|}.

Notation "C ^op" := (@Opposite C)
  (at level 7, format "C ^op") : category_scope.

Lemma op_invol {C : Category} : (C^op)^op = C.
Proof.
  unfold Opposite; simpl.
  destruct C; simpl.
  f_equal.
Qed.

Definition op   {C : Category} {X Y} (f : Y ~{C}~> X) : X ~{C^op}~> Y := f.
Definition unop {C : Category} {X Y} (f : X ~{C^op}~> Y) : Y ~{C}~> X := f.
