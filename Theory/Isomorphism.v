Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Isomorphism.

Context `{C : Category}.

(* Two objects in C are isomorphic, if there is an isomorphism between theme.
   Note that this definition has computational content, so we can make use of
   the morphisms. *)
Class Isomorphism (X Y : C) : Type := {
  to   : X ~> Y;
  from : Y ~> X;

  iso_to_from : to ∘ from ≈ id;
  iso_from_to : from ∘ to ≈ id
}.

Arguments to {X Y} _.
Arguments from {X Y} _.
Arguments iso_to_from {X Y} _.
Arguments iso_from_to {X Y} _.

Infix "≅" := Isomorphism (at level 91) : category_scope.

Definition Isomorphism_Prop (X Y : C) : Prop :=
  exists (f : X ~> Y) (g : Y ~> X), f ∘ g ≈ id //\\ g ∘ f ≈ id.

Infix "≃" := Isomorphism_Prop (at level 91) : category_scope.

Definition ob_equiv : crelation C := fun X Y => X ≃ Y.

Global Program Instance isomorphism_equivalence : Equivalence Isomorphism_Prop.
Obligation 1.
  intros ?.
  exists id, id; cat.
Qed.
Obligation 2.
  intros ?? HA.
  destruct HA as [to [from [to_from from_to]]].
  exists from, to; cat.
Qed.
Obligation 3.
  intros ??? HA HB.
  destruct HA as [to0 [from0 [to_from0 from_to0]]].
  destruct HB as [to1 [from1 [to_from1 from_to1]]].
  exists (to1 ∘ to0), (from0 ∘ from1).
    rewrite <- comp_assoc.
    rewrite (comp_assoc to0).
    rewrite to_from0; cat.
  rewrite <- comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ from1).
  rewrite from_to1; cat.
Qed.

Global Program Instance ob_setoid : Setoid C.

Definition isomorphism_equiv {X Y : C} : crelation (X ≅ Y) :=
  fun f g => to f ≈ to g //\\ from f ≈ from g.

Global Program Instance isomorphism_equiv_equivalence {X Y : C} :
  Equivalence (@isomorphism_equiv X Y).
Next Obligation.
  repeat intro.
  split; reflexivity.
Qed.
Next Obligation.
  repeat intros ?? HA.
  split; symmetry; apply HA.
Qed.
Next Obligation.
  repeat intros ? y ? HA HB.
  destruct HA, HB.
  split.
    transitivity (to y); auto.
  transitivity (from y); auto.
Qed.

Global Program Instance isomorphism_setoid {X Y : C} : Setoid (X ≅ Y) := {
  equiv := isomorphism_equiv;
  setoid_equiv := isomorphism_equiv_equivalence
}.

End Isomorphism.

Infix "≅" := (@Isomorphism _) (at level 91) : category_scope.
Notation "F ≅[ C ] G" := (@Isomorphism C F G)
  (at level 91, only parsing) : category_scope.

Infix "≃" := Isomorphism_Prop (at level 91) : category_scope.
Notation "F ≃[ C ] G" := (@Isomorphism_Prop C F G)
  (at level 91, only parsing) : category_scope.

Arguments to {_ X Y} _.
Arguments from {_ X Y} _.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

(* An isomorphism between arrows in a category C is an isomorphism of objects
   in the category of set(oid)s, taking [hom] to the be the carrier type, and
   arrow equivalence to be the setoid. By using Sets in this way, we gain the
   fact that the arrows on both sides are respectful of C's notion of arrow
   equivalence. *)
Notation "X ≊ Y" := ({| carrier := X |} ≅[Sets] {| carrier := Y |})
  (at level 99) : category_scope.
