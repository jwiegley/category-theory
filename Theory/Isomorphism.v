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

Global Program Instance isomorphism_equivalence :
  CRelationClasses.Equivalence Isomorphism.
Obligation 1.
  intros ?.
  apply Build_Isomorphism with (to:=id) (from:=id); cat.
Defined.
Obligation 2.
  intros ???.
  destruct X.
  apply Build_Isomorphism with (to:=from0) (from:=to0); cat.
Defined.
Obligation 3.
  intros ?????.
  destruct X, X0.
  apply Build_Isomorphism with (to:=to1 ∘ to0) (from:=from0 ∘ from1).
    rewrite <- comp_assoc.
    rewrite (comp_assoc to0).
    rewrite iso_to_from0; cat.
  rewrite <- comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ from1).
  rewrite iso_from_to1; cat.
Defined.

End Isomorphism.

Infix "≅" := (@Isomorphism _) (at level 91) : category_scope.
Notation "F ≅[ C ] G" := (@Isomorphism C F G)
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
Notation "X ≃ Y" := ({| carrier := X |} ≅[Sets] {| carrier := Y |})
  (at level 99) : category_scope.
