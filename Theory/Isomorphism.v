Require Import Category.Lib.
Require Export Category.Theory.
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

Global Program Instance isomorphic_equivalence :
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

Global Program Instance arrow_Isomorphism :
  CMorphisms.Proper
    (CMorphisms.respectful Isomorphism
       (CMorphisms.respectful Isomorphism Basics.arrow)) Isomorphism.
Obligation 1.
  intros ???????.
  transitivity x; auto.
    symmetry; assumption.
  transitivity x0; auto.
Defined.

Global Program Instance flip_arrow_Isomorphism :
  CMorphisms.Proper
    (CMorphisms.respectful Isomorphism
       (CMorphisms.respectful Isomorphism
                              (Basics.flip Basics.arrow))) Isomorphism.
Obligation 1.
  intros ???????.
  transitivity y; auto.
  transitivity y0; auto.
  symmetry; assumption.
Defined.

End Isomorphism.

Infix "≅" := (@Isomorphism _) (at level 91) : category_scope.
Infix "≅[ C  ]" := (@Isomorphism C) (at level 91) : category_scope.

Arguments to {_ X Y} _.
Arguments from {_ X Y} _.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

(* An isomorphism between arrows in any category C is an isomorphism in the
   category of set(oid)s. *)
Notation "X ≃ Y" :=
  ({| carrier := X |} ≅[Sets] {| carrier := Y |}) (at level 99).
