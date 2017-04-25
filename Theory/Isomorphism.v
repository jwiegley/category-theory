Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Isomorphism.

Context `{C : Category}.

(* Two objects in C are isomorphic, if there is an isomorphism between theme.
   Note that this definition has computational content, so we can make use of
   the morphisms. *)
Class Isomorphism (X Y : C) : Type := {
  to   :> X ~> Y;
  from :  Y ~> X;

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
Next Obligation.
  intros.
  apply Build_Isomorphism with (to:=id) (from:=id); cat.
Defined.
Next Obligation.
  intros; destruct X.
  apply Build_Isomorphism with (to:=from0) (from:=to0); cat.
Defined.
Next Obligation.
  intros; destruct X, X0.
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
Next Obligation.
  proper.
  rewrite <- X.
  transitivity x0; auto.
Defined.

Global Program Instance flip_arrow_Isomorphism :
  CMorphisms.Proper
    (CMorphisms.respectful Isomorphism
       (CMorphisms.respectful Isomorphism
                              (Basics.flip Basics.arrow))) Isomorphism.
Next Obligation.
  proper.
  transitivity y; auto.
  transitivity y0; auto.
  symmetry; assumption.
Defined.

Definition Isomorphism_Prop (X Y : C) : Prop :=
  exists (f : X ~> Y) (g : Y ~> X), f ∘ g ≈ id ∧ g ∘ f ≈ id.

Infix "≃" := Isomorphism_Prop (at level 91) : category_scope.

Definition ob_equiv : relation C := fun X Y => X ≃ Y.

Global Program Instance isomorphism_prop_equivalence :
  Equivalence Isomorphism_Prop.
Next Obligation.
  intros.
  exists id, id; cat.
Qed.
Next Obligation. firstorder. Qed.
Next Obligation.
  intros.
  destruct H as [to0 [from0 [to_from0 from_to0]]].
  destruct H0 as [to1 [from1 [to_from1 from_to1]]].
  exists (to1 ∘ to0), (from0 ∘ from1).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc to0).
  rewrite to_from0; cat.
  rewrite to_from1; cat.
  rewrite (comp_assoc from1).
  rewrite from_to1; cat.
Qed.

Global Program Instance impl_Isomorphism_Prop :
  Proper
    (respectful Isomorphism_Prop
       (respectful Isomorphism_Prop Basics.impl)) Isomorphism_Prop.
Next Obligation.
  proper.
  transitivity x; auto.
    symmetry; assumption.
  transitivity x0; auto.
Defined.

Global Program Instance flip_impl_Isomorphism_Prop :
  Proper
    (respectful Isomorphism_Prop
       (respectful Isomorphism_Prop
                              (Basics.flip Basics.impl))) Isomorphism_Prop.
Next Obligation.
  proper.
  transitivity y; auto.
  transitivity y0; auto.
  symmetry; assumption.
Defined.

Global Program Instance ob_setoid : Setoid C.

Definition isomorphism_equiv {X Y : C} : relation (X ≅ Y) :=
  fun f g => to f ≈ to g ∧ from f ≈ from g.

Global Program Instance isomorphism_equiv_equivalence {X Y : C} :
  Equivalence (@isomorphism_equiv X Y).
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

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

Coercion to : Isomorphism >-> hom.

Hint Unfold isomorphism_equiv.
