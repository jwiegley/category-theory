Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

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
  Equivalence Isomorphism.
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
  Proper
    (respectful Isomorphism
       (respectful Isomorphism Basics.arrow)) Isomorphism.
Next Obligation.
  proper.
  transitivity x; auto.
    symmetry; assumption.
  transitivity x0; auto.
Qed.

Global Program Instance flip_arrow_Isomorphism :
  Proper
    (respectful Isomorphism
       (respectful Isomorphism
                              (Basics.flip Basics.arrow))) Isomorphism.
Next Obligation.
  proper.
  transitivity y; auto.
  transitivity y0; auto.
  symmetry; assumption.
Qed.

Definition ob_equiv : crelation C := fun X Y => X ≅ Y.

Global Program Instance ob_setoid : Setoid C.

Definition isomorphism_equiv {X Y : C} : crelation (X ≅ Y) :=
  fun f g => (to f ≈ to g) * (from f ≈ from g).

Local Obligation Tactic := firstorder.

Global Program Instance isomorphism_equiv_equivalence {X Y : C} :
  Equivalence (@isomorphism_equiv X Y).

Global Program Instance isomorphism_setoid {X Y : C} : Setoid (X ≅ Y) := {
  equiv := isomorphism_equiv;
  setoid_equiv := isomorphism_equiv_equivalence
}.

End Isomorphism.

Delimit Scope isomorphism_scope with isomorphism.
Open Scope isomorphism_scope.

Notation "X ≅ Y" := (@Isomorphism _%category X%object Y%object)
  (at level 91) : isomorphism_scope.
Notation "X ≅[ C ] Y" := (@Isomorphism C%category X%object Y%object)
  (at level 91, only parsing) : isomorphism_scope.

Arguments to {_%category X%object Y%object} _%morphism.
Arguments from {_%category X%object Y%object} _%morphism.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

Hint Unfold isomorphism_equiv.

Ltac isomorphism :=
  unshelve (refine {| to := _; from := _ |}; simpl; intros).
