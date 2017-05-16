Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Morphisms.

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

Global Program Instance isomorphism_equivalence : Equivalence Isomorphism.
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

Coercion to : Isomorphism >-> hom.

Notation "f '⁻¹'" := (from f) (at level 9, format "f '⁻¹'") : morphism_scope.

Hint Unfold isomorphism_equiv.

Ltac isomorphism :=
  unshelve (refine {| to := _; from := _ |}; simpl; intros).

Program Instance id_iso `{C : Category} {X : C} : X ≅ X := {
  to := id;
  from := id
}.

Program Definition compose_iso `{C : Category}
        {X Y Z : C} `(f : Y ≅ Z) `(g : X ≅ Y) : X ≅ Z := {|
  to := to f ∘ to g;
  from := from g ∘ from f
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to g)).
  rewrite iso_to_from; cat.
  apply iso_to_from.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (from f)).
  rewrite iso_from_to; cat.
  apply iso_from_to.
Qed.

Program Instance iso_monic `{C : Category} {X Y} (iso : @Isomorphism C X Y) :
  Monic iso.
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_from_to iso).
  rewrite <- !comp_assoc.
  rewrite X0.
  reflexivity.
Qed.

Program Instance iso_from_monic `{C : Category} {X Y} (iso : @Isomorphism C X Y) :
  Monic (iso⁻¹).
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_to_from iso).
  rewrite <- !comp_assoc.
  rewrite X0.
  reflexivity.
Qed.

Program Instance iso_epic `{C : Category} {X Y} (iso : @Isomorphism C X Y) :
  Epic iso.
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_to_from iso).
  rewrite !comp_assoc.
  rewrite X0.
  reflexivity.
Qed.

Program Instance iso_from_epic `{C : Category} {X Y} (iso : @Isomorphism C X Y) :
  Epic (iso⁻¹).
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_from_to iso).
  rewrite !comp_assoc.
  rewrite X0.
  reflexivity.
Qed.

Program Instance Monic_Retraction_Iso
        `{C : Category} {X Y : C} `(r : @Retraction _ _ _ f) `(m : @Monic _ _ _ f) :
  X ≅ Y := {
  to := f;
  from := retract
}.
Next Obligation.
  destruct r; simpl.
  apply monic.
  rewrite comp_assoc.
  rewrite <- retract_comp; cat.
Qed.
Next Obligation.
  destruct r; simpl.
  apply monic.
  rewrite comp_assoc.
  rewrite retract_comp; cat.
Qed.

Program Instance Epic_Section_Iso
        `{C : Category} {X Y : C} `(s : @Section _ _ _ f) `(e : @Epic _ _ _ f) :
  X ≅ Y := {
  to := f;
  from := section
}.
Next Obligation.
  destruct s; simpl.
  specialize (epic Y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite section_comp; cat.
Qed.
Next Obligation.
  destruct s; simpl.
  specialize (epic Y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite <- section_comp; cat.
Qed.
