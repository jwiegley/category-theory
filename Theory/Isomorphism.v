Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Morphisms.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Isomorphism.

Context {C : Category}.

(* This defines what it means for two objects in a category to be
   "isomorphic". This requires both witnesses to the isomoprhism, and proof
   their compositions are equivalent to identity in both directions. Since
   this is a computationally relevant definition, having an isomorphism allows
   for conversion of objects within definitions.

   An isomorphism in Cat is the same as an equivalence of categories. In order
   to get actual isomorphism between categories, the compositions F ○ G and G
   ○ F need to be equal, rather than equivalent, to identity. Since this is
   usually too strong a notion, it does not have its own abstraction here. *)

Class Isomorphism (x y : C) : Type := {
  to   :> x ~> y;
  from :  y ~> x;

  iso_to_from : to ∘ from ≈ id;
  iso_from_to : from ∘ to ≈ id
}.

Arguments to {x y} _.
Arguments from {x y} _.
Arguments iso_to_from {x y} _.
Arguments iso_from_to {x y} _.

Infix "≅" := Isomorphism (at level 91) : category_scope.

Global Program Instance iso_id {x : C} : x ≅ x := {
  to   := id;
  from := id
}.

Global Program Definition iso_sym {x y : C} `(f : x ≅ y) : y ≅ x := {|
  to   := from f;
  from := to f;

  iso_to_from := iso_from_to f;
  iso_from_to := iso_to_from f
|}.

Global Program Definition iso_compose {x y z : C} `(f : y ≅ z) `(g : x ≅ y) :
  x ≅ z := {|
  to   := to f ∘ to g;
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

Global Program Instance isomorphism_equivalence : Equivalence Isomorphism := {
  Equivalence_Reflexive  := @iso_id;
  Equivalence_Symmetric  := @iso_sym;
  Equivalence_Transitive := fun _ _ _ g f => iso_compose f g
}.

Definition ob_equiv : crelation C := fun x y => x ≅ y.

Global Program Instance ob_setoid : Setoid C.

Definition isomorphism_equiv {x y : C} : crelation (x ≅ y) :=
  fun f g => (to f ≈ to g) * (from f ≈ from g).

Local Obligation Tactic := firstorder.

Global Program Instance isomorphism_equiv_equivalence {x y : C} :
  Equivalence (@isomorphism_equiv x y).

Global Program Instance isomorphism_setoid {x y : C} : Setoid (x ≅ y) := {
  equiv := isomorphism_equiv;
  setoid_equiv := isomorphism_equiv_equivalence
}.

End Isomorphism.

Delimit Scope isomorphism_scope with isomorphism.
Open Scope isomorphism_scope.

Notation "x ≅ y" := (@Isomorphism _%category x%object y%object)
  (at level 91) : isomorphism_scope.
Notation "x ≅[ C ] y" := (@Isomorphism C%category x%object y%object)
  (at level 91, only parsing) : isomorphism_scope.

Arguments to {_%category x%object y%object} _%morphism.
Arguments from {_%category x%object y%object} _%morphism.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

Coercion to : Isomorphism >-> hom.

Notation "f '⁻¹'" := (from f) (at level 9, format "f '⁻¹'") : morphism_scope.

Hint Unfold isomorphism_equiv.

Ltac isomorphism :=
  unshelve (refine {| to := _; from := _ |}; simpl; intros).

Program Instance iso_monic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Monic iso.
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_from_to iso).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

Program Instance iso_from_monic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Monic (iso⁻¹).
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_to_from iso).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

Program Instance iso_epic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Epic iso.
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_to_from iso).
  rewrite !comp_assoc.
  rewrites; reflexivity.
Qed.

Program Instance iso_from_epic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Epic (iso⁻¹).
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_from_to iso).
  rewrite !comp_assoc.
  rewrites; reflexivity.
Qed.

Program Instance Monic_Retraction_Iso
        {C : Category} {x y : C} `(r : @Retraction _ _ _ f) `(m : @Monic _ _ _ f) :
  x ≅ y := {
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
        {C : Category} {x y : C} `(s : @Section _ _ _ f) `(e : @Epic _ _ _ f) :
  x ≅ y := {
  to := f;
  from := section
}.
Next Obligation.
  destruct s; simpl.
  specialize (epic y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite section_comp; cat.
Qed.
Next Obligation.
  destruct s; simpl.
  specialize (epic y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite <- section_comp; cat.
Qed.
