Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Comma.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Ltac reduce :=
  repeat match goal with
    | [ H : {p : _ & _ } |- _ ] => destruct H
    end;
  simpl; auto; try split; cat; simpl; cat.

Local Obligation Tactic := simpl; intros.

Program Instance Comma_Iso_to_Left {A : Category} {B : Category} {C : Category}
        (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C) :
  (x ↓ z) ⟶ (y ↓ z).
Next Obligation.
  exists ``X; simpl.
  exact (`2 X ∘ transform[from iso] _).
Defined.
Next Obligation.
  exists ``f; simpl.
  rewrite comp_assoc.
  rewrite <- (`2 f).
  rewrite <- comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.
Next Obligation. proper. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Program Instance Comma_Iso_from_Left {A : Category} {B : Category} {C : Category}
        (x y : A ⟶ C) (iso : x ≅[Fun] y) (z : B ⟶ C) :
  (y ↓ z) ⟶ (x ↓ z).
Next Obligation.
  exists ``X; simpl.
  exact (`2 X ∘ transform[to iso] _).
Defined.
Next Obligation.
  exists ``f; simpl.
  rewrite comp_assoc.
  rewrite <- (`2 f).
  rewrite <- comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.
Next Obligation. proper. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Program Instance Comma_Iso_to_Right {A : Category} {B : Category} {C : Category}
        (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C) :
  (z ↓ x) ⟶ (z ↓ y).
Next Obligation.
  exists ``X; simpl.
  exact (transform[to iso] _ ∘ `2 X).
Defined.
Next Obligation.
  exists ``f; simpl.
  rewrite <- comp_assoc.
  rewrite (`2 f).
  rewrite comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.
Next Obligation. proper. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Program Instance Comma_Iso_from_Right {A : Category} {B : Category} {C : Category}
        (x y : B ⟶ C) (iso : x ≅[Fun] y) (z : A ⟶ C) :
  (z ↓ y) ⟶ (z ↓ x).
Next Obligation.
  exists ``X; simpl.
  exact (transform[from iso] _ ∘ `2 X).
Defined.
Next Obligation.
  exists ``f; simpl.
  rewrite <- comp_assoc.
  rewrite (`2 f).
  rewrite comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  reflexivity.
Defined.
Next Obligation. proper. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Program Instance Comma_Iso {A : Category} {B : Category} {C : Category} :
  Proper (@Isomorphism Fun ==> @Isomorphism Fun ==> @Isomorphism Cat)
         (@Comma A B C).
Next Obligation.
  proper.
  transitivity (y ↓ x0). {
    isomorphism; simpl.
    - apply Comma_Iso_to_Left; assumption.
    - apply Comma_Iso_from_Left; assumption.
    - constructive; simpl.
      + exists (id, id); cat.
        rewrite <- comp_assoc; simpl;
        srewrite (iso_to_from X); cat.
      + exists (id, id); cat.
        rewrite <- comp_assoc; simpl;
        srewrite (iso_to_from X); cat.
      + clear; simpl; cat.
      + clear; simpl; cat.
      + clear; simpl; split; cat.
    - constructive; simpl.
      + exists (id, id); cat.
        rewrite <- comp_assoc; simpl;
        srewrite (iso_from_to X); cat.
      + exists (id, id); cat.
        rewrite <- comp_assoc; simpl;
        srewrite (iso_from_to X); cat.
      + clear; simpl; cat.
      + clear; simpl; cat.
      + clear; simpl; split; cat.
  }
  isomorphism; simpl.
  - apply Comma_Iso_to_Right; assumption.
  - apply Comma_Iso_from_Right; assumption.
  - constructive; simpl.
    + exists (id, id); cat.
      rewrite comp_assoc; simpl;
      srewrite (iso_to_from X0); cat.
    + exists (id, id); cat.
      rewrite comp_assoc; simpl;
      srewrite (iso_to_from X0); cat.
    + clear; simpl; cat.
    + clear; simpl; cat.
    + clear; simpl; split; cat.
  - constructive; simpl.
    + exists (id, id); cat.
      rewrite comp_assoc; simpl;
      srewrite (iso_from_to X0); cat.
    + exists (id, id); cat.
      rewrite comp_assoc; simpl;
      srewrite (iso_from_to X0); cat.
    + clear; simpl; cat.
    + clear; simpl; cat.
    + clear; simpl; split; cat.
Qed.
