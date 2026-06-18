Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** Invariance of the comma category under natural isomorphism of its functors. *)

(* nLab: https://ncatlab.org/nlab/show/comma+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category
   nLab: https://ncatlab.org/nlab/show/isomorphism

   Neither dedicated comma-category page states this invariance result
   explicitly; it follows from the definitions there together with the general
   notion of isomorphism, and is the strict-functor refinement of the standard
   fact that comma categories are invariant up to equivalence under naturally
   isomorphic defining functors.

   A morphism (f, g) of a comma category is an isomorphism exactly when both
   components f and g are isomorphisms in their respective categories (its
   inverse being (f⁻¹, g⁻¹)); this is what lets a natural isomorphism of one
   defining functor be transported objectwise to an isomorphism of objects of
   the comma category.

   Concretely, a natural isomorphism `iso : x ≅[Fun] y` of functors into a
   common codomain induces functors between the corresponding comma categories
   by reassociating the mediating morphism `h := `2 X` through the components
   of `iso`:

     - Comma_Iso_to_Left   : (x ↓ z) ⟶ (y ↓ z)   sends (a, b, h) to
                             (a, b, h ∘ from iso a)     [left argument moved]
     - Comma_Iso_from_Left : (y ↓ z) ⟶ (x ↓ z)   the reverse, via `to iso`
     - Comma_Iso_to_Right  : (z ↓ x) ⟶ (z ↓ y)   sends (a, b, h) to
                             (a, b, to iso b ∘ h)       [right argument moved]
     - Comma_Iso_from_Right: (z ↓ y) ⟶ (z ↓ x)   the reverse, via `from iso`

   On morphisms each functor is the identity pair (f, g); the commuting-square
   obligation is discharged by naturality of `iso` together with the source
   square. Comma_Iso then packages these into

     Comma  :  (x ≅[Fun] x') -> (y ≅[Fun] y') -> ((x ↓ y) ≅[Cat] (x' ↓ y'))

   i.e. @Comma A B C is `Proper` for natural isomorphism of each functor
   argument valued in isomorphism in Cat. Note that, per Theory/Isomorphism.v,
   an isomorphism in Cat is an *equivalence* of categories (the round-trips are
   only `≈ id`, not `= id`), so this is precisely the "invariant up to
   equivalence" statement; the round-trip natural isomorphisms are built with
   `constructive` from the inverse laws `iso_to_from` and `iso_from_to`. *)

Ltac reduce :=
  repeat match goal with
    | [ H : {p : _ & _ } |- _ ] => destruct H
    end;
  simpl; auto; try split; cat; simpl; cat.

#[local] Obligation Tactic := simpl; intros.

#[export]
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
Next Obligation. now repeat intro. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.

#[export]
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
  do 2 rewrite <- comp_assoc.
  apply compose_respects; try reflexivity.
  now rewrite <- naturality.
Defined.
Next Obligation. now repeat intro. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.

#[export]
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
Next Obligation. now repeat intro. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.

#[export]
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
Next Obligation. now repeat intro. Qed.
Next Obligation. now split. Qed.
Next Obligation. now split. Qed.

#[export]
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
      + clear; simpl.
        split.
        * symmetry.
          rewrite id_right.
          apply id_left.
        * symmetry.
          rewrite id_right.
          apply id_left.
    - constructive; simpl.
      + exists (id, id); cat.
        rewrite <- comp_assoc; simpl;
        srewrite (iso_from_to X); cat.
      + exists (id, id); cat.
        rewrite <- comp_assoc; simpl;
        srewrite (iso_from_to X); cat.
      + clear; simpl.
        split; apply id_left.
      + clear; simpl.
        split; apply id_left.
      + clear; simpl.
        split; rewrite id_right; symmetry; apply id_left.
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
    + clear; simpl.
      split; symmetry; rewrite id_right; apply id_left.
  - constructive; simpl.
    + exists (id, id); cat.
      rewrite comp_assoc; simpl;
      srewrite (iso_from_to X0); cat.
    + exists (id, id); cat.
      rewrite comp_assoc; simpl;
      srewrite (iso_from_to X0); cat.
    + clear; simpl.
      split; apply id_left.
    + clear; simpl.
      split; apply id_left.
    + clear; simpl.
      split; symmetry; rewrite id_right; apply id_left.
Qed.
