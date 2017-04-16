Require Import Category.Lib.
Require Export Category.Theory.Natural.
Require Import Category.Construct.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

(* jww (2017-04-16): How to represent heteromorphisms? *)

Program Instance Profunctor `(D : Category) `(C : Category) : D^op ⟶ [C, Sets] := {
  fobj := fun X => {|
    fobj := fun Y => {| carrier := @hom C X Y
                      ; is_setoid := @homset C X Y |};
    fmap := fun Y Z (f : Y ~{C}~> Z) =>
              {| morphism := fun (g : X ~{C}~> Y) =>
                               (f ∘ g) : X ~{C}~> Z |}
  |};
  fmap := fun X Y (f : X ~{C^op}~> Y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ unop f |}
  |}
}.
Next Obligation.
  intros ?? HA.
  rewrite HA; reflexivity.
Defined.
Next Obligation.
  intros ?? HA ?; simpl.
  rewrite HA; reflexivity.
Defined.
Next Obligation. cat. Defined.
Next Obligation.
  unfold Basics.compose.
  rewrite comp_assoc; reflexivity.
Defined.
Next Obligation.
  repeat intro; intuition.
Defined.
Next Obligation.
  unfold Basics.compose.
  rewrite comp_assoc; reflexivity.
Defined.
Next Obligation.
  repeat intro; intuition; simpl in *.
  unfold unop.
  rewrite X0; reflexivity.
Defined.
Next Obligation.
  intro; simpl; unfold unop; intros; cat.
Defined.
Next Obligation.
  intro; simpl; unfold unop, Basics.compose; intros.
  rewrite comp_assoc; reflexivity.
Defined.

Coercion HomFunctor : Category >-> Functor.

Notation "'Hom' ( A , ─ )" := (@HomFunctor _ A) : category_scope.
