Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Record SetoidObject := {
  carrier :> Type;
  is_setoid :> Setoid carrier
}.

Record SetoidMorphism `{Setoid A} `{Setoid B} := {
  morphism :> A -> B;
  proper_morphism :> Proper (equiv ==> equiv) morphism
}.

Arguments SetoidMorphism {_} _ {_} _.
Arguments morphism {_ _ _ _ _} _.

Program Instance SetoidMorphism_Setoid {A B : SetoidObject} :
  Setoid (SetoidMorphism A B) := {|
  equiv := fun f g => forall x, @equiv _ B (f x) (g x)
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    apply X.
  - transitivity (y x0).
      apply X.
    apply X0.
Qed.

Definition setoid_morphism_id {A : SetoidObject} : SetoidMorphism A A := {|
  morphism := Datatypes.id
|}.

Hint Unfold setoid_morphism_id.

Program Definition setoid_morphism_compose {A B C : SetoidObject}
        (g : SetoidMorphism B C)
        (f : SetoidMorphism A B) : SetoidMorphism A C := {|
  morphism := Basics.compose g f
|}.
Next Obligation.
  repeat intro.
  apply proper_morphism.
  apply proper_morphism.
  assumption.
Qed.

Hint Unfold setoid_morphism_compose.
(* Hint Unfold setoid_morphism_compose_obligation_1. *)

(* The category of setoids.

       objects: setoids
        arrows: setoid homomorphisms
      identity: typical identity of sets
   composition: composition of set maps, preserving equivalence
 *)
Program Definition Sets : Category := {|
  ob      := SetoidObject;
  hom     := fun A B => SetoidMorphism A B;
  homset  := @SetoidMorphism_Setoid;
  id      := @setoid_morphism_id;
  compose := @setoid_morphism_compose
|}.
Next Obligation.
  proper.
  unfold equiv in *; simpl in *; intros.
  rewrite X0.
  apply proper_morphism, X1.
Qed.

(* An isomorphism between arrows in a category C is an isomorphism of objects
   in the category of set(oid)s, taking [hom] to the be the carrier type, and
   arrow equivalence to be the setoid. By using Sets in this way, we gain the
   fact that the arrows on both sides are respectful of C's notion of arrow
   equivalence. *)
Notation "X ≊ Y" := ({| carrier := X |} ≅[Sets] {| carrier := Y |})
  (at level 99) : category_scope.

Ltac morphism :=
  unshelve (refine {| morphism := _ |}; simpl; intros).

Require Import Category.Structure.Terminal.

Program Instance Unit_Setoid : Setoid () := {
  equiv := fun x y => x = y
}.

Program Instance Sets_Terminal : @Terminal Sets := {
  One := {| carrier := unit |};
  one := _
}.
Next Obligation.
  morphism.
    intros.
    exact tt.
  proper.
Qed.
Next Obligation.
  destruct (f x), (g x).
  reflexivity.
Qed.

Require Import Category.Structure.Initial.

Program Instance False_Setoid : Setoid False.

Program Instance Sets_Initial : @Initial Sets := {
  Zero := {| carrier := False |};
  zero := _
}.
Next Obligation.
  morphism.
  contradiction.
Qed.
Next Obligation.
  contradiction.
Qed.
