Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

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
  constructor; repeat intro; intuition.
  transitivity (y x0); auto.
Qed.

Definition setoid_morphism_id {A : SetoidObject} : SetoidMorphism A A := {|
  morphism := Datatypes.id
|}.

Program Definition setoid_morphism_compose {A B C : SetoidObject}
        (g : SetoidMorphism B C)
        (f : SetoidMorphism A B) : SetoidMorphism A C := {|
  morphism := Basics.compose g f
|}.
Next Obligation.
  repeat intro; unfold compose.
  destruct A, B, C; simpl.
  destruct g, f; simpl.
  unfold Basics.compose.
  rewrite X; reflexivity.
Qed.

(* The category of setoids.

       objects: setoids
        arrows: setoid homomorphisms
      identity: typical identity of sets
   composition: composition of set maps, preserving equivalence
 *)
Program Instance Sets : Category := {
  ob      := SetoidObject;
  hom     := fun A B => SetoidMorphism A B;
  id      := @setoid_morphism_id;
  compose := @setoid_morphism_compose
}.
Next Obligation.
  repeat intro.
  unfold setoid_morphism_compose; simpl.
  unfold Basics.compose.
  destruct x0, y0, x, y; simpl in *.
  rewrite X0, X1; reflexivity.
Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
