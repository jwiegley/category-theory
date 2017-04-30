Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.

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
Program Instance Sets : Category := {
  ob      := SetoidObject;
  hom     := fun A B => SetoidMorphism A B;
  id      := @setoid_morphism_id;
  compose := @setoid_morphism_compose
}.
Next Obligation.
  proper.
  unfold equiv in *; simpl in *; intros.
  rewrite X0.
  apply proper_morphism, X1.
Qed.

Program Instance Sets_Cartesian : @Cartesian Sets := {
  Prod := fun X Y =>
            {| carrier := (carrier X * carrier Y)%type
             ; is_setoid :=
                 {| equiv := fun x y =>
                               @equiv _ X (fst x) (fst y) *
                               @equiv _ Y (snd x) (snd y)
                  ; setoid_equiv := _
                  |}
             |};
  fork := fun _ _ _ f g => {| morphism := fun x => (f x, g x) |};
  exl := fun _ _ => {| morphism := fst |};
  exr := fun _ _ => {| morphism := snd |}
}.
Next Obligation. proper; apply proper_morphism; assumption. Qed.
Next Obligation. split; intros; firstorder. Qed.

Program Instance Sets_Cocartesian : @Cocartesian Sets := {
  Coprod := fun X Y =>
            {| carrier := (carrier X + carrier Y)%type
             ; is_setoid :=
                 {| equiv := fun x y =>
                      match x with
                      | Datatypes.inl x =>
                        match y with
                        | Datatypes.inl y => @equiv _ X x y
                        | Datatypes.inr _ => False
                        end
                      | Datatypes.inr x =>
                        match y with
                        | Datatypes.inl _ => False
                        | Datatypes.inr y => @equiv _ Y x y
                        end
                      end
                  ; setoid_equiv := _
                  |}
             |};
  merge := fun _ _ _ f g =>
             {| morphism := fun x =>
                  match x with
                  | Datatypes.inl x => f x
                  | Datatypes.inr x => g x
                  end |};
  inl := fun _ _ => {| morphism := Datatypes.inl |};
  inr := fun _ _ => {| morphism := Datatypes.inr |}
}.
Next Obligation.
  equivalence;
  destruct y, x; intuition;
  destruct z; intuition.
Qed.
Next Obligation.
  proper.
  destruct f, g; intuition.
  destruct y, x; intuition;
  destruct z; intuition.
Qed.
Next Obligation.
  simpl; split; intros.
    split; intros.
      specialize (X0 (Datatypes.inl x)); simpl in X0.
      assumption.
    specialize (X0 (Datatypes.inr x)); simpl in X0.
    assumption.
  destruct x; apply X0.
Qed.

(* An isomorphism between arrows in a category C is an isomorphism of objects
   in the category of set(oid)s, taking [hom] to the be the carrier type, and
   arrow equivalence to be the setoid. By using Sets in this way, we gain the
   fact that the arrows on both sides are respectful of C's notion of arrow
   equivalence. *)
Notation "X ≊ Y" := ({| carrier := X |} ≅[Sets] {| carrier := Y |})
  (at level 99) : category_scope.
