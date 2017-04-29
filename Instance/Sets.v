Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Record SetoidObject := {
  carrier :> Type;
  is_csetoid :> CSetoid carrier
}.

Record SetoidMorphism `{CSetoid A} `{CSetoid B} := {
  morphism :> A -> B;
  proper_morphism :> CMorphisms.Proper (cequiv ===> cequiv) morphism;
  proper_morphism_prop :> Proper (equiv ==> equiv) morphism :=
    cequiv_proper1 proper_morphism
}.

Arguments SetoidMorphism {_} _ {_} _.
Arguments morphism {_ _ _ _ _} _.
Arguments proper_morphism_prop {_ _ _ _ _ _ _} /.

Program Instance SetoidMorphism_Setoid {A B : SetoidObject} :
  CSetoid (SetoidMorphism A B) := {|
  cequiv := fun f g => forall x, @cequiv _ B (f x) (g x)
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    apply X.
  - transitivity (y x0).
      apply X.
    apply X0.
Defined.

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
Defined.

Hint Unfold setoid_morphism_compose.
Hint Unfold setoid_morphism_compose_obligation_1.

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
  unfold cequiv in *; simpl in *; intros.
  rewrite X0.
  apply proper_morphism, X1.
Defined.
Next Obligation.
  unfold equiv, cequiv; simpl.
  unfold cequiv; simpl.
  apply inhabits; reflexivity.
Defined.
Next Obligation.
  unfold equiv, cequiv; simpl.
  unfold cequiv; simpl.
  apply inhabits; reflexivity.
Defined.

Program Instance Sets_Cartesian : @Cartesian Sets := {
  Prod := fun X Y =>
            {| carrier := (carrier X * carrier Y)%type
             ; is_csetoid :=
                 {| cequiv := fun x y =>
                               @cequiv _ X (fst x) (fst y) *
                               @cequiv _ Y (snd x) (snd y)
                  ; setoid_cequiv := _
                  |}
             |};
  fork := fun _ _ _ f g => {| morphism := fun x => (f x, g x) |};
  exl := fun _ _ => {| morphism := fst |};
  exr := fun _ _ => {| morphism := snd |}
}.
Next Obligation.
  proper.
  split; simpl;
  apply proper_morphism; assumption.
Defined.
Next Obligation. proper; destruct X; assumption. Defined.
Next Obligation. proper; destruct X; assumption. Defined.
Next Obligation.
  proper.
  unfold cequiv; simpl; intro.
  split.
    apply X0.
  apply X1.
Defined.
Next Obligation.
  autounfold; simpl;
  unfold Sets_Cartesian_obligation_2; simpl;
  unfold Sets_Cartesian_obligation_3; simpl;
  unfold Sets_Cartesian_obligation_4; simpl;
  unfold equiv; simpl;
  unfold cequiv; simpl.
  simpl; split; intros.
    destruct H.
    split; apply inhabits;
    firstorder.
  destruct H, H, H0.
  apply inhabits.
  firstorder.
Qed.

Program Instance Sets_Cocartesian : @Cocartesian Sets := {
  Coprod := fun X Y =>
            {| carrier := (carrier X + carrier Y)%type
             ; is_csetoid :=
                 {| cequiv := fun x y =>
                      match x with
                      | Datatypes.inl x =>
                        match y with
                        | Datatypes.inl y => @cequiv _ X x y
                        | Datatypes.inr _ => False
                        end
                      | Datatypes.inr x =>
                        match y with
                        | Datatypes.inl _ => False
                        | Datatypes.inr y => @cequiv _ Y x y
                        end
                      end
                  ; setoid_cequiv := _
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
Defined.
Next Obligation.
  proper.
  destruct f, g; intuition.
  destruct y, x; intuition;
  destruct z; intuition.
Defined.
Next Obligation.
  proper.
  unfold cequiv; simpl; intros.
  destruct x1.
    apply X0.
  apply X1.
Defined.
Next Obligation.
  autounfold; simpl;
  unfold Sets_Cocartesian_obligation_2; simpl;
  unfold Sets_Cocartesian_obligation_3; simpl;
  unfold Sets_Cocartesian_obligation_4; simpl;
  unfold equiv; simpl;
  unfold cequiv; simpl.
  simpl; split; intros.
    destruct H.
    split; apply inhabits; intros.
      specialize (X0 (Datatypes.inl x)); simpl in X0.
      assumption.
    specialize (X0 (Datatypes.inr x)); simpl in X0.
    assumption.
  destruct H, H, H0.
  apply inhabits; intros.
  destruct x.
    apply X0.
  apply X1.
Defined.

(* An isomorphism between arrows in a category C is an isomorphism of objects
   in the category of set(oid)s, taking [hom] to the be the carrier type, and
   arrow equivalence to be the setoid. By using Sets in this way, we gain the
   fact that the arrows on both sides are respectful of C's notion of arrow
   equivalence. *)
Notation "X ≊ Y" := ({| carrier := X |} ≅[Sets] {| carrier := Y |})
  (at level 99) : category_scope.
