Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Record SetoidObject := {
  carrier :> Type;
  is_setoid :> Setoid carrier
}.

Record SetoidMorphism `{Setoid x} `{Setoid y} := {
  morphism :> x → y;
  proper_morphism :> Proper (equiv ==> equiv) morphism
}.

Arguments SetoidMorphism {_} _ {_} _.
Arguments morphism {_ _ _ _ _} _.

#[global]
Program Instance SetoidMorphism_Setoid {x y : SetoidObject} :
  Setoid (SetoidMorphism x y) := {|
  equiv := fun f g => ∀ x, @equiv _ y (f x) (g x)
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    apply X.
  - transitivity (y0 x1).
      apply X.
    apply X0.
Qed.

Definition setoid_morphism_id {x : SetoidObject} : SetoidMorphism x x := {|
  morphism := Datatypes.id
|}.

#[export] Hint Unfold setoid_morphism_id : core.

Program Definition setoid_morphism_compose {x y C : SetoidObject}
        (g : SetoidMorphism y C)
        (f : SetoidMorphism x y) : SetoidMorphism x C := {|
  morphism := Basics.compose g f
|}.
Next Obligation.
  repeat intro.
  apply proper_morphism.
  apply proper_morphism.
  assumption.
Qed.

#[export] Hint Unfold setoid_morphism_compose : core.

(* The category of setoids.

       objects: setoids
        arrows: setoid homomorphisms
      identity: typical identity of sets
   composition: composition of set maps, preserving equivalence
 *)
Program Definition Sets : Category := {|
  obj     := SetoidObject;
  hom     := fun x y => SetoidMorphism x y;
  homset  := @SetoidMorphism_Setoid;
  id      := @setoid_morphism_id;
  compose := @setoid_morphism_compose
|}.
Next Obligation.
  proper.
  unfold equiv in *; simpl in *; intros.
  rewrite X.
  apply proper_morphism, X0.
Qed.

Require Import Category.Theory.Isomorphism.

(* An isomorphism between arrows in a category C is an isomorphism of objects
   in the category of set(oid)s, taking [hom] to the be the carrier type, and
   arrow equivalence to be the setoid. By using Sets in this way, we gain the
   fact that the arrows on both sides are respectful of C's notion of arrow
   equivalence. *)
Notation "x ≊ y" := ({| carrier := x |} ≅[Sets] {| carrier := y |})
  (at level 99) : category_scope.

#[global]
Program Instance isomorphism_to_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (to iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct to; simpl in *.
  rewrite X; reflexivity.
Qed.

#[global]
Program Instance isomorphism_from_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (from iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct from; simpl in *.
  rewrite X; reflexivity.
Qed.

Ltac morphism :=
  unshelve (refine {| morphism := _ |}; simpl; intros).

Require Import Category.Structure.Terminal.

#[global]
Program Instance Unit_Setoid : Setoid (unit : Type) := {
  equiv := fun x y => x = y
}.

#[global]
Program Instance Sets_Terminal : @Terminal Sets := {
  terminal_obj := {| carrier := unit : Type |};
  one := fun _ => {| morphism := fun _ => tt |};
  one_unique := fun x f g => _
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

Require Import Category.Structure.Initial.

#[global]
Program Instance False_Setoid : Setoid False.

#[global]
Program Instance Sets_Initial : @Initial Sets := {
  terminal_obj := {| carrier := False |};
  one := _
}.
Next Obligation. morphism; contradiction. Qed.
Next Obligation. contradiction. Qed.

Require Import Category.Structure.Monoidal.

#[global]
Program Instance Sets_Product_Monoidal : @Monoidal Sets := {
  I      := {| carrier := unit : Type |};
  tensor := {|
    fobj := fun p =>
      {| carrier := carrier (fst p) * carrier (snd p)
       ; is_setoid := _
       |};
    fmap := fun x y f =>
      {| morphism := fun p => (fst f (fst p), snd f (snd p))
       ; proper_morphism := _ |}
  |}
}.
Next Obligation.
  construct.
  - repeat intro.
    destruct s, s0.
    exact (fst X ≈ fst X0 ∧ snd X ≈ snd X0).
  - simpl.
    equivalence.
Defined.
Next Obligation.
  proper; simpl in *.
  - destruct s.
    now rewrites.
  - destruct s0.
    now rewrites.
Qed.
Next Obligation.
  construct.
  - construct.
    + now destruct X.
    + proper.
  - construct.
    + split; [ exact tt | assumption ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct u.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + now destruct X.
    + proper.
  - construct.
    + split; [ assumption | exact tt ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct u.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + simplify; auto.
    + proper.
  - construct.
    + simplify; auto.
    + proper.
  - simpl.
    simplify; simpl; cat.
  - simpl.
    simplify; simpl; cat.
Defined.
