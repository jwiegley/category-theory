Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(*
Import ListNotations.

(* This record establishes the structure of a concrete category's objects and
   arrows, in terms of fixed sets of natural numbers. It's main practical use
   is for building diagrams. *)

Record Concrete_Structure := {
  obs   : nat;
  arrs  : nat;

  composition : Fin.t arrs -> Fin.t arrs -> Fin.t arrs;
  composition_assoc {f g h} :
    composition f (composition g h) = composition (composition f g) h
}.

(* A concrete category has a fixed set of objects (of some decidable type, to
   differentiate them), and a fixed set of arrows between those objects. A
   frequent use of these is as index categories to build diagrams. *)

Program Definition Concrete (C : Concrete_Structure) :
  Category := {|
  ob      := Fin.t (obs C);
  hom     := fun _ _ => Fin.t (S (arrs C));
  homset  := fun _ _ => {| equiv := eq |};
  id      := fun _ => F1;
  compose := fun x y z f g => match f, g with
    | f,  F1 => f
    | F1, g  => g
    | f,  g  => f
    end
|}.
Next Obligation. destruct f; reflexivity. Qed.
Next Obligation. destruct f; reflexivity. Qed.
Next Obligation.
  destruct f, g, h; auto; f_equal.
  - pose proof (@composition_assoc S t t0 t1).
    destruct (composition S t0 t1); try tauto.
    destruct (composition S t t0); try tauto.
    destruct (composition S t t2); try tauto.
    destruct (composition S t3 t1); try tauto.
    subst; reflexivity.
  - destruct (composition S t t0); try tauto.
  - destruct (composition S t t0); try tauto.
Qed.
Next Obligation.
  destruct f, g, h; auto; f_equal.
  - pose proof (@composition_assoc S t t0 t1).
    destruct (composition S t0 t1); try tauto.
    destruct (composition S t t0); try tauto.
    destruct (composition S t t2); try tauto.
    destruct (composition S t3 t1); try tauto.
    subst; reflexivity.
  - destruct (composition S t t0); try tauto.
  - destruct (composition S t t0); try tauto.
Qed.

Module ConcreteInstances.

Set Transparent Obligations.

(* The 0 category has no objects and no morphisms. It is initial in Cat. *)

Program Definition Structure_0 : Concrete_Structure := {|
  obs  := 0;
  arrs := 0
|}.
Next Obligation. apply case0; auto. Qed.
Next Obligation. apply case0; auto. Qed.

Program Definition Concrete_0 := Concrete Structure_0.

Program Instance Map_0 `(C : Category) : Concrete_0 ⟶ C.
Next Obligation. inversion H. Qed.
Next Obligation. inversion X. Qed.
Next Obligation. inversion X. Qed.
Next Obligation. inversion X. Qed.

Program Instance Initial_0 : @Initial Cat := {
  Zero := Concrete_0;
  zero := Map_0
}.
Next Obligation.
  constructive.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact A0.
  refine (case0 (fun _ => _) _). exact A0.
Qed.

Program Instance Initial_0_is_0 : @Zero Cat Initial_0 ≅ 0.
Next Obligation. exact Id. Qed.
Next Obligation. exact Id. Qed.
Next Obligation.
  constructive.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact None.
  refine (case0 (fun _ => _) _); simpl.
  refine (case0 (fun _ => _) _); simpl. exact X.
  simpl; refine (case0 (fun _ => _) _).
  simpl; refine (case0 (fun _ => _) _).
Qed.
Next Obligation.
  constructive.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact X.
  refine (case0 (fun _ => _) _). exact None.
  refine (case0 (fun _ => _) _); simpl.
  refine (case0 (fun _ => _) _); simpl. exact X.
  simpl; refine (case0 (fun _ => _) _).
  simpl; refine (case0 (fun _ => _) _).
Qed.

(* The 1 category has one object and its identity morphism. It is terminal in
   Cat. *)

Program Definition Structure_1 : Concrete_Structure := {|
  obs  := 1;
  arrs := 0
|}.
Next Obligation. apply case0; auto. Qed.
Next Obligation. apply case0; auto. Qed.

Program Definition Concrete_1 := Concrete Structure_1.

Program Instance Map_1 `(C : Category) : C ⟶ Concrete_1 := {
  fobj := fun _ => F1;
  fmap := fun _ _ _ => id
}.

Program Instance Terminal_1 : @Terminal Cat := {
  One := Concrete_1;
  one := Map_1
}.
Next Obligation.
  constructive; auto; simpl.
  all:swap 2 4.
  - exact None.
  - exact None.
  - simpl.
    destruct (fmap[f] f0); simpl;
    destruct (fmap[g] f0); auto;
    pattern t; apply case0.
  - simpl.
    destruct (fmap[f] f0); simpl;
    destruct (fmap[g] f0); auto;
    pattern t; apply case0.
  - simpl.
    destruct (fmap[f] f0); simpl;
    destruct (fmap[g] f0); auto;
    pattern t; apply case0.
  - simpl.
    destruct (fmap[f] f0); simpl;
    destruct (fmap[g] f0); auto;
    pattern t; apply case0.
  - simpl.
    destruct (fmap[g] id); auto;
    pattern t; apply case0.
  - simpl.
    destruct (fmap[f] id); auto;
    pattern t; apply case0.
Qed.

Program Instance Terminal_1_is_1 : @One Cat Terminal_1 ≅ _1.
Next Obligation.
  functor; simpl; intros; reflexivity.
Defined.
Next Obligation.
  functor; simpl; intros; reflexivity.
Defined.
Next Obligation.
  constructive; intuition.
Qed.
Next Obligation.
  constructive; intuition.
  all:swap 2 4.
  - exact None.
  - exact None.
  - simpl.
    destruct f; auto;
    pattern t; apply case0.
  - simpl.
    destruct f; auto;
    pattern t; apply case0.
  - simpl.
    destruct f; auto;
    pattern t; apply case0.
  - simpl.
    destruct f; auto;
    pattern t; apply case0.
  - reflexivity.
  - reflexivity.
Qed.

(* The 2 category has two objects, their identity morphisms, and a morphism
   from the first to the second object. *)

Program Definition Structure_2 : Concrete_Structure := {|
  obs  := 2;
  arrs := 1
|}.
Next Obligation. exact None. Defined.

Definition Concrete_2 := Concrete Structure_2.

(* The 3 category has three objects, their identity morphisms, and morphisms
   from the first to the second object, the second to the third, and the first
   to the third (required by composition). *)

Program Definition Structure_3 : Concrete_Structure := {|
  obs  := 3;
  arrs := 3;
  composition := fun f g =>
                   
|}.

Definition Concrete_3 := Concrete Structure_3.

End ConcreteInstances.
*)
