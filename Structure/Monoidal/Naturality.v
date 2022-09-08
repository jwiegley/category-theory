Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.
Set Transparent Obligations.

Section MonoidalNaturality.

Context `{M : @Monoidal C}.

Program Definition Tensor_Left {F : C ⟶ C} {y : C} : C ⟶ C := {|
  fobj := fun x => (F x ⨂ y)%object;
  fmap := fun _ _ f => fmap[F] f ⨂[M] id
|}.
Next Obligation.
  proper; apply bimap_respects; rewrites; reflexivity.
Defined.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Left_Map `{@Mapping C P} {y : C} :
  @Mapping C (fun x => P x ⨂ y)%object := {
  map := fun _ _ f => map f ⨂ id;
}.

#[export] Program Instance Tensor_Right {F : C ⟶ C} {x : C} : C ⟶ C := {
  fobj := fun y => (x ⨂ F y)%object;
  fmap := fun _ _ f => id ⨂[M] fmap[F] f
}.
Next Obligation.
  proper; apply bimap_respects;
  rewrites; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Right_Map `{@Mapping C P} {x : C} :
  @Mapping C (fun y => x ⨂ P y)%object := {
  map := fun _ _ f => id ⨂ map f;
}.

Program Definition Tensor_Both `{F : C ⟶ C} : C ⟶ C := {|
  fobj := fun x => (F x ⨂ F x)%object;
  fmap := fun _ _ f => fmap[F] f ⨂[M] fmap[F] f
|}.
Next Obligation.
  proper; apply bimap_respects;
  rewrites; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

#[export] Program Instance Tensor_Both_Map `{@Mapping C P} :
  @Mapping C (fun x => P x ⨂ P x)%object := {
  map := fun _ _ f => map f ⨂ map f;
}.

Theorem monoidal_naturality :
  natural (@unit_left _ M) *
  natural (@unit_right _ M) *
  natural (@tensor_assoc _ M).
Proof. prove_naturality M normal. Qed.

End MonoidalNaturality.
