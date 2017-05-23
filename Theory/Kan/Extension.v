Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section KanExtension.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.

Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ○ F;
  fmap := fun _ _ f => {| transform := fun Z => transform[f] (F Z) |}
|}.
Next Obligation. apply naturality. Qed.

Class HasRan := {
  Ran : ([A, C]) ⟶ ([B, C]);

  ran_adjoint : Induced ⊣ Ran
}.

Class HasRanL (X : A ⟶ C) := {
  RanL : B ⟶ C;

  ranl_transform : RanL ○ F ⟹ X;

  ranl_delta (M : B ⟶ C) (N : M ○ F ⟹ X) : M ⟹ RanL;

  ump_ranl (M : B ⟶ C) (N : M ○ F ⟹ X) :
    N ≈[[A, C]] ranl_transform ⊙ outside (ranl_delta M N) F
}.

Require Import Category.Instance.Cat.

(* Wikipedia: "There is also a local definition of 'the Kan extension of a
   given functor F along p' which can exist even if the entire functor defined
   above [global Kan extension] does not. This is a generalization of the fact
   that a particular diagram of shape C can have a limit even if not every
   such diagram does. It is also a special case of the fact discussed at
   adjoint functor that an adjoint functor can fail to exist completely, but
   may still be partially defined. If the local Kan extension of every single
   functor exists for some given p : C → C' and D, then these local Kan
   extensions fit together to define a functor which is the global Kan
   extension." *)

Global Program Instance HasRan_HasRanL {R : HasRan} (X : A ⟶ C) :
  HasRanL X := {|
  RanL := Ran X;
  ranl_transform :=
    let adj_from := from (@adj_iso _ _ _ _ ran_adjoint (Ran X) X)
                         nat_identity in
    {| transform  := transform[adj_from]
     ; naturality := naturality[adj_from] |};
  ranl_delta := fun M N => to (@adj_iso _ _ _ _ ran_adjoint M X) N
|}.
Next Obligation.
  pose proof (@adj_right_nat_l' _ _ _ _ ran_adjoint); simpl in X0.
  rewrite <- X0; clear X0.
  pose proof (@adj_right_left _ _ _ _ ran_adjoint).
  unfold adj_left, adj_right in X0;
  unfold adj_left', adj_right' in X0.
  destruct R, ran_adjoint0;
  specialize (X0 M X N A0).
  destruct adj_iso, to, from; simpl in *;
  unfold nat_compose; simpl in *.
  rewrite <- X0; clear X0.
  apply proper_morphism0.
  simpl; intros; cat.
Qed.

End KanExtension.

Arguments HasRan {_ _} F {_}.
Arguments Ran {_ _} F {_ _}.

Arguments HasRanL {_ _} F {_} _.
Arguments RanL {_ _} F {_} _ {_}.
