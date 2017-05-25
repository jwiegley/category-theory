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
Next Obligation. apply naturality_sym. Qed.

Class RightKan := {
  Ran : ([A, C]) ⟶ ([B, C]);

  ran_adjoint : Induced ⊣ Ran
}.

Class LocalRightKan (X : A ⟶ C) := {
  LocalRan : B ⟶ C;

  ran_transform : LocalRan ○ F ⟹ X;

  ran_delta (M : B ⟶ C) (N : M ○ F ⟹ X) : M ⟹ LocalRan;

  ump_ran (M : B ⟶ C) (N : M ○ F ⟹ X) :
    N ≈[[A, C]] ran_transform ⊙ outside (ran_delta M N) F
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

Global Program Instance RightKan_to_LocalRightKan {R : RightKan} (X : A ⟶ C) :
  LocalRightKan X := {|
  LocalRan := Ran X;
  ran_transform :=
    let adj_from := from (@adj _ _ _ _ ran_adjoint (Ran X) X)
                         nat_identity in
    {| transform  := transform[adj_from]
     ; naturality := naturality[adj_from] |};
  ran_delta := fun M N => to (@adj _ _ _ _ ran_adjoint M X) N
|}.
Next Obligation.
  srewrite_r (naturality[from (@adj _ _ _ _ ran_adjoint (Ran X) X) nat_identity]).
  reflexivity.
Qed.
Next Obligation.
  pose proof (@from_adj_nat_l _ _ _ _ ran_adjoint); simpl in X0.
  rewrite <- X0; clear X0.
  pose proof (@iso_from_to _ _ _ (@adj _ _ _ _ ran_adjoint M X) N A0).
  simpl in *.
  unfold nat_compose; simpl in *.
  rewrite <- X0; clear X0.
  sapply (proper_morphism (@from _ _ _ (@adj _ _ _ _ ran_adjoint M X))).
  simpl; intros; cat.
Qed.

Class LeftKan := {
  Lan : ([A, C]) ⟶ ([B, C]);

  lan_adjoint : Lan ⊣ Induced
}.

Class LocalLeftKan (X : A ⟶ C) := {
  LocalLan : B ⟶ C;

  lan_transform : X ⟹ LocalLan ○ F;

  lan_delta (M : B ⟶ C) (N : X ⟹ M ○ F) : LocalLan ⟹ M;

  ump_lan (M : B ⟶ C) (N : X ⟹ M ○ F) :
    N ≈[[A, C]] outside (lan_delta M N) F ⊙ lan_transform
}.

End KanExtension.

Arguments RightKan {_ _} F {_}.
Arguments Ran {_ _} F {_ _}.

Arguments LocalRightKan {_ _} F {_} _.
Arguments LocalRan {_ _} F {_} _ {_}.

Arguments LeftKan {_ _} F {_}.
Arguments Lan {_ _} F {_ _}.

Arguments LocalLeftKan {_ _} F {_} _.
Arguments LocalLan {_ _} F {_} _ {_}.
