Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Instance.Nat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section KanExtension.

Context `{A : Category}.
Context `{B : Category}.
Context `{F : A ⟶ B}.
Context `{C : Category}.

(* jww (2017-05-19): This should be the definition of Compose. *)
Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ○ F;
  fmap := fun _ _ f => {| transform := fun Z => transform[f] (F Z) |}
|}.
Next Obligation. apply naturality. Qed.

Class HasRan := {
  Ran : ([A, C]) ⟶ ([B, C]);

  ran_adjoint : Induced ⊣ Ran
}.

End KanExtension.

Arguments Ran {_ _} F {_ _}.
Arguments HasRan {_ _} F {_}.
