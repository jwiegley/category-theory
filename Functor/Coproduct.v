Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.

Generalizable All Variables.

Section Coproduct.

Context {C : Category}.
Context `{@Cocartesian C}.

Definition sum_obj : C ∐ C → C :=
  sum_rect (const C) Datatypes.id Datatypes.id.

Section sum_map.

#[local] Set Transparent Obligations.

Program Definition sum_map (a : C ∐ C) (b : C ∐ C) (f : a ~> b) :
  sum_obj a ~> sum_obj b :=
  match a, b with
  | Datatypes.inl x, Datatypes.inl y => _
  | Datatypes.inl _, Datatypes.inr _ => !
  | Datatypes.inr x, Datatypes.inl _ => !
  | Datatypes.inr x, Datatypes.inr y => _
  end.

End sum_map.

#[export]
Program Instance CoproductFunctor : C ∐ C ⟶ C := {
  fobj := sum_obj;
  fmap := sum_map;
}.
Next Obligation.
  proper; destruct x, y; simpl; tauto.
Qed.
Next Obligation.
  destruct x; simpl; reflexivity.
Qed.
Next Obligation.
  destruct x, y, z; simpl; cat; tauto.
Qed.

End Coproduct.
