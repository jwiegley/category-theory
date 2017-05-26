Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.
Require Export Category.Instance.Sets.
Require Export Category.Structure.Cocartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance Sets_Cocartesian : @Cocartesian Sets := {
  Prod := fun X Y =>
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
  fork := fun _ _ _ f g =>
             {| morphism := fun x =>
                  match x with
                  | Datatypes.inl x => f x
                  | Datatypes.inr x => g x
                  end |};
  exl := fun _ _ => {| morphism := Datatypes.inl |};
  exr := fun _ _ => {| morphism := Datatypes.inr |}
}.
Next Obligation.
  proper.
  destruct f, g; intuition.
  destruct y, x; intuition;
  destruct z; intuition.
Qed.
Next Obligation.
  simplify.
  - specialize (X0 (Datatypes.inl x)); auto.
  - specialize (X0 (Datatypes.inr x)); auto.
  - destruct x; auto.
Qed.
