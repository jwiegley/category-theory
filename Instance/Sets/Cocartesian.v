Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

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
  product_obj := fun x y =>
    {| carrier := (carrier x + carrier y)%type
     ; is_setoid :=
         {| equiv := fun z w =>
              match z with
              | Datatypes.inl z =>
                match w with
                | Datatypes.inl w => @equiv _ x z w
                | Datatypes.inr _ => False
                end
              | Datatypes.inr z =>
                match w with
                | Datatypes.inl _ => False
                | Datatypes.inr w => @equiv _ y z w
                end
              end
          ; setoid_equiv := _
          |} |};
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
  - specialize (X (Datatypes.inl x0)); auto.
  - specialize (X (Datatypes.inr x0)); auto.
  - destruct x0; auto.
Qed.
