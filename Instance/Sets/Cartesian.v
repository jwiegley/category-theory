Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Instance.Sets.
Require Export Category.Structure.Cartesian.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance Sets_Cartesian : @Cartesian Sets := {
  Prod := fun X Y =>
            {| carrier := (carrier X * carrier Y)%type
             ; is_setoid :=
                 {| equiv := fun x y =>
                               @equiv _ X (fst x) (fst y) *
                               @equiv _ Y (snd x) (snd y)
                  ; setoid_equiv := _
                  |}
             |};
  fork := fun _ _ _ f g => {| morphism := fun x => (f x, g x) |};
  exl := fun _ _ => {| morphism := fst |};
  exr := fun _ _ => {| morphism := snd |}
}.
Next Obligation. proper; apply proper_morphism; assumption. Qed.
Next Obligation. all:firstorder. Qed.
