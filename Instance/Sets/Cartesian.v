Require Import Category.Lib.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.

#[export]
Program Instance Sets_Cartesian : @Cartesian Sets := {
  product_obj := fun x y =>
    {| carrier := (carrier x * carrier y)%type
     ; is_setoid :=
         {| equiv := fun z w =>
                       @equiv _ x (fst z) (fst w) *
                       @equiv _ y (snd z) (snd w)
          ; setoid_equiv := _
          |} |};
  fork := fun _ _ _ f g => {| morphism := fun x => (f x, g x) |};
  exl := fun _ _ => {| morphism := fst |};
  exr := fun _ _ => {| morphism := snd |}
}.
Next Obligation. proper; apply proper_morphism; assumption. Qed.
Next Obligation. all:firstorder. Qed.
