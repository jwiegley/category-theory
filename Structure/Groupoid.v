Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Groupoid.

Context `{C : Category}.

(* A Groupoid is a category where all morphisms are isomorphisms, and morphism
   equivalence is equivalence of isomorphisms. *)

Program Instance Groupoid : Category := {
  ob      := @ob C;
  hom     := @Isomorphism C;
  homset  := @isomorphism_setoid C;
  id      := fun _ =>
    {| to := id
     ; from := id |};
  compose := fun _ _ _ f g =>
    {| to := to f ∘ to g
     ; from := from g ∘ from f |}
}.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to g)).
  rewrite iso_to_from; cat.
  apply iso_to_from.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (from f)).
  rewrite iso_from_to; cat.
  apply iso_from_to.
Qed.
Next Obligation.
  repeat intros ?? HA ?? HB.
  unfold isomorphism_equiv.
  destruct HA, HB; simpl; split.
    rewrite H, H1; reflexivity.
  rewrite H0, H2; reflexivity.
Qed.
Next Obligation.
  unfold isomorphism_equiv.
  destruct f; simpl; split; cat.
Qed.
Next Obligation.
  unfold isomorphism_equiv.
  destruct f; simpl; split; cat.
Qed.
Next Obligation.
  unfold isomorphism_equiv.
  destruct f, g, h; simpl; split;
  rewrite comp_assoc; reflexivity.
Qed.

End Groupoid.
