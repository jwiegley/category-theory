Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Groupoid.

Context `{C : Category}.

(* A Groupoid is a category where all the morphisms are isomorphisms, and
   morphism equivalence is equivalence of isomorphisms. *)
Program Instance Groupoid : Category := {
  ob      := @ob C;
  hom     := @Isomorphism C;
  id      := fun _ => _;
  compose := fun _ _ _ => _;
}.
Next Obligation. Admitted.
Next Obligation.
  reflexivity.                  (* identity is reflexivity *)
Defined.
Next Obligation.
  transitivity H0; assumption.  (* composition is transitivity *)
Defined.
Next Obligation.
  unfold Groupoid_obligation_3.
  intros ??????.
(*
  - destruct x, y, x0, y0, H, H0; simpl in *.
    rewrite iso_to_eqv.
    rewrite iso_to_eqv0.
    reflexivity.
  - destruct x, y, x0, y0, H, H0; simpl in *.
    rewrite iso_from_eqv.
    rewrite iso_from_eqv0.
    reflexivity.
Qed.
*)
Admitted.
Next Obligation.
  unfold Groupoid_obligation_2.
  unfold Groupoid_obligation_3.
(*
  - destruct f; simpl; cat.
  - destruct f; simpl; cat.
Qed.
*)
Admitted.
Next Obligation.
  unfold Groupoid_obligation_2.
  unfold Groupoid_obligation_3.
(*
  - destruct f; simpl; cat.
  - destruct f; simpl; cat.
Qed.
*)
Admitted.
Next Obligation.
  unfold Groupoid_obligation_2.
  unfold Groupoid_obligation_3.
(*
  - destruct f, g, h; simpl.
    rewrite comp_assoc; reflexivity.
  - destruct f, g, h; simpl.
    rewrite comp_assoc; reflexivity.
Qed.
*)
Admitted.

End Groupoid.
