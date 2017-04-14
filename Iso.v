Require Import Lib.
Require Export Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Iso.

Context `{C : Category}.

Class isomorphism `(iso_to : X ~> Y) `(iso_from: Y ~> X) : Type := {
  iso_to_from : iso_to   ∘ iso_from ≈ id;
  iso_from_to : iso_from ∘ iso_to   ≈ id
}.

Arguments iso_to_from {_ _ _ _} _.
Arguments iso_from_to {_ _ _ _} _.

Infix "≃" := isomorphism (at level 91) : category_scope.

Definition isomorphism_eqv `{iso_to : X ~> Y} `{iso_from: Y ~> X}
           (F G : iso_to ≃ iso_from) : Prop :=
  proof_eq (iso_to_from F) (iso_to_from G) /\
  proof_eq (iso_from_to F) (iso_from_to G).

Global Program Instance isomorphism_eqv_Equivalence
       `{iso_to : X ~> Y} `{iso_from: Y ~> X} :
  Equivalence (@isomorphism_eqv _ _ iso_to iso_from).
Obligation 1.
  intros ?.
  destruct x.
  unfold isomorphism_eqv, proof_eq; auto.
Qed.
Obligation 2.
  intros ???.
  destruct x, y.
  unfold isomorphism_eqv, proof_eq in *; simpl in *; intuition.
Qed.
Obligation 3.
  intros ?????.
  unfold isomorphism_eqv, proof_eq in *; simpl in *; intuition.
  transitivity (iso_to_from y); auto.
  transitivity (iso_from_to y); auto.
Qed.

Class isomorphic (X Y : C) : Type := {
  iso_to   : X ~> Y;
  iso_from : Y ~> X;
  iso_witness : iso_to ≃ iso_from
}.

Arguments iso_to {X Y} _.
Arguments iso_from {X Y} _.
Arguments iso_witness {X Y} _.

Infix "≅" := isomorphic (at level 90) : category_scope.

Global Program Instance isomorphic_equivalence :
  CRelationClasses.Equivalence isomorphic.
Obligation 1.
  intros ?.
  apply Build_isomorphic with (iso_to:=id) (iso_from:=id).
  constructor; cat.
Defined.
Obligation 2.
  intros ???.
  destruct X.
  apply Build_isomorphic with (iso_to:=iso_from0) (iso_from:=iso_to0).
  destruct iso_witness0.
  constructor; auto.
Defined.
Obligation 3.
  intros ?????.
  destruct X, X0.
  apply Build_isomorphic with (iso_to:=iso_to1 ∘ iso_to0)
                              (iso_from:=iso_from0 ∘ iso_from1).
  destruct iso_witness0, iso_witness1.
  constructor.
    rewrite <- comp_assoc.
    rewrite (comp_assoc iso_to0).
    rewrite iso_to_from0; cat.
  rewrite <- comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ iso_from1).
  rewrite iso_from_to1; cat.
Defined.

Global Program Instance arrow_isomorphic :
  CMorphisms.Proper
    (CMorphisms.respectful isomorphic
       (CMorphisms.respectful isomorphic Basics.arrow)) isomorphic.
Obligation 1.
  intros ???????.
  transitivity x; auto.
    symmetry; assumption.
  transitivity x0; auto.
Defined.

Global Program Instance flip_arrow_isomorphic :
  CMorphisms.Proper
    (CMorphisms.respectful isomorphic
       (CMorphisms.respectful isomorphic
                              (Basics.flip Basics.arrow))) isomorphic.
Obligation 1.
  intros ???????.
  transitivity y; auto.
  transitivity y0; auto.
  symmetry; assumption.
Defined.

Lemma isomorphic_transport {X Y : C}
      (F G : X ≅ Y)
      (iso_to_eqv : iso_to F ≈ iso_to G)
      (iso_from_eqv : iso_from F ≈ iso_from G) :
  iso_to F ≃ iso_from F.
Proof.
  destruct G, iso_witness0; simpl in *.
  rewrite <- iso_to_eqv in *.
  rewrite <- iso_from_eqv in *.
  constructor; auto.
Qed.

Record isomorphic_eqv {X Y : C} (F G : X ≅ Y) : Prop := {
  iso_to_eqv      : iso_to F ≈ iso_to G;
  iso_from_eqv    : iso_from F ≈ iso_from G;
  iso_witness_eqv :
    isomorphism_eqv (iso_witness F)
                    (isomorphic_transport F G iso_to_eqv iso_from_eqv)
}.

Global Program Instance isomorphic_eqv_Equivalence {X Y : C} :
  Equivalence (@isomorphic_eqv X Y).
Obligation 1.
  intros ?.
  econstructor.
  split; apply proof_irrelevance.
  Unshelve.
  - reflexivity.
  - reflexivity.
Qed.
Obligation 2.
  intros ?? HA.
  econstructor.
  split; apply proof_irrelevance.
  Unshelve.
  - symmetry.
    destruct HA.
    assumption.
  - symmetry.
    destruct HA.
    assumption.
Qed.
Obligation 3.
  intros ??? HA HB.
  econstructor.
  split; apply proof_irrelevance.
  Unshelve.
  - destruct HA.
    destruct HB.
    transitivity (iso_to y); auto.
  - destruct HA.
    destruct HB.
    transitivity (iso_from y); auto.
Qed.

End Iso.

Infix "≃" := isomorphism (at level 91) : category_scope.
Infix "≅" := isomorphic (at level 90) : category_scope.

Arguments iso_to_from {_ _ _ _ _} _.
Arguments iso_from_to {_ _ _ _ _} _.

Arguments iso_to {_ X Y} _.
Arguments iso_from {_ X Y} _.
Arguments iso_witness {_ X Y} _.
