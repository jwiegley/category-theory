Require Import Lib.
Require Export Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section Isomorphism.

Context `{C : Category}.

(* Two morphisms in a category C form an isomorphism if they compose to
   identity in both directions. *)
Class isomorphism `(iso_to : X ~> Y) `(iso_from: Y ~> X) : Prop := {
  iso_to_from : iso_to   ∘ iso_from ≈ id;
  iso_from_to : iso_from ∘ iso_to   ≈ id
}.

Arguments iso_to_from {_ _ _ _} _.
Arguments iso_from_to {_ _ _ _} _.

Infix "≃" := isomorphism (at level 91) : category_scope.

(* Two isomorphisms for the same pair of morphisms are equivalent by proof
   irrelevance. *)
Lemma isomorphism_eqv
      `{iso_toF : X ~> Y} `{iso_fromF: Y ~> X}
      `{iso_toG : X ~> Y} `{iso_fromG: Y ~> X} :
  iso_toF ≈ iso_toG ->
  iso_fromF ≈ iso_fromG ->
  iso_toF ≃ iso_fromF <-> iso_toG ≃ iso_fromG.
Proof.
  intros HF HG; split; intros HE;
  destruct HE.
    rewrite HF, HG in *.
    constructor; auto.
  rewrite <- HF, <- HG in *.
  constructor; auto.
Qed.

(* Two objects in C are isomorphic, if there is an isomorphism between theme.
   Note that this definition has computational content, so we can make use of
   the morphisms. *)
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

Record isomorphic_eqv {X Y : C} (F G : X ≅ Y) : Prop := {
  iso_to_eqv   : iso_to F   ≈ iso_to G;
  iso_from_eqv : iso_from F ≈ iso_from G
}.

Global Program Instance isomorphic_eqv_Equivalence {X Y : C} :
  Equivalence (@isomorphic_eqv X Y).
Obligation 1.
  intros ?.
  constructor.
  - reflexivity.
  - reflexivity.
Qed.
Obligation 2.
  intros ?? HA.
  constructor.
  - symmetry.
    destruct HA.
    assumption.
  - symmetry.
    destruct HA.
    assumption.
Qed.
Obligation 3.
  intros ??? HA HB.
  constructor.
  - destruct HA.
    destruct HB.
    transitivity (iso_to y); auto.
  - destruct HA.
    destruct HB.
    transitivity (iso_from y); auto.
Qed.

Class hom_iso {X Y Z W : C}
      `(hom_iso_to   : X ~{C}~> Y -> Z ~{C}~> W)
      `(hom_iso_from : Z ~{C}~> W -> X ~{C}~> Y) := {
  hom_iso_to_from {f} : hom_iso_to   (hom_iso_from f) ≈ f;
  hom_iso_from_to {f} : hom_iso_from (hom_iso_to f)   ≈ f;

  hom_iso_to_respects   : Proper (eqv ==> @eqv _ Z W) hom_iso_to;
  hom_iso_from_respects : Proper (eqv ==> @eqv _ X Y) hom_iso_from
}.

End Isomorphism.

Infix "≃" := isomorphism (at level 91) : category_scope.
Infix "≅" := isomorphic (at level 90) : category_scope.

Arguments iso_to_from {_ _ _ _ _} _.
Arguments iso_from_to {_ _ _ _ _} _.

Arguments iso_to {_ X Y} _.
Arguments iso_from {_ X Y} _.
Arguments iso_witness {_ X Y} _.
