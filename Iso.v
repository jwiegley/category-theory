Require Import Lib.
Require Export Category.

Generalizable All Variables.

Class isomorphism `{Category ob}
       `(iso_to : X ~> Y) `(iso_from: Y ~> X) : Type := {
  iso_to_from : iso_to   ∘ iso_from ≈ id;
  iso_from_to : iso_from ∘ iso_to   ≈ id
}.

Arguments iso_to_from {_ _ _ _ _ _} _.
Arguments iso_from_to {_ _ _ _ _ _} _.

Class isomorphic `{Category ob} (X Y : ob) : Type := {
  iso_to   : X ~> Y;
  iso_from : Y ~> X;
  iso_witness : isomorphism iso_to iso_from
}.

Arguments iso_to {_ _ X Y} _.
Arguments iso_from {_ _ X Y} _.
Arguments iso_witness {_ _ X Y} _.

Infix "≅" := isomorphic (at level 90) : category_scope.

Program Instance isomorphic_equivalence `{Category ob} :
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
  rewrite (@comp_assoc _ _ _ _ _ _ iso_from1).
  rewrite iso_from_to1; cat.
Defined.

Program Instance arrow_isomorphic `{Category C} :
  CMorphisms.Proper
    (CMorphisms.respectful isomorphic
       (CMorphisms.respectful isomorphic Basics.arrow)) isomorphic.
Obligation 1.
  intros ???????.
  transitivity x; auto.
    symmetry; assumption.
  transitivity x0; auto.
Defined.

Program Instance flip_arrow_isomorphic `{Category C} :
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
