Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section AdjunctionToTransform.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Program Definition Adjunction_from_Transform (A : F ∹ U) : F ⊣ U := {|
  adj := fun a b =>
    {| to   := {| morphism := fun f =>n fmap f ∘ transform[unit[A]] a |}
     ; from := {| morphism := fun f => transform[counit[A]] b ∘ fmap f |} |}
|}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. proper; now rewrites. Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  srewrite (naturality[unit[A]]).
  rewrite comp_assoc.
  srewrite (@Transformation.fmap_counit_unit); cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  srewrite_r (naturality[counit[A]]).
  rewrite <- comp_assoc.
  srewrite (@Transformation.counit_fmap_unit); cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  srewrite (naturality[unit[A]]).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  srewrite_r (naturality[counit[A]]).
  now rewrite <- comp_assoc.
Qed.

Program Definition Adjunction_to_Transform {A : F ⊣ U} : F ∹ U := {|
  Transformation.unit   := {| transform := fun _ => unit |};
  Transformation.counit := {| transform := fun _ => counit |}
|}.
Next Obligation.
  unfold unit.
  rewrite <- to_adj_nat_r, <- to_adj_nat_l; cat.
Qed.
Next Obligation.
  unfold unit.
  rewrite <- to_adj_nat_r, <- to_adj_nat_l; cat.
Qed.
Next Obligation.
  unfold counit.
  rewrite <- from_adj_nat_r, <- from_adj_nat_l; cat.
Qed.
Next Obligation.
  unfold counit.
  rewrite <- from_adj_nat_r, <- from_adj_nat_l; cat.
Qed.
Next Obligation.
  unfold unit, counit.
  rewrite <- from_adj_nat_l; cat.
  apply (@iso_from_to _ _ _ adj _).
Qed.
Next Obligation.
  unfold unit, counit.
  rewrite <- to_adj_nat_r; cat.
  apply (@iso_to_from _ _ _ adj _).
Qed.

End AdjunctionToTransform.
