Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Adjunction.Natural.Transformation.
Require Export Category.Theory.Adjunction.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section AdjunctionToTransform.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Program Definition Adjunction_from_Transform (A : F ∹ U) : F ⊣ U := {|
  adj := fun a b =>
    {| to   := {| morphism := fun f =>
         fmap f ∘ @Transformation.unit _ _ _ _ A a |}
     ; from := {| morphism := fun f =>
         @Transformation.counit _ _ _ _ A b ∘ fmap f |} |}
|}.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  srewrite (naturality[Transformation.unit]).
  rewrite comp_assoc.
  srewrite (@Transformation.fmap_counit_unit); cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  srewrite_r (naturality[Transformation.counit]).
  rewrite <- comp_assoc.
  srewrite (@Transformation.counit_fmap_unit); cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  srewrite (naturality[Transformation.unit]).
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  srewrite_r (naturality[Transformation.counit]).
  rewrite <- comp_assoc.
  reflexivity.
Qed.

Program Definition Adjunction_to_Transform {A : F ⊣ U} : F ∹ U := {|
  Transformation.unit   := {| transform := fun a => @unit _ _ _ _ A a |};
  Transformation.counit := {| transform := fun b => @counit _ _ _ _ A b |}
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
