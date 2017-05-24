Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Theory.Adjunction.Isomorphism.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section AdjunctionToIso.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Program Definition Adjunction_to_Iso {A : F ⊣ U} :
  Adjunction_Iso F U := {|
  adj := fun a b =>
    {| to := {| morphism := fun f =>
        fmap f ∘ @Adjunction.unit _ _ _ _ A a |}
     ; from := {| morphism := fun f =>
        @Adjunction.counit _ _ _ _ A b ∘ fmap f |} |}
|}.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  srewrite (naturality[Adjunction.unit] a).
  rewrite comp_assoc.
  srewrite (@Adjunction.fmap_counit_unit); cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  srewrite_r (naturality[Adjunction.counit] _ _ x).
  rewrite <- comp_assoc.
  srewrite (@Adjunction.counit_fmap_unit); cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  srewrite (naturality[Adjunction.unit] a).
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
  srewrite_r (naturality[Adjunction.counit] b).
  rewrite <- comp_assoc.
  reflexivity.
Qed.

End AdjunctionToIso.
