Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Construction.Comma.
Require Export Category.Instance.One.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section ProductComma.

Ltac simpl_cat :=
  repeat (
    simpl; intros;
    simplify;
    simpl; intros;
    match goal with
    | [ |- _ ≅ _ ] => unshelve econstructor
    | [ |- _ ⟹ _ ] => unshelve econstructor
    | [ |- _ ⟶ _ ] => unshelve econstructor
    | [ |- @Proper _ _ _ ] => first [ abstract proper | proper ]
    | [ |- @Equivalence _ _ ] => first [ abstract equivalence | equivalence ]
    | [ |- _ ≈ _ ] => abstract cat
    | _ => cat
    end).

Theorem Comma_Product {C : Category} {D : Category}
        (F : C ⟶ 1) (G : D ⟶ 1) :
  (F ↓ G) ≅[Cat] C ∏ D.
Proof. simpl_cat. Qed.

End ProductComma.
