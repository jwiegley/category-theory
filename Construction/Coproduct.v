Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Coproduct.

Context {C : Category}.
Context {D : Category}.

(* A Groupoid is a category where all morphisms are isomorphisms, and morphism
   equivalence is equivalence of isomorphisms. *)

Program Definition Coproduct : Category := {|
  ob      := C + D;
  hom     := fun X Y =>
               match X return Type with
               | Datatypes.inl X =>
                 match Y with
                 | Datatypes.inl Y => X ~> Y
                 | Datatypes.inr _ => False
                 end
               | Datatypes.inr X =>
                 match Y with
                 | Datatypes.inl _ => False
                 | Datatypes.inr Y => X ~> Y
                 end
               end;
  homset  := fun X Y => {| equiv := fun f g => _ |};
  id      := fun X =>
               match X with
               | Datatypes.inl X => id
               | Datatypes.inr X => id
               end;
  compose := fun _ _ _ f g => _
|}.
Next Obligation.
  destruct X.
    destruct Y.
      exact (f ≈ g).
    contradiction.
  destruct Y.
    contradiction.
  exact (f ≈ g).
Defined.
Next Obligation.
  equivalence;
  destruct X, Y; simpl; intuition;
  unfold Coproduct_obligation_1 in *;
  intuition.
Qed.
Next Obligation.
  destruct H, H0, H1; intuition; exact (f ∘ g).
Defined.
Next Obligation.
  proper.
  destruct X, Y, Z;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition.
Qed.
Next Obligation.
  destruct X, Y;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct X, Y;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct X, Y, Z, W;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct X, Y, Z, W;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.

End Coproduct.

Notation "C ∐ D" := (@Coproduct C D) (at level 90) : category_scope.
