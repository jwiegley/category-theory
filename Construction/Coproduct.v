Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Section Coproduct.

Context {C : Category}.
Context {D : Category}.

Local Set Warnings "-intuition-auto-with-star".

Program Definition Coproduct : Category := {|
  obj     := C + D;
  hom     := fun x y =>
               match x return Type with
               | Datatypes.inl x =>
                 match y with
                 | Datatypes.inl y => x ~> y
                 | Datatypes.inr _ => False
                 end
               | Datatypes.inr x =>
                 match y with
                 | Datatypes.inl _ => False
                 | Datatypes.inr y => x ~> y
                 end
               end;
  homset  := fun x y => {| equiv := fun f g => _ |};
  id      := fun x =>
               match x with
               | Datatypes.inl x => id
               | Datatypes.inr x => id
               end;
  compose := fun _ _ _ f g => _
|}.
Next Obligation.
  destruct x.
  - destruct y.
    + exact (f ≈ g).
    + contradiction.
  - destruct y.
    + contradiction.
    + exact (f ≈ g).
Defined.
Next Obligation.
  equivalence;
  destruct x, y; simpl; intuition;
  unfold Coproduct_obligation_1 in *;
  intuition; auto with *.
Qed.
Next Obligation.
  repeat match goal with [ H : _ + _ |- _ ] => destruct H end;
  intuition; exact (f ∘ g).
Defined.
Next Obligation.
  proper.
  destruct x, y, z;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; auto with *.
Qed.
Next Obligation.
  destruct x, y;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct x, y;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct x, y, z, w;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.
Next Obligation.
  destruct x, y, z, w;
  unfold Coproduct_obligation_1 in *;
  unfold Coproduct_obligation_3 in *;
  intuition; cat.
Qed.

End Coproduct.

Notation "C ∐ D" := (@Coproduct C D) (at level 90) : category_scope.
