Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The coproduct (disjoint union) of two categories. *)

(* nLab: https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   The coproduct category C ∐ D has as objects the tagged disjoint union of the
   objects of C and D, an object being either inl c with c : C or inr d with
   d : D. Morphisms exist only within a single summand: a hom inl c ~> inl c'
   is a morphism c ~> c' in C, a hom inr d ~> inr d' is a morphism d ~> d' in
   D, and the hom-set between objects of different summands is empty (encoded
   here as False). Identity and composition are inherited from whichever
   summand the objects live in, and equivalence of morphisms is the ≈ of that
   summand. The unit and associativity laws hold because they hold in each
   summand.

   This is the coproduct in Cat, the category of categories: the inclusion
   functors C ⟶ C ∐ D and D ⟶ C ∐ D exhibit C ∐ D as the categorical coproduct
   of C and D, so a functor C ∐ D ⟶ E is the same as a pair of functors C ⟶ E
   and D ⟶ E. This is the coproduct *of categories*, and is distinct from a
   coproduct *object* inside a single category, formed via a universal cocone
   in Structure/Cocartesian.v. *)

Section Coproduct.

Context {C : Category}.
Context {D : Category}.

Local Set Warnings "-intuition-auto-with-star".

Program Definition Coproduct : Category := {|
  obj     := C + D;            (* tagged disjoint union of objects *)
  hom     := fun x y =>        (* within a summand; False across summands *)
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
