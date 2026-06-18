Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Coproduct.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** Cat has finite coproducts: the coproduct of two categories. *)

(* nLab:      https://ncatlab.org/nlab/show/Cat
   nLab:      https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   Cat has finite coproducts. The coproduct of two categories C and D is the
   disjoint-union (coproduct) category C ∐ D of Construction/Coproduct.v, and
   here it is exhibited as the categorical coproduct in Cat:

       product_obj := C ∐ D    (the coproduct object, read in Cat^op)
       exl         := Inl       (inclusion functor C ⟶ C ∐ D)
       exr         := Inr       (inclusion functor D ⟶ C ∐ D)
       fork F G    := [F, G]    (copairing / case functor C ∐ D ⟶ E)

   Because [Cocartesian C] is by definition [Cartesian (C^op)] (a coproduct in
   C is a product in C^op, dualizing all arrows), this instance is literally a
   proof that Cat^op is Cartesian: the product fields of Cat^op are the
   coproduct fields of Cat, and [ump_products] read in Cat^op is the universal
   property of the coproduct -- a functor C ∐ D ⟶ E is uniquely the case
   functor [F, G] of a pair of functors F : C ⟶ E and G : D ⟶ E.

   The copairing's action on a hom is forced by the disjoint union: within a
   summand it runs F (resp. G), and the cross-summand hom-sets are empty (False
   in Construction/Coproduct.v), discharged here by [False_rect].

   The nullary coproduct, the initial object of Cat, is the empty category 0
   (Instance/Zero.v); it is supplied separately by [Initial] and is not a field
   of this binary-coproduct class. *)

#[export]
Program Instance Cat_Cocartesian : @Cocartesian Cat := {
  product_obj := @Coproduct;
  fork := fun _ _ _ F G =>
    {| fobj := fun x =>
                 match x with
                 | Datatypes.inl x => F x
                 | Datatypes.inr x => G x
                 end
     ; fmap := fun x y f =>
                 match x with
                 | Datatypes.inl x =>
                   match y with
                   | Datatypes.inl y => _
                   | Datatypes.inr y => False_rect _ _
                   end
                 | Datatypes.inr x =>
                   match y with
                   | Datatypes.inl y => False_rect _ _
                   | Datatypes.inr y => _
                   end
                 end |};
  exl := fun _ _ =>
            {| fobj := Datatypes.inl
             ; fmap := fun _ _ => _ |};
  exr := fun _ _ =>
            {| fobj := Datatypes.inr
             ; fmap := fun _ _ => _ |};
}.
Next Obligation. exact (fmap f). Defined.
Next Obligation. exact (fmap f). Defined.
Next Obligation.
  proper.
  destruct x, y; simpl in *;
  solve [ apply fmap_respects; auto | contradiction ].
Qed.
Next Obligation.
  destruct x; simpl in *; cat.
Qed.
Next Obligation.
  destruct x, y, z; simpl in *; try tauto;
  apply fmap_comp.
Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  proper.
  destruct x3, y1; simpl; auto; tauto.
Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  split; intros; simplify.
  - apply (e (Datatypes.inl x0) (Datatypes.inl y)).
  - apply (e (Datatypes.inr x0) (Datatypes.inr y)).
  - destruct x1; auto.
  - destruct x1, y.
    + apply e0; tauto.
    + tauto.
    + tauto.
    + apply e; tauto.
Qed.
