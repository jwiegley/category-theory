Require Import Category.Lib.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cocartesian.

Generalizable All Variables.

(** * Coproducts of setoids (disjoint union) *)

(* nLab: https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   The coproduct of two setoids in [Sets] is their disjoint union. The carrier
   is the sum type [carrier x + carrier y], and two elements are equivalent
   exactly when they sit in the same summand and are equivalent there: [inl z]
   and [inl w] agree iff [z ≈ w] in [x], [inr z] and [inr w] agree iff [z ≈ w]
   in [y], and elements drawn from different summands are never identified (the
   cross cases reduce to [False]). The injections are the constructors
   [inl : x ~> x + y] and [inr : y ~> x + y].

   The universal property is witnessed by copairing: given [f : x ~> z] and
   [g : y ~> z], the case-split map [fun s => match s with inl a => f a
   | inr b => g b end] is the unique morphism [x + y ~> z] with [fork f g ∘ inl
   ≈ f] and [fork f g ∘ inr ≈ g]. (Here [fork], [exl], [exr] are the
   product-of-[C^op] fields through which [Cocartesian] is defined, so they
   supply the coproduct's copairing and injections with arrows reversed.) *)

#[export]
Program Instance Sets_Cocartesian : @Cocartesian Sets := {
  product_obj := fun x y =>
    {| carrier := (carrier x + carrier y)%type
     ; is_setoid :=
         {| equiv := fun z w =>
              match z with
              | Datatypes.inl z =>
                match w with
                | Datatypes.inl w => @equiv _ x z w
                | Datatypes.inr _ => False
                end
              | Datatypes.inr z =>
                match w with
                | Datatypes.inl _ => False
                | Datatypes.inr w => @equiv _ y z w
                end
              end
          ; setoid_equiv := _
          |} |};
  fork := fun _ _ _ f g =>
    {| morphism := fun x =>
         match x with
         | Datatypes.inl x => f x
         | Datatypes.inr x => g x
         end |};
  exl := fun _ _ => {| morphism := Datatypes.inl |};
  exr := fun _ _ => {| morphism := Datatypes.inr |}
}.
Next Obligation.
  proper.
  destruct f, g; intuition.
  destruct y, x; intuition;
  destruct z; intuition.
Qed.
Next Obligation.
  proper.
  destruct x2; intuition.
Qed.
Next Obligation.
  simplify; intuition;
  now match goal with
    [ H : ∀ _ : _ + _, _ ≈ _ |- _ ] => rewrite H
  end.
Qed.
