Require Import Category.Lib.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cartesian.

Generalizable All Variables.

(** * Cartesian (binary product) structure on [Sets] *)

(* nLab: https://ncatlab.org/nlab/show/product
   nLab: https://ncatlab.org/nlab/show/setoid
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   The category [Sets] of setoids has binary products, computed as the
   product setoid. The product of two setoids x and y has

       carrier:  carrier x * carrier y     (the type of ordered pairs)
            ≈:  (a₁, b₁) ≈ (a₂, b₂)  :=  a₁ ≈ a₂  ∧  b₁ ≈ b₂

   i.e. the carrier is the product type and equivalence is componentwise (the
   `*` joining the two [equiv] proofs is conjunction, the product in [Type]).
   This is the standard product in Set, refined to setoids so that the
   componentwise relation is again an equivalence.

   The two projections [exl], [exr] are the underlying [fst], [snd] (which
   respect `≈` by definition of the componentwise relation), and the pairing
   ⟨f, g⟩ ([fork]) of f : x ~> y and g : x ~> z is x ↦ (f x, g x). These
   satisfy the universal mapping property of [Cartesian]: ⟨f, g⟩ is the unique
   map h with exl ∘ h ≈ f and exr ∘ h ≈ g, since equivalence of pairs is exactly
   componentwise equivalence. *)

#[export]
Program Instance Sets_Cartesian : @Cartesian Sets := {
  product_obj := fun x y =>
    {| carrier := (carrier x * carrier y)%type
     ; is_setoid :=
         {| equiv := fun z w =>
                       @equiv _ x (fst z) (fst w) *
                       @equiv _ y (snd z) (snd w)
          ; setoid_equiv := _
          |} |};
  fork := fun _ _ _ f g => {| morphism := fun x => (f x, g x) |};
  exl := fun _ _ => {| morphism := fst |};
  exr := fun _ _ => {| morphism := snd |}
}.
Next Obligation. proper; apply proper_morphism; assumption. Qed.
Next Obligation. all:firstorder. Qed.
