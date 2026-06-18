Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.

Generalizable All Variables.

(** The comma category over the terminal category is the product category. *)

(* nLab: https://ncatlab.org/nlab/show/comma+category
   nLab: https://ncatlab.org/nlab/show/product+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category
   Wikipedia: https://en.wikipedia.org/wiki/Product_category

   For any functors F : C ⟶ 1 and G : D ⟶ 1 into the terminal category 1, the
   comma category (F ↓ G) is isomorphic in Cat to the product category C ∏ D:

       (F ↓ G) ≅[Cat] C ∏ D.

   An object of (F ↓ G) is a triple (c, d, h : F c ~> G d), but since 1 is
   terminal its only hom-set is the singleton poly_unit, so the mediating
   morphism h is forced and carries no information; an object is thus a pair
   (c, d). A morphism (c, d, h) ~> (c', d', h') is a pair (f, g) subject to the
   commuting square h' ∘ F f ≈ G g ∘ h, but that square lives in 1 where all
   morphisms are equal, so the condition is vacuous and a morphism is just a
   pair (f, g). Hence (F ↓ G) is exactly C ∏ D. The result does not depend on
   which F and G are chosen, only on the codomain being terminal: this is
   distinct from the special case in which the *domains* of the two functors
   are 1 (Wikipedia), where the comma category is instead the discrete category
   of morphisms between the two selected objects. *)

Section ProductComma.

(* Build the isomorphism (and its functors, naturals, and proofs) by repeatedly
   peeling the head connective of the goal and discharging the leaf with the
   appropriate category tactic. *)
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
