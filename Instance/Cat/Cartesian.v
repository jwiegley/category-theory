Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** Cat has binary products, given by the product category. *)

(* nLab:      https://ncatlab.org/nlab/show/Cat
   nLab:      https://ncatlab.org/nlab/show/product+category
   Wikipedia: https://en.wikipedia.org/wiki/Product_category
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

   The categorical product of two categories C and D in Cat is the product
   category C ∏ D (Construction/Product.v): objects are pairs (c, d), morphisms
   are pairs (f, g), and composition is componentwise. This file equips Cat
   with the binary-product half of its [Cartesian] structure, taking

       product_obj C D := C ∏ D,

   with projection functors exl := Fst (π₁, (c, d) ↦ c) and exr := Snd (π₂,
   (c, d) ↦ d), and pairing ⟨F, G⟩ := fork F G the functor x ↦ (F x, G x).
   The class field [ump_products] discharged below is the universal mapping
   property: exl ∘ ⟨F, G⟩ ≅ F, exr ∘ ⟨F, G⟩ ≅ G, and ⟨F, G⟩ is the unique
   such functor up to natural isomorphism (the hom-equivalence in Cat is
   natural isomorphism, not on-the-nose equality, so these are ≅ in [Cat]).

   This supplies only the *binary* products. The nullary product, the terminal
   object of Cat, is the terminal category 1 (Instance/One.v, [Cat_Terminal]);
   the two together make Cat a category with finite products. *)

Local Set Warnings "-intuition-auto-with-star".

#[export]
Program Instance Cat_Cartesian : @Cartesian Cat := {
  product_obj := @Product;
  fork := fun _ _ _ F G =>
            {| fobj := fun x => (F x, G x)
             ; fmap := fun _ _ f => (fmap[F] f, fmap[G] f) |};
  exl := fun _ _ =>
            {| fobj := fst
             ; fmap := fun _ _ => fst |};
  exr := fun _ _ =>
            {| fobj := snd
             ; fmap := fun _ _ => snd |};
}.
Next Obligation. proper; apply fmap_respects; auto. Qed.
Next Obligation. simplify; rewrite !fmap_comp; intuition; auto with *. Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  proper.
  - isomorphism; simpl; split.
    + apply x2.
    + apply x1.
    + apply (from (x2 _)).
    + apply (from (x1 _)).
    + apply iso_to_from.
    + apply iso_to_from.
    + apply iso_from_to.
    + apply iso_from_to.
  - apply e0.
  - apply e.
Qed.
Next Obligation.
  rename x into A.
  rename y into B.
  rename z into C.
  split; intros; simplify.
  - isomorphism.
    + exact (fst (to (x x0))).
    + exact (fst (from (x x0))).
    + exact (fst (iso_to_from (x x0))).
    + exact (fst (iso_from_to (x x0))).
  - apply (fst (e _ _ _)).
  - isomorphism.
    + exact (snd (to (x x0))).
    + exact (snd (from (x x0))).
    + exact (snd (iso_to_from (x x0))).
    + exact (snd (iso_from_to (x x0))).
  - apply (snd (e _ _ _)).
  - isomorphism.
    + exact(to (x0 x1), to (x x1)).
    + exact(from (x0 x1), from (x x1)).
    + exact(iso_to_from (x0 x1), iso_to_from (x x1)).
    + exact(iso_from_to (x0 x1), iso_from_to (x x1)).
  - apply e0.
  - apply e.
Qed.
