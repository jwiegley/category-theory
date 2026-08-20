Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.

Generalizable All Variables.

(** * The direct sum is the coproduct in CMon *)

(* Book: Mac Lane, "Categories for the Working Mathematician" (2nd ed.),
         §III.3, book p. 63 (maclane:III.3:remark1)
   Wikipedia: https://en.wikipedia.org/wiki/Biproduct

   Instance/CMon/Biproduct.v proved
   that the direct product of two commutative monoids is at once their
   product and their coproduct — [CMon_bi_is_product] and
   [CMon_bi_is_coproduct] at Instance/CMon/Biproduct.v:352 and :404, both
   in the ∃!-form, packaged as [CMon_Biproducts].  What it never did was
   say so in the vocabulary the rest of the library uses: there was no
   [Cartesian CMon] and no [Cocartesian CMon] anywhere.

   This file is that sentence, and it is DELIVERED WITH NO NEW PROOF AT
   ALL — two lines, both supplied by
   [:=], the whole content coming from Structure/Biproduct/Cartesian.v's
   generic bridge applied to the existing [CMon_Biproducts].  It is
   included because it is the bridge's cleanest demonstration: the
   donor's biproduct was already complete, so what the bridge adds is
   exactly and only the vocabulary.

   Instance/Ab/Coproduct.v and Instance/Mod/Coproduct.v are the same
   statement one and two layers up, where the donor's biproduct does NOT
   already exist and must be built; the three files together are Mac
   Lane's "direct sum" roster entry.

   WHAT IS NOT DELIVERED.  Nothing beyond the repackaging: no indexed
   coproducts, no [Additive CMon] (there are no inverses — that is what
   Instance/Ab.v adds), and no claim that the coproduct injections are
   monic. *)

#[export] Instance CMon_Cartesian : @Cartesian CMon :=
  @biproduct_Cartesian CMon CMon_Zero CMon_Biproducts.

#[export] Instance CMon_Cocartesian : @Cocartesian CMon :=
  @biproduct_Cocartesian CMon CMon_Zero CMon_Biproducts.

(** ** Strict identifications *)

(* The coproduct IS the product, the same object. *)
Example CMon_coprod_is_prod (M N : CMonObject) :
  @Coprod CMon CMon_Cocartesian M N
    = @product_obj CMon CMon_Cartesian M N := eq_refl.

Example CMon_coprod_obj (M N : CMonObject) :
  @Coprod CMon CMon_Cocartesian M N = CMon_product M N := eq_refl.

Example CMon_inl_is_CMon_inl (M N : CMonObject) :
  @inl CMon CMon_Cocartesian M N = CMon_inl M N := eq_refl.

Example CMon_inr_is_CMon_inr (M N : CMonObject) :
  @inr CMon CMon_Cocartesian M N = CMon_inr M N := eq_refl.

Example CMon_merge_is_copair (M N P : CMonObject)
  (f : M ~{CMon}~> P) (g : N ~{CMon}~> P) :
  @merge CMon CMon_Cocartesian P M N f g = CMon_copair f g := eq_refl.

Example CMon_exl_is_CMon_exl (M N : CMonObject) :
  @exl CMon CMon_Cartesian M N = CMon_exl M N := eq_refl.

Example CMon_exr_is_CMon_exr (M N : CMonObject) :
  @exr CMon CMon_Cartesian M N = CMon_exr M N := eq_refl.
