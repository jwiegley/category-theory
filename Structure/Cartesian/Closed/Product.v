Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/product+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   The product C ∏ D of two cartesian closed categories is again cartesian
   closed, with all of the structure computed componentwise. Neither
   reference states this closure result directly; it is the standard
   corollary that limits and exponentials in a product category are taken
   factorwise (see [product+category]: objects, morphisms, and composition
   of C ∏ D are pairs handled componentwise).

   Recall from [Closed] that exponent_obj x y is displayed as y ^ x. The
   exponential of (c, d) over (c', d') is therefore taken in each factor:

       (e, f) ^ (c, d) = (e ^ c, f ^ d)

   so [exponent_obj (c,d) (e,f)] = (fst·^fst·, snd·^snd·) below. The
   product-exponential adjunction (- × y) ⊣ (- ^ y) holds factorwise: the
   currying iso Hom((c,d)×(c',d'), e) ≅ Hom((c,d), e^(c',d')) is the
   pointwise pairing of the two component isos [exp_iso] of C and D, so
   evaluation and currying both act componentwise. *)

Section ProductClosed.

Context {C : Category}.
Context {D : Category}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.
Context `{@Closed C _}.
Context `{@Closed D _}.

Program Instance Product_Closed : @Closed (C ∏ D) Product_Cartesian := {
  (* internal hom, componentwise: (e,f) ^ (c,d) = (e^c, f^d) *)
  exponent_obj := fun x y => (fst y ^ fst x, snd y ^ snd x);
  (* currying iso, the factorwise pairing of the component exp_iso's *)
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f =>
                    (to exp_iso (fst f), to exp_iso (snd f)) |}
     ; from := {| morphism := fun f =>
                    (from exp_iso (fst f), from exp_iso (snd f)) |} |}
}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. split; exact (iso_to_from (@exp_iso _ _ _ _ _ _) _). Qed.
Next Obligation. split; exact (iso_from_to (@exp_iso _ _ _ _ _ _) _). Qed.

End ProductClosed.
