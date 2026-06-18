Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.

From Coq Require Import Arith.

Generalizable All Variables.

(** * Parallel-composition bifunctor on FreeCat *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   The monoidal product of a (strict, symmetric) monoidal category is a
   bifunctor [⊗ : C ∏ C ⟶ C].  For the free PROP [FreeCat S] this is the
   parallel composition of string diagrams, with arities given by addition:

     - on objects:    [(m, n) ↦ m + n]   (tensor on objects is [Nat.add])
     - on morphisms:  [(f, g) ↦ T_tens f g], so [f : m1 ~> n1] and
                       [g : m2 ~> n2] yield [f ⊗ g : m1 + m2 ~> n1 + n2]

   The bifunctor laws (a functor out of the product category [FreeCat S ∏
   FreeCat S]) follow from the [TE_tens_*] constructors of the [TermEq]
   quotient relation:
     - respectfulness (fmap_respects):  [TE_tens_cong]
     - identity preservation (fmap_id): [TE_tens_id]
         [id_m ⊗ id_n ≈ id_(m+n)]
     - composition preservation (fmap_comp), i.e. the middle-four
       interchange [(f1 ⊙ f2) ⊗ (g1 ⊙ g2) ≈ (f1 ⊗ g1) ⊙ (f2 ⊗ g2)]:
       [TE_interchange] (used via [TE_sym], since the constructor states
       the reverse orientation). *)

Section FreeTensor.

Context (S : Signature).

(** The tensor bifunctor on FreeCat S. *)
Program Definition FreeCat_Tensor : FreeCat S ∏ FreeCat S ⟶ FreeCat S := {|
  fobj := fun p => Nat.add (fst p) (snd p);
  fmap := fun p q m =>
    @T_tens S (fst p) (fst q) (snd p) (snd q) (fst m) (snd m)
|}.
Next Obligation.
  unfold Proper, respectful.
  intros [f1 f2] [g1 g2] [Hf Hg]; simpl in *.
  apply TE_tens_cong; assumption.
Qed.
Next Obligation.
  apply TE_tens_id.
Qed.
Next Obligation.
  apply TE_sym, TE_interchange.
Qed.

End FreeTensor.

Arguments FreeCat_Tensor S : assert.
