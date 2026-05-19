Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.

From Stdlib Require Import Arith.

Generalizable All Variables.

(** * Parallel-composition bifunctor on FreeCat

    The tensor on [FreeCat S] takes:
      - on objects: [(m, n) -> m + n]
      - on morphisms: [(f, g) -> T_tens f g]

    Functoriality follows from the [TE_tens_*] constructors of the
    quotient relation:
      - identity preservation:    [TE_tens_id]
      - composition preservation: [TE_interchange] (parallel/sequential)
      - respectfulness:           [TE_tens_cong] *)

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
