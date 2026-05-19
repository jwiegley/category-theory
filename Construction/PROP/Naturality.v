Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.CastTensor.

From Stdlib Require Import Arith.

Generalizable All Variables.

(** * Naturality lemmas for the structural isomorphisms

    Algebraic facts about [Term S] that the Monoidal instance on
    [FreeCat S] needs.  Each lemma states a strict-PROP naturality
    equation in terms of [T_cast] (the structural map) and [T_tens]
    (the bimap).

    The proofs rely on:
      - [TE_tens_id0_left] for the strict left-unit law
      - [Nat.add_0_l] being DEFINITIONAL so [T_cast (Nat.add_0_l n)
        : Term S (0+n) n] is the [T_cast eq_refl]-equivalent identity *)

Section Naturality.

Context (S : Signature).

Open Scope nat_scope.

(** ** Left-unitor naturality

    Goal (in [FreeCat S]):
      g ⊙ unit_left ≈ unit_left ⊙ bimap id g
    expanded to [Term]:
      g ⊙ T_cast (Nat.add_0_l x) ≈ T_cast (Nat.add_0_l y) ⊙ (T_id 0 ⊕ g) *)

Lemma left_unit_natural {x y : nat} (g : Term S x y) :
  TermEq S (T_comp g (T_cast (Nat.add_0_l x)))
           (T_comp (T_cast (Nat.add_0_l y)) (T_tens (T_id 0) g)).
Proof.
  (* [Nat.add_0_l n : 0+n = n] is opaque, but by UIP on [nat] (which
     has decidable equality), every such cast equals [T_cast eq_refl]
     = [T_id n] via [T_cast_id]. *)
  rewrite (T_cast_id (Nat.add_0_l x)).
  rewrite (T_cast_id (Nat.add_0_l y)).
  apply TE_trans with g.
  - apply TE_id_right.
  - apply TE_sym.
    apply TE_trans with (T_tens (T_id 0) g).
    + apply TE_id_left.
    + apply TE_tens_id0_left.
Qed.

(** ** Left-unitor naturality, the [from]-direction

    Goal:  bimap id g ⊙ unit_left⁻¹ ≈ unit_left⁻¹ ⊙ g
    expanded:
      (T_id 0 ⊕ g) ⊙ T_cast (eq_sym (Nat.add_0_l x))
        ≈ T_cast (eq_sym (Nat.add_0_l y)) ⊙ g *)

Lemma left_unit_natural_from {x y : nat} (g : Term S x y) :
  TermEq S (T_comp (T_tens (T_id 0) g) (T_cast (eq_sym (Nat.add_0_l x))))
           (T_comp (T_cast (eq_sym (Nat.add_0_l y))) g).
Proof.
  rewrite (T_cast_id (eq_sym (Nat.add_0_l x))).
  rewrite (T_cast_id (eq_sym (Nat.add_0_l y))).
  apply TE_trans with (T_tens (T_id 0) g).
  - apply TE_id_right.
  - apply TE_trans with g.
    + apply TE_tens_id0_left.
    + apply TE_sym, TE_id_left.
Qed.

(** ** Simple corollaries of the strict-unit axioms *)

(** Tensoring two identity terms with [T_id 0] on the left collapses
    to a single identity term. *)
Lemma tens_id0_id (n : nat) :
  TermEq S (T_tens (T_id 0) (T_id n)) (T_id n).
Proof. apply TE_tens_id0_left. Qed.

(** Repeated tensor of [T_id 0] on the left is still [T_id 0]. *)
Lemma tens_id0_id0 :
  TermEq S (T_tens (T_id 0) (T_id 0)) (T_id 0).
Proof. apply TE_tens_id0_left. Qed.

End Naturality.
