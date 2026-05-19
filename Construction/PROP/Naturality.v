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

(** ** Braid naturality, exposed as a named lemma

    Direct restatement of [TE_braid_natural] with a friendly name.
    Downstream callers building the SymmetricMonoidal instance on
    [FreeCat S] use this to discharge [braid_natural]. *)

Lemma braid_natural {m1 n1 m2 n2 : nat}
                    (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_tens g f) (T_braid m1 m2))
           (T_comp (T_braid n1 n2) (T_tens f g)).
Proof. apply TE_braid_natural. Qed.

(** ** Braid involution, exposed as a named lemma

    Direct restatement of [TE_braid_invol]:
        σ_{n,m} ⊙ σ_{m,n} ≈ id_{m+n}
    Downstream callers building the SymmetricMonoidal instance use
    this to discharge [braid_invol]. *)

Lemma braid_invol (m n : nat) :
  TermEq S (T_comp (T_braid n m) (T_braid m n)) (T_id (m + n)).
Proof. apply TE_braid_invol. Qed.

End Naturality.
