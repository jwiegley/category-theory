Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.CastTensor.

From Coq Require Import Arith.

Generalizable All Variables.

(** * Naturality lemmas for the structural isomorphisms *)

(* nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   nLab: https://ncatlab.org/nlab/show/braided+monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category

   Restated in library notation (writing [g ⊙ f] for [T_comp g f], the
   diagrammatic "g after f", and [f ⊕ g] for [T_tens f g]):

     - braid naturality: σ slides past a tensor of two morphisms,
         (g ⊕ f) ⊙ σ_{m1,m2} ≈ σ_{n1,n2} ⊙ (f ⊕ g)
       for f : m1 ⇒ n1, g : m2 ⇒ n2.  This is exactly the naturality
       square of the symmetry σ_{a,b} : a ⊗ b → b ⊗ a, matching the
       source equation (g ⊗ f) ∘ σ_{a,b} = σ_{a',b'} ∘ (f ⊗ g).
     - braid involution (symmetry): σ_{n,m} ⊙ σ_{m,n} ≈ id_{m+n},
       the source's σ_{B,A} ∘ σ_{A,B} = id_{A⊗B}.
     - the interchange law (bifunctoriality of ⊕) lives in [TermEq] as
       [TE_interchange]; here it is used implicitly through the tensor
       of morphisms appearing in braid naturality.

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

(** ** Strict-PROP right-unit at the [T_cast] level

    [TE_tens_id0_right] states the right-unit law in [eq_rect]
    transport form.  We can extract its content as a [T_cast]
    sandwich: pre/post-composing by appropriate casts gives a
    direct [T_tens f (T_id 0) ↔ f]-style equation. *)

(* Note: a clean [T_cast]-form right-unit lemma — bridging
   [TE_tens_id0_right]'s [eq_rect] transport form to a sandwiched
   [T_cast] composition — requires first generalising over the
   arity equation [n + 0 = n] rather than destructing it in place.
   That is exactly what the transport bridges [eq_rect_cod_cast]
   and [eq_rect_r_dom_cast] of [Construction/PROP/Monoidal.v] do:
   they convert the [eq_rect] spelling wholesale, and the Monoidal
   instance derives its [right_unit_natural] there in full
   generality.

   The arity-specialised lemmas below ([tens_id0_right_at_0],
   [tens_id0_right_at]) treat the case where the arity is
   syntactically known, so the [eq_rect] collapses by computation
   (after UIP on [nat] discharges the opaque [Nat.add_0_r]); for
   the general naturality square, use [right_unit_natural] in
   [Construction/PROP/Monoidal.v]. *)

(** ** Right-unit at the trivial arity (0 + 0 = 0)

    When both arities are 0, [Nat.add_0_r] reduces definitionally
    and [T_tens f (T_id 0) ≈ f] follows from [TE_tens_id0_right]
    after the [eq_rect] collapses by [reflexivity]. *)

Lemma tens_id0_right_at_0 (f : Term S 0 0) :
  TermEq S (T_tens f (T_id 0)) f.
Proof.
  pose proof (TE_tens_id0_right f) as Hr.
  simpl in Hr.
  (* [Nat.add_0_r 0] reduces by [cbn]/[simpl] to [eq_refl] only if
     [Nat.add_0_r] is transparent.  In stdlib it is opaque, so we
     need to rewrite via UIP. *)
  unfold eq_rect_r in Hr; simpl in Hr.
  rewrite (Eqdep_dec.UIP_dec PeanoNat.Nat.eq_dec
            (Nat.add_0_r 0) eq_refl) in Hr.
  simpl in Hr.
  exact Hr.
Qed.

(** ** Arity-specialised right-unit at any concrete (n, n) *)

Lemma tens_id0_right_at (n : nat) (f : Term S n n) :
  TermEq S
    (eq_rect (n + 0) (fun k => Term S (n + 0) k)
             (T_tens f (T_id 0)) n (Nat.add_0_r n))
    (eq_rect_r (fun k => Term S k n) f (Nat.add_0_r n)).
Proof. exact (TE_tens_id0_right f). Qed.

(** ** Tensor-associativity at any concrete arities *)

Lemma tens_assoc_at {m1 n1 m2 n2 m3 n3 : nat}
                    (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3) :
  TermEq S
    (eq_rect (Nat.add (Nat.add n1 n2) n3)
             (fun k => Term S (Nat.add (Nat.add m1 m2) m3) k)
             (T_tens (T_tens f g) h)
             (Nat.add n1 (Nat.add n2 n3))
             (eq_sym (Nat.add_assoc n1 n2 n3)))
    (eq_rect_r
       (fun k => Term S k (Nat.add n1 (Nat.add n2 n3)))
       (T_tens f (T_tens g h))
       (eq_sym (Nat.add_assoc m1 m2 m3))).
Proof. exact (TE_tens_assoc f g h). Qed.

(** ** Braid naturality, exposed as a named lemma

    Direct restatement of [TE_braid_natural] with a friendly name,
    for use outside the instance files.  The instance files
    themselves ([Construction/PROP/Braided.v],
    [Construction/PROP/Presentation.v]) deliberately apply the
    constructor [TE_braid_natural] directly and do not import this
    file: the name [braid_natural] would shadow the
    [BraidedMonoidal] projection of the same name in their record
    literals. *)

Lemma braid_natural {m1 n1 m2 n2 : nat}
                    (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_tens g f) (T_braid m1 m2))
           (T_comp (T_braid n1 n2) (T_tens f g)).
Proof. apply TE_braid_natural. Qed.

(** ** Braid involution, exposed as a named lemma

    Direct restatement of [TE_braid_invol]:
        σ_{n,m} ⊙ σ_{m,n} ≈ id_{m+n}
    for use outside the instance files.  As with [braid_natural]
    above, [Construction/PROP/Symmetric.v] deliberately applies the
    constructor [TE_braid_invol] directly rather than importing
    this file, since the name [braid_invol] would shadow the
    [SymmetricMonoidal] projection of the same name in its record
    literal. *)

Lemma braid_invol (m n : nat) :
  TermEq S (T_comp (T_braid n m) (T_braid m n)) (T_id (m + n)).
Proof. apply TE_braid_invol. Qed.

End Naturality.
