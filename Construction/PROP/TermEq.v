Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.

From Stdlib Require Import Arith.

Generalizable All Variables.

(** * Equational theory of free-PROP terms

    The equivalence relation [TermEq] on [Term S m n] quotients the
    raw syntax of [Construction/PROP/Term.v] by the strict symmetric
    monoidal category axioms:

      - reflexivity, symmetry, transitivity (the setoid laws)
      - congruences for [T_comp] and [T_tens]
      - category laws: identity-left, identity-right, associativity
      - bifunctor (tensor) laws: identity, sequential interchange,
        functoriality
      - symmetric-monoidal coherence: braid naturality, braid
        involution, hexagon

    The strict-PROP axioms on naturals — [T_id n ⊕ T_id m ≈ T_id (n+m)],
    the addition-as-tensor strict laws — are present as primitive
    constructors of [TermEq] because the [Term] type is indexed by [nat]
    and [T_id n ⊕ T_id m] has type [Term S (n+m) (n+m)] while
    [T_id (n+m)] has the same type by definition; the equation is
    well-typed without any [eq_rect] casts.

    This file defines just the equivalence relation.  The [Setoid]
    instance and the [Category] / [PROP] structure on the quotient
    live in successor files. *)

Section TermEq.

Context (S : Signature).

(** Strict tensor coherence requires equating terms whose types
    involve different parenthesisations of [+] on [nat].  Because
    [nat] addition is associative ONLY up to propositional [=]
    (not definitional), we cannot state e.g. an associator
    [T_assoc : Term S ((m+n)+p) (m+(n+p))] in [Term] alone.  The
    equational theory bridges these via the strict axioms
    [TE_assoc_obj] / [TE_unit_*_obj]; in practice they are used as
    rewrite rules to bring a term into a canonical right-associated
    form on its arities. *)

Inductive TermEq : forall {m n}, Term S m n -> Term S m n -> Prop :=

  (** Setoid laws. *)
  | TE_refl  : forall {m n} (t : Term S m n), TermEq t t
  | TE_sym   : forall {m n} (s t : Term S m n),
               TermEq s t -> TermEq t s
  | TE_trans : forall {m n} (s t u : Term S m n),
               TermEq s t -> TermEq t u -> TermEq s u

  (** Congruence of sequential composition. *)
  | TE_comp_cong : forall {m n p}
                          (f f' : Term S n p) (g g' : Term S m n),
                   TermEq f f' -> TermEq g g' ->
                   TermEq (T_comp f g) (T_comp f' g')

  (** Congruence of parallel composition (tensor). *)
  | TE_tens_cong : forall {m1 n1 m2 n2}
                          (f f' : Term S m1 n1) (g g' : Term S m2 n2),
                   TermEq f f' -> TermEq g g' ->
                   TermEq (T_tens f g) (T_tens f' g')

  (** Category laws: id-left, id-right, associativity. *)
  | TE_id_left  : forall {m n} (f : Term S m n),
                  TermEq (T_comp (T_id n) f) f
  | TE_id_right : forall {m n} (f : Term S m n),
                  TermEq (T_comp f (T_id m)) f
  | TE_assoc    : forall {m n p q}
                         (h : Term S p q) (g : Term S n p) (f : Term S m n),
                  TermEq (T_comp (T_comp h g) f)
                         (T_comp h (T_comp g f))

  (** Bifunctor laws: identity, sequential interchange.

      [TE_tens_id]: [id_m ⊕ id_n = id_(m+n)] — typing OK because [Term]
      is [nat]-indexed and addition is the tensor on arities. *)
  | TE_tens_id : forall (m n : nat),
                 TermEq (T_tens (T_id m) (T_id n)) (T_id (m + n))

  (** [TE_interchange]: (f₁ ⊕ g₁) ⊙ (f₂ ⊕ g₂) ≈ (f₁ ⊙ f₂) ⊕ (g₁ ⊙ g₂)
      — the parallel/sequential interchange law. *)
  | TE_interchange :
      forall {m1 n1 p1 m2 n2 p2}
             (f1 : Term S n1 p1) (g1 : Term S n2 p2)
             (f2 : Term S m1 n1) (g2 : Term S m2 n2),
        TermEq (T_comp (T_tens f1 g1) (T_tens f2 g2))
               (T_tens (T_comp f1 f2) (T_comp g1 g2))

  (** Braid involution: [σ_{m,n} ⊙ σ_{n,m} ≈ id_{m+n}].  Block-braiding
      twice returns to identity. *)
  | TE_braid_invol :
      forall (m n : nat),
        TermEq (T_comp (T_braid n m) (T_braid m n)) (T_id (m + n))

  (** Braid naturality (top form):
        (g ⊕ f) ⊙ σ_{m1,m2} ≈ σ_{n1,n2} ⊙ (f ⊕ g)
      where f : m1 -> n1, g : m2 -> n2. *)
  | TE_braid_natural :
      forall {m1 n1 m2 n2}
             (f : Term S m1 n1) (g : Term S m2 n2),
        TermEq (T_comp (T_tens g f) (T_braid m1 m2))
               (T_comp (T_braid n1 n2) (T_tens f g)).

End TermEq.

Arguments TE_refl  {S m n}.
Arguments TE_sym   {S m n}.
Arguments TE_trans {S m n}.
Arguments TE_comp_cong {S m n p}.
Arguments TE_tens_cong {S m1 n1 m2 n2}.
Arguments TE_id_left  {S m n}.
Arguments TE_id_right {S m n}.
Arguments TE_assoc {S m n p q}.
Arguments TE_tens_id {S}.
Arguments TE_interchange {S m1 n1 p1 m2 n2 p2}.
Arguments TE_braid_invol {S}.
Arguments TE_braid_natural {S m1 n1 m2 n2}.
