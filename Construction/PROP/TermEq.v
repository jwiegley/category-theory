Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.

From Stdlib Require Import Arith.

Generalizable All Variables.

Local Open Scope nat_scope.

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
               (T_comp (T_braid n1 n2) (T_tens f g))

  (** Strict-PROP unit on tensor: tensoring with the empty term
      [T_id 0] on the LEFT is an identity operation modulo the
      definitional equation [0 + n = n].

      This axiom is the analogue of the strict-unit law in a
      [StrictMonoidal] category.  In a generic [Monoidal] category
      it would be a natural ISOMORPHISM (the left unitor), not an
      equation; PROPs are strict on the nose, so we assert it as
      an equation in [TermEq].

      We state it as commuting with arity-zero through a [T_id]
      composition wrapper, so the types line up: both sides have
      type [Term S (0 + n) n]. *)
  | TE_tens_id0_left :
      forall {m n : nat} (f : Term S m n),
        TermEq (T_tens (T_id 0) f) f

  (** Strict-PROP unit on the right: dually, tensoring with [T_id 0]
      on the RIGHT is identity modulo [n + 0 = n].

      Stated in transport form via [eq_rect] over the
      arity-equations.  Concretely [T_tens f (T_id 0)] has type
      [Term S (m + 0) (n + 0)]; we transport it to [Term S m n] using
      [Nat.add_0_r] on both indices, and assert the result equals [f]. *)
  | TE_tens_id0_right :
      forall {m n : nat} (f : Term S m n),
        TermEq (eq_rect (Nat.add n O)
                        (fun k => Term S (Nat.add m O) k)
                        (T_tens f (T_id O))
                        n
                        (Nat.add_0_r n))
               (eq_rect_r
                  (fun k => Term S k n)
                  f
                  (Nat.add_0_r m))

  (** Strict-PROP associativity of tensor.  Transport form. *)
  | TE_tens_assoc :
      forall {m1 n1 m2 n2 m3 n3 : nat}
             (f : Term S m1 n1) (g : Term S m2 n2) (h : Term S m3 n3),
        TermEq (eq_rect (Nat.add (Nat.add n1 n2) n3)
                        (fun k => Term S (Nat.add (Nat.add m1 m2) m3) k)
                        (T_tens (T_tens f g) h)
                        (Nat.add n1 (Nat.add n2 n3))
                        (eq_sym (Nat.add_assoc n1 n2 n3)))
               (eq_rect_r
                  (fun k => Term S k (Nat.add n1 (Nat.add n2 n3)))
                  (T_tens f (T_tens g h))
                  (eq_sym (Nat.add_assoc m1 m2 m3)))

  (** ** Hexagon axioms for block braids

      In a strict symmetric monoidal category the braid decomposes
      additively in either argument (Mac Lane CWM Ch.VII §7;
      Joyal–Street §2; Selinger §3.2):

        σ_{m+n,p} ≈ (σ_{m,p} ⊕ id_n) ⊙ (id_m ⊕ σ_{n,p})       (hex-left)
        σ_{m,n+p} ≈ (id_n ⊕ σ_{m,p}) ⊙ (σ_{m,n} ⊕ id_p)       (hex-right)

      The LHS and RHS do not have matching types on the nose because
      addition on [nat] is associative only up to propositional [=],
      so both equations are stated in transport form via [eq_rect]
      against [Nat.add_assoc], analogous to [TE_tens_assoc].

      Without these, e.g. [T_braid 3 2] is not provably equal to the
      layered composite of single-wire swaps, and the [SymmetricMonoidal]
      instance on [FreeCat S] cannot discharge [hexagon_to] /
      [hexagon_from] for non-trivial arities. *)

  | TE_braid_hex_left :
      forall (m n p : nat),
        TermEq
          (* LHS: σ_{m+n,p} with source cast (m+n)+p → m+(n+p). *)
          (eq_rect ((m + n) + p)
                   (fun s => Term S s (p + (m + n)))
                   (T_braid (m + n) p)
                   (m + (n + p))
                   (eq_sym (Nat.add_assoc m n p)))
          (* RHS: (σ_{m,p} ⊕ id_n) ⊙ (id_m ⊕ σ_{n,p})
             — the outer term needs both source and target casts to
             reach types Term S (m+(p+n)) (p+(m+n)); the inner term
             already has type Term S (m+(n+p)) (m+(p+n)). *)
          (T_comp
             (eq_rect ((p + m) + n)
                      (fun t => Term S (m + (p + n)) t)
                      (eq_rect ((m + p) + n)
                               (fun s => Term S s ((p + m) + n))
                               (T_tens (T_braid m p) (T_id n))
                               (m + (p + n))
                               (eq_sym (Nat.add_assoc m p n)))
                      (p + (m + n))
                      (eq_sym (Nat.add_assoc p m n)))
             (T_tens (T_id m) (T_braid n p)))

  | TE_braid_hex_right :
      forall (m n p : nat),
        TermEq
          (* LHS: σ_{m,n+p} with target cast (n+p)+m → n+(p+m). *)
          (eq_rect ((n + p) + m)
                   (fun t => Term S (m + (n + p)) t)
                   (T_braid m (n + p))
                   (n + (p + m))
                   (eq_sym (Nat.add_assoc n p m)))
          (* RHS: (id_n ⊕ σ_{m,p}) ⊙ (σ_{m,n} ⊕ id_p)
             — outer source: n+(m+p) → (n+m)+p (Nat.add_assoc forward);
               inner source: (m+n)+p → m+(n+p) (eq_sym). *)
          (T_comp
             (eq_rect (n + (m + p))
                      (fun s => Term S s (n + (p + m)))
                      (T_tens (T_id n) (T_braid m p))
                      ((n + m) + p)
                      (Nat.add_assoc n m p))
             (eq_rect ((m + n) + p)
                      (fun s => Term S s ((n + m) + p))
                      (T_tens (T_braid m n) (T_id p))
                      (m + (n + p))
                      (eq_sym (Nat.add_assoc m n p))))

  (** ** Unit-braid coherence

      In any symmetric monoidal category the braid involving the unit
      object collapses to the unitor: [σ_{I,X} = λ_X ∘ ρ_X^{-1}].  In
      the strict-PROP setting on [nat], this becomes
      [T_braid 0 n ≈ T_id n] and [T_braid n 0 ≈ T_id n] modulo the
      arity equation [n + 0 = n] (which is propositional, not
      definitional — [Nat.add] is left-strict only). *)

  | TE_braid_unit_left :
      forall (n : nat),
        TermEq
          (* T_braid 0 n : Term S (0+n) (n+0) = Term S n (n+0).
             Cast the target n+0 → n. *)
          (eq_rect (n + 0) (fun t => Term S n t)
                   (T_braid 0 n)
                   n
                   (Nat.add_0_r n))
          (T_id n)

  | TE_braid_unit_right :
      forall (n : nat),
        TermEq
          (* T_braid n 0 : Term S (n+0) (0+n) = Term S (n+0) n.
             Cast the source n+0 → n. *)
          (eq_rect (n + 0) (fun s => Term S s n)
                   (T_braid n 0)
                   n
                   (Nat.add_0_r n))
          (T_id n).

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
Arguments TE_tens_id0_left {S m n}.
Arguments TE_tens_id0_right {S m n}.
Arguments TE_tens_assoc {S m1 n1 m2 n2 m3 n3}.
Arguments TE_braid_hex_left {S}.
Arguments TE_braid_hex_right {S}.
Arguments TE_braid_unit_left {S}.
Arguments TE_braid_unit_right {S}.
