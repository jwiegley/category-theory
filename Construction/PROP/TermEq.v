Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.

From Coq Require Import Arith.

Generalizable All Variables.

Local Open Scope nat_scope.

(** * Equational theory of free-PROP terms *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   The equivalence relation [TermEq] on [Term S m n] quotients the
   raw syntax of [Construction/PROP/Term.v] by the strict symmetric
   monoidal category axioms.  The quotient [Term S / TermEq] is the
   free PROP (= free strict symmetric monoidal category whose objects
   are the naturals under [+]) on the signature [S].

   In library notation, with [⊙ = T_comp], [⊕ = T_tens],
   [id = T_id], [σ = T_braid], the constructors below assert:

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
    live in successor files.

    In a STRICT symmetric monoidal category the associator and unitors
    are identities, so the pentagon and triangle coherences hold on the
    nose and the only substantive coherences left are the hexagon and
    the symmetry/involution equation [σ_{n,m} ⊙ σ_{m,n} ≈ id] (cf. the
    nLab and Wikipedia pages above).  Because [nat] addition is strictly
    associative/unital only up to propositional [=], several of those
    "on the nose" equations are nonetheless stated below in [eq_rect]
    transport form. *)

Section TermEq.

Context (S : Signature).

(** Strict tensor coherence requires equating terms whose types
    involve different parenthesisations of [+] on [nat].  Because
    [nat] addition is associative ONLY up to propositional [=]
    (not definitional), we cannot state e.g. an associator
    [T_assoc : Term S ((m+n)+p) (m+(n+p))] in [Term] alone.  The
    equational theory bridges these via the strict tensor axioms
    [TE_tens_assoc] / [TE_tens_id0_left] / [TE_tens_id0_right]; in
    practice they are used as rewrite rules to bring a term into a
    canonical right-associated form on its arities. *)

Inductive TermEq : forall {m n}, Term S m n -> Term S m n -> Prop :=

  (** Setoid laws. *)
  | TE_refl  : forall {m n} (t : Term S m n), TermEq t t     (* equivalence: reflexivity *)
  | TE_sym   : forall {m n} (s t : Term S m n),              (* equivalence: symmetry *)
               TermEq s t -> TermEq t s
  | TE_trans : forall {m n} (s t u : Term S m n),            (* equivalence: transitivity *)
               TermEq s t -> TermEq t u -> TermEq s u

  (** Congruence of sequential composition. *)
  | TE_comp_cong : forall {m n p}                            (* congruence of [T_comp] *)
                          (f f' : Term S n p) (g g' : Term S m n),
                   TermEq f f' -> TermEq g g' ->
                   TermEq (T_comp f g) (T_comp f' g')

  (** Congruence of parallel composition (tensor). *)
  | TE_tens_cong : forall {m1 n1 m2 n2}                      (* congruence of [T_tens] *)
                          (f f' : Term S m1 n1) (g g' : Term S m2 n2),
                   TermEq f f' -> TermEq g g' ->
                   TermEq (T_tens f g) (T_tens f' g')

  (** Category laws: id-left, id-right, associativity. *)
  | TE_id_left  : forall {m n} (f : Term S m n),             (* category: left identity *)
                  TermEq (T_comp (T_id n) f) f
  | TE_id_right : forall {m n} (f : Term S m n),             (* category: right identity *)
                  TermEq (T_comp f (T_id m)) f
  | TE_assoc    : forall {m n p q}                           (* category: associativity of [⊙] *)
                         (h : Term S p q) (g : Term S n p) (f : Term S m n),
                  TermEq (T_comp (T_comp h g) f)
                         (T_comp h (T_comp g f))

  (** Bifunctor laws: identity, sequential interchange.

      [TE_tens_id]: [id_m ⊕ id_n = id_(m+n)] — typing OK because [Term]
      is [nat]-indexed and addition is the tensor on arities. *)
  | TE_tens_id : forall (m n : nat),                         (* bifunctor: tensor preserves identity *)
                 TermEq (T_tens (T_id m) (T_id n)) (T_id (m + n))

  (** [TE_interchange]: (f₁ ⊕ g₁) ⊙ (f₂ ⊕ g₂) ≈ (f₁ ⊙ f₂) ⊕ (g₁ ⊙ g₂)
      — the parallel/sequential interchange law. *)
  | TE_interchange :                                         (* bifunctor: middle-four interchange *)
      forall {m1 n1 p1 m2 n2 p2}
             (f1 : Term S n1 p1) (g1 : Term S n2 p2)
             (f2 : Term S m1 n1) (g2 : Term S m2 n2),
        TermEq (T_comp (T_tens f1 g1) (T_tens f2 g2))
               (T_tens (T_comp f1 f2) (T_comp g1 g2))

  (** Braid involution: [σ_{m,n} ⊙ σ_{n,m} ≈ id_{m+n}].  Block-braiding
      twice returns to identity. *)
  | TE_braid_invol :                                         (* symmetry: involution σ⊙σ = id *)
      forall (m n : nat),
        TermEq (T_comp (T_braid n m) (T_braid m n)) (T_id (m + n))

  (** Braid naturality (top form):
        (g ⊕ f) ⊙ σ_{m1,m2} ≈ σ_{n1,n2} ⊙ (f ⊕ g)
      where f : m1 -> n1, g : m2 -> n2. *)
  | TE_braid_natural :                                       (* symmetry: braiding naturality *)
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
  | TE_tens_id0_left :                                       (* strict unit: left unitor λ = id *)
      forall {m n : nat} (f : Term S m n),
        TermEq (T_tens (T_id 0) f) f

  (** Strict-PROP unit on the right: dually, tensoring with [T_id 0]
      on the RIGHT is identity modulo [n + 0 = n].

      Stated in transport form via [eq_rect] over the
      arity-equations.  Concretely [T_tens f (T_id 0)] has type
      [Term S (m + 0) (n + 0)]; we transport it to [Term S m n] using
      [Nat.add_0_r] on both indices, and assert the result equals [f]. *)
  | TE_tens_id0_right :                                      (* strict unit: right unitor ρ = id *)
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
  | TE_tens_assoc :                                          (* strict associator α = id *)
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
      [hexagon_from] for non-trivial arities.

      ** Minimality note (nLab/Wikipedia, symmetric_monoidal_category)

      In a SYMMETRIC (as opposed to merely braided) monoidal category
      the two hexagons are NOT independent: given the symmetry equation
      [σ_{n,m} ⊙ σ_{m,n} ≈ id] ([TE_braid_invol]) together with braid
      naturality ([TE_braid_natural]), either hexagon implies the other.
      So exactly one of [TE_braid_hex_left] / [TE_braid_hex_right] is
      logically necessary; the other is a derivable theorem we keep as a
      primitive constructor for ergonomics (the [eq_rect] transport
      bookkeeping makes the formal derivation tedious).  As with the
      unit-braid constructors below, the redundancy is sound and cannot
      make [TermEq] inconsistent (every constructor is inhabited by the
      standard permutation model).  Deriving one as a [Lemma] after the
      inductive would change only the axiom budget, not any
      [TermEq]-judgement.  See review FLAG (needs-followup). *)

  | TE_braid_hex_left :                                       (* symmetry: hexagon (left argument) *)
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

  | TE_braid_hex_right :                                      (* symmetry: hexagon (right argument) *)
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
      definitional — [Nat.add] is left-strict only).

      ** Minimality note (Joyal–Street §2 Prop. 2.1; Mac Lane CWM VII §1)

      In the literature these unit-braid equations are NOT independent
      axioms — they are theorems of [hexagon + naturality + invol +
      triangle].  Sketch of the derivation in our setting (we omit the
      formal proof's eq_rect bookkeeping for brevity):

        1. Instantiate [TE_braid_hex_right] at [m := n], [n := 0],
           [p := 0]:
             σ_{n, 0+0} ≈ (id_0 ⊕ σ_{n,0}) ⊙ (σ_{n,0} ⊕ id_0).
        2. Collapse the [id_0 ⊕ _] and [_ ⊕ id_0] tensors via
           [TE_tens_id0_left] / [TE_tens_id0_right]:
             σ_{n, 0} ≈ σ_{n, 0} ⊙ σ_{n, 0}                   (idempotency)
        3. By [TE_braid_invol]: [σ_{0, n} ⊙ σ_{n, 0} ≈ id_{n+0} ≈ id_n].
           Compose both sides of (2) with [σ_{0, n}] on the left:
             σ_{0, n} ⊙ σ_{n, 0} ≈ σ_{0, n} ⊙ (σ_{n, 0} ⊙ σ_{n, 0}).
             id_n        ≈  σ_{0, n} ⊙ σ_{n, 0} ⊙ σ_{n, 0}      (assoc)
             id_n        ≈  id_n ⊙ σ_{n, 0}                     (involution)
             id_n        ≈  σ_{n, 0}                            (id-left)
        4. The dual [σ_{0, n} ≈ id_n] follows by applying [TE_braid_invol]
           once more to step (3)'s conclusion.

      We keep them as primitive constructors here for ergonomics: the
      formal derivation requires substantial [eq_rect] bookkeeping
      across hexagon-, strict-unit-, and involution-form transports
      (the unit-arity cases of those transports do not reduce
      definitionally in [Nat.add]), and the downstream [SymmetricMonoidal]
      instance on [FreeCat S] consumes the strict form directly.

      Adding sound redundant constructors is harmless (it cannot make
      [TermEq] inconsistent — every constructor remains inhabited by
      the standard permutation model).  A future refactor that
      derives these as [Lemma]s after the inductive declaration would
      not change any [TermEq]-judgements, only the axiom budget. *)

  | TE_braid_unit_left :                                      (* symmetry: unit braid σ_{0,n} = id (derivable) *)
      forall (n : nat),
        TermEq
          (* T_braid 0 n : Term S (0+n) (n+0) = Term S n (n+0).
             Cast the target n+0 → n. *)
          (eq_rect (n + 0) (fun t => Term S n t)
                   (T_braid 0 n)
                   n
                   (Nat.add_0_r n))
          (T_id n)

  | TE_braid_unit_right :                                     (* symmetry: unit braid σ_{n,0} = id (derivable) *)
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

(** ** Identity bookkeeping

    The strict monoidal functors built downstream on free and
    presented PROPs all have comparison maps that are identities or
    tensors of identities, so their coherence squares reduce to the
    same four identity-collapsing equations.  They are stated here
    once, over an arbitrary signature, and consumed by
    [Construction/PROP/Presentation.v] (at the signature of an [SMT])
    and [Construction/PROP/Tietze.v]. *)

(** An identity slides from one side of a morphism to the other. *)
Lemma tm_id_swap {S : Signature} {m n : nat} (t : Term S m n) :
  TermEq S (T_comp t (T_id m)) (T_comp (T_id n) t).
Proof.
  apply TE_trans with t.
  - apply TE_id_right.
  - apply TE_sym, TE_id_left.
Qed.

(** A composite of identities equals a tensor of identities. *)
Lemma tm_comp_id_tens {S : Signature} (m n : nat) :
  TermEq S (T_comp (T_id (m + n)) (T_id (m + n))) (T_tens (T_id m) (T_id n)).
Proof.
  apply TE_trans with (T_id (m + n)).
  - apply TE_id_left.
  - apply TE_sym, TE_tens_id.
Qed.

(** Collapsing an identity and a tensor of identities after [t]. *)
Lemma tm_collapse_r {S : Signature} {m n p : nat} (t : Term S (m + n) p) :
  TermEq S (T_comp (T_comp t (T_id (m + n))) (T_tens (T_id m) (T_id n))) t.
Proof.
  apply TE_trans with (T_comp t (T_tens (T_id m) (T_id n))).
  - apply TE_comp_cong.
    + apply TE_id_right.
    + apply TE_refl.
  - apply TE_trans with (T_comp t (T_id (m + n))).
    + apply TE_comp_cong.
      * apply TE_refl.
      * apply TE_tens_id.
    + apply TE_id_right.
Qed.

(** Collapsing an identity and a tensor of identities before [t]. *)
Lemma tm_collapse_l {S : Signature} {m n p : nat} (t : Term S p (m + n)) :
  TermEq S (T_comp (T_comp (T_id (m + n)) (T_tens (T_id m) (T_id n))) t) t.
Proof.
  apply TE_trans with (T_comp (T_tens (T_id m) (T_id n)) t).
  - apply TE_comp_cong.
    + apply TE_id_left.
    + apply TE_refl.
  - apply TE_trans with (T_comp (T_id (m + n)) t).
    + apply TE_comp_cong.
      * apply TE_tens_id.
      * apply TE_refl.
    + apply TE_id_left.
Qed.

(** ** Generic substitution

    [T_subst sub] replaces every generator leaf [T_gen s] by the term
    [sub _ _ s] and leaves the structural constructors untouched.  It
    is the common skeleton of the term homomorphisms defined
    downstream in [Construction/PROP/Tietze.v] — relabelling along a
    signature morphism ([T_map], whose generator action is [T_gen]
    after the morphism) and the definitional-extension retraction
    ([ext_retract], whose generator action substitutes the defining
    word) — so the nineteen-case preservation induction
    [T_subst_TermEq] below is proved ONCE and instantiated there. *)

Fixpoint T_subst {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {m n : nat} (t : Term S m n) : Term T m n :=
  match t in Term _ m' n' return Term T m' n' with
  | T_id k      => T_id k
  | T_braid a b => T_braid a b
  | T_comp g f  => T_comp (T_subst sub g) (T_subst sub f)
  | T_tens f g  => T_tens (T_subst sub f) (T_subst sub g)
  | T_gen s     => sub _ _ s
  end.

(** *** Transport seams

    The strict-PROP axioms of [TermEq] carry their arity mismatches as
    [eq_rect] transports; [T_subst] commutes with each transport shape
    by Leibniz equality (destruct the arity equation). *)

Lemma T_subst_eq_rect_cod {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a b b' : nat} (e : b = b') (t : Term S a b) :
  T_subst sub (eq_rect b (fun k : nat => Term S a k) t b' e)
  = eq_rect b (fun k : nat => Term T a k) (T_subst sub t) b' e.
Proof. destruct e; reflexivity. Qed.

Lemma T_subst_eq_rect_dom {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a a' b : nat} (e : a = a') (t : Term S a b) :
  T_subst sub (eq_rect a (fun k : nat => Term S k b) t a' e)
  = eq_rect a (fun k : nat => Term T k b) (T_subst sub t) a' e.
Proof. destruct e; reflexivity. Qed.

Lemma T_subst_eq_rect_r_dom {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {a a' b : nat} (e : a' = a) (t : Term S a b) :
  T_subst sub (eq_rect_r (fun k : nat => Term S k b) t e)
  = eq_rect_r (fun k : nat => Term T k b) (T_subst sub t) e.
Proof. destruct e; reflexivity. Qed.

(** *** Preservation of the free equations

    [T_subst sub] carries every free equation of [TermEq S] to the
    corresponding free equation of [TermEq T], for ANY generator
    action [sub].  The induction covers all nineteen constructors:
    the thirteen constructor-to-constructor cases reduce by
    computation, and the six transport-form cases first move
    [T_subst] across the [eq_rect] seams by the Leibniz bridges
    above, then close with the same primitive constructor. *)

Lemma T_subst_TermEq {S T : Signature}
  (sub : forall a b : nat, S a b -> Term T a b)
  {m n : nat} {s t : Term S m n} :
  TermEq S s t -> TermEq T (T_subst sub s) (T_subst sub t).
Proof.
  intros HT.
  induction HT.
  - (* TE_refl *)
    apply TE_refl.
  - (* TE_sym *)
    exact (TE_sym _ _ IHHT).
  - (* TE_trans *)
    exact (TE_trans _ _ _ IHHT1 IHHT2).
  - (* TE_comp_cong *)
    cbn [T_subst]; apply TE_comp_cong; assumption.
  - (* TE_tens_cong *)
    cbn [T_subst]; apply TE_tens_cong; assumption.
  - (* TE_id_left *)
    cbn [T_subst]; apply TE_id_left.
  - (* TE_id_right *)
    cbn [T_subst]; apply TE_id_right.
  - (* TE_assoc *)
    cbn [T_subst]; apply TE_assoc.
  - (* TE_tens_id *)
    cbn [T_subst]; apply TE_tens_id.
  - (* TE_interchange *)
    cbn [T_subst]; apply TE_interchange.
  - (* TE_braid_invol *)
    cbn [T_subst]; apply TE_braid_invol.
  - (* TE_braid_natural *)
    cbn [T_subst]; apply TE_braid_natural.
  - (* TE_tens_id0_left *)
    cbn [T_subst]; apply TE_tens_id0_left.
  - (* TE_tens_id0_right *)
    rewrite T_subst_eq_rect_cod, T_subst_eq_rect_r_dom.
    cbn [T_subst]; apply TE_tens_id0_right.
  - (* TE_tens_assoc *)
    rewrite T_subst_eq_rect_cod, T_subst_eq_rect_r_dom.
    cbn [T_subst]; apply TE_tens_assoc.
  - (* TE_braid_hex_left *)
    cbn [T_subst].
    rewrite T_subst_eq_rect_cod, !T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_hex_left.
  - (* TE_braid_hex_right *)
    cbn [T_subst].
    rewrite T_subst_eq_rect_cod, !T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_hex_right.
  - (* TE_braid_unit_left *)
    rewrite T_subst_eq_rect_cod.
    cbn [T_subst]; apply TE_braid_unit_left.
  - (* TE_braid_unit_right *)
    rewrite T_subst_eq_rect_dom.
    cbn [T_subst]; apply TE_braid_unit_right.
Qed.
