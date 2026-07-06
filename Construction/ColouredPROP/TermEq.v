Require Import Category.Lib.
Require Import Category.Construction.ColouredPROP.Signature.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Equational theory of free coloured-PROP terms *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   The equivalence relation [CTermEq] on [CTerm S cs ds] quotients the
   raw syntax of [Construction/ColouredPROP/Signature.v] by the strict
   symmetric monoidal category axioms.  The quotient
   [CTerm S / CTermEq S] is the free COLOURED PROP (= free strict
   symmetric monoidal category whose objects are the finite words over
   [Colour] under concatenation) on the signature [S].

   In library notation, with [⊙c = CT_comp], [⊕c = CT_tens],
   [id = CT_id], [σ = CT_braid], the constructors below assert:

      - reflexivity, symmetry, transitivity (the setoid laws)
      - congruences for [CT_comp] and [CT_tens]
      - category laws: identity-left, identity-right, associativity
      - bifunctor (tensor) laws: identity, sequential interchange,
        functoriality
      - symmetric-monoidal coherence: braid naturality, braid
        involution, hexagon

    The strict-PROP axioms on colour words — [CT_id cs ⊕c CT_id ds ≈
    CT_id (cs ++ ds)], the concatenation-as-tensor strict laws — are
    present as primitive constructors of [CTermEq] because the [CTerm]
    type is indexed by [list Colour] and [CT_id cs ⊕c CT_id ds] has
    type [CTerm S (cs ++ ds) (cs ++ ds)] while [CT_id (cs ++ ds)] has
    the same type by definition; the equation is well-typed without
    any [eq_rect] casts.

    This file defines just the equivalence relation.  The [Setoid]
    instance and the [Category] / coloured-PROP structure on the
    quotient live in successor files ([Construction/ColouredPROP/
    Free.v] onward).

    In a STRICT symmetric monoidal category the associator and unitors
    are identities, so the pentagon and triangle coherences hold on the
    nose and the only substantive coherences left are the hexagon and
    the symmetry/involution equation [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id] (cf.
    the nLab and Wikipedia pages above).  Because list concatenation is
    strictly associative/right-unital only up to propositional [=]
    (exactly the asymmetry of [Nat.add] in the one-sorted donor:
    [[] ++ l] is definitional but [l ++ []] and re-association are
    not), several of those "on the nose" equations are nonetheless
    stated below in [eq_rect] transport form. *)

Section CTermEq.

Context {Colour : Type}.
Context (S : CSignature Colour).

(** Strict tensor coherence requires equating terms whose types
    involve different parenthesisations of [++] on [list Colour].
    Because concatenation is associative ONLY up to propositional [=]
    (not definitional), we cannot state e.g. an associator
    [CT_assoc : CTerm S ((cs ++ ds) ++ es) (cs ++ (ds ++ es))] in
    [CTerm] alone.  The equational theory bridges these via the strict
    tensor axioms [CTE_tens_assoc] / [CTE_tens_id0_left] /
    [CTE_tens_id0_right]; in practice they are used as rewrite rules to
    bring a term into a canonical right-associated form on its
    boundaries. *)

Inductive CTermEq : forall {cs ds}, CTerm S cs ds -> CTerm S cs ds -> Prop :=

  (** Setoid laws. *)
  | CTE_refl {cs ds} (f : CTerm S cs ds) :                   (* equivalence: reflexivity *)
      CTermEq f f
  | CTE_sym {cs ds} (f g : CTerm S cs ds) :                  (* equivalence: symmetry *)
      CTermEq f g -> CTermEq g f
  | CTE_trans {cs ds} (f g h : CTerm S cs ds) :              (* equivalence: transitivity *)
      CTermEq f g -> CTermEq g h -> CTermEq f h

  (** Congruence of sequential composition. *)
  | CTE_comp_cong {cs ds es}                                 (* congruence of [CT_comp] *)
      (f f' : CTerm S ds es) (g g' : CTerm S cs ds) :
      CTermEq f f' -> CTermEq g g' ->
      CTermEq (CT_comp f g) (CT_comp f' g')

  (** Congruence of parallel composition (tensor). *)
  | CTE_tens_cong {cs1 ds1 cs2 ds2}                          (* congruence of [CT_tens] *)
      (f f' : CTerm S cs1 ds1) (g g' : CTerm S cs2 ds2) :
      CTermEq f f' -> CTermEq g g' ->
      CTermEq (CT_tens f g) (CT_tens f' g')

  (** Category laws: id-left, id-right, associativity. *)
  | CTE_id_left {cs ds} (f : CTerm S cs ds) :                (* category: left identity *)
      CTermEq (CT_comp (CT_id ds) f) f
  | CTE_id_right {cs ds} (f : CTerm S cs ds) :               (* category: right identity *)
      CTermEq (CT_comp f (CT_id cs)) f
  | CTE_assoc {cs ds es fs}                                  (* category: associativity of [⊙c] *)
      (h : CTerm S es fs) (g : CTerm S ds es) (f : CTerm S cs ds) :
      CTermEq (CT_comp (CT_comp h g) f)
              (CT_comp h (CT_comp g f))

  (** Bifunctor laws: identity, sequential interchange.

      [CTE_tens_id]: [id_cs ⊕c id_ds = id_(cs ++ ds)] — typing OK
      because [CTerm] is [list Colour]-indexed and concatenation is
      the tensor on boundaries. *)
  | CTE_tens_id (cs ds : list Colour) :                      (* bifunctor: tensor preserves identity *)
      CTermEq (CT_tens (CT_id cs) (CT_id ds)) (CT_id (cs ++ ds))

  (** [CTE_interchange]: (f₁ ⊕c g₁) ⊙c (f₂ ⊕c g₂) ≈ (f₁ ⊙c f₂) ⊕c (g₁ ⊙c g₂)
      — the parallel/sequential interchange law. *)
  | CTE_interchange {cs ds es cs' ds' es'}                   (* bifunctor: middle-four interchange *)
      (f1 : CTerm S ds es) (f2 : CTerm S cs ds)
      (g1 : CTerm S ds' es') (g2 : CTerm S cs' ds') :
      CTermEq (CT_comp (CT_tens f1 g1) (CT_tens f2 g2))
              (CT_tens (CT_comp f1 f2) (CT_comp g1 g2))

  (** Braid involution: [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id_{cs ++ ds}].
      Block-braiding twice returns to identity. *)
  | CTE_braid_invol (cs ds : list Colour) :                  (* symmetry: involution σ⊙σ = id *)
      CTermEq (CT_comp (CT_braid ds cs) (CT_braid cs ds)) (CT_id (cs ++ ds))

  (** Braid naturality (top form):
        (g ⊕c f) ⊙c σ_{cs1,cs2} ≈ σ_{ds1,ds2} ⊙c (f ⊕c g)
      where f : cs1 -> ds1, g : cs2 -> ds2. *)
  | CTE_braid_natural {cs1 ds1 cs2 ds2}                      (* symmetry: braiding naturality *)
      (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
      CTermEq (CT_comp (CT_tens g f) (CT_braid cs1 cs2))
              (CT_comp (CT_braid ds1 ds2) (CT_tens f g))

  (** Strict-PROP unit on tensor: tensoring with the empty term
      [CT_id []] on the LEFT is an identity operation modulo the
      definitional equation [[] ++ cs = cs].

      This axiom is the analogue of the strict-unit law in a
      [StrictMonoidal] category.  In a generic [Monoidal] category
      it would be a natural ISOMORPHISM (the left unitor), not an
      equation; coloured PROPs are strict on the nose, so we assert
      it as an equation in [CTermEq].

      Both sides have type [CTerm S ([] ++ cs) ds] = [CTerm S cs ds]
      on the nose, so no transport is needed — [[] ++ l] reduces
      definitionally, just as [0 + n] does on [nat]. *)
  | CTE_tens_id0_left {cs ds} (f : CTerm S cs ds) :          (* strict unit: left unitor λ = id *)
      CTermEq (CT_tens (CT_id []) f) f

  (** Strict-PROP unit on the right: dually, tensoring with [CT_id []]
      on the RIGHT is identity modulo [cs ++ [] = cs].

      Stated in transport form via [eq_rect] over the boundary
      equations.  Concretely [CT_tens f (CT_id [])] has type
      [CTerm S (cs ++ []) (ds ++ [])]; we transport it to
      [CTerm S cs ds] using [app_nil_r] on both indices, and assert
      the result equals [f]. *)
  | CTE_tens_id0_right {cs ds} (f : CTerm S cs ds) :         (* strict unit: right unitor ρ = id *)
      CTermEq (eq_rect (ds ++ [])
                       (fun k => CTerm S (cs ++ []) k)
                       (CT_tens f (CT_id []))
                       ds
                       (app_nil_r ds))
              (eq_rect_r (fun k => CTerm S k ds)
                         f
                         (app_nil_r cs))

  (** Strict-PROP associativity of tensor.  Transport form. *)
  | CTE_tens_assoc {cs1 ds1 cs2 ds2 cs3 ds3}                 (* strict associator α = id *)
      (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) (h : CTerm S cs3 ds3) :
      CTermEq (eq_rect ((ds1 ++ ds2) ++ ds3)
                       (fun k => CTerm S ((cs1 ++ cs2) ++ cs3) k)
                       (CT_tens (CT_tens f g) h)
                       (ds1 ++ (ds2 ++ ds3))
                       (eq_sym (app_assoc ds1 ds2 ds3)))
              (eq_rect_r (fun k => CTerm S k (ds1 ++ (ds2 ++ ds3)))
                         (CT_tens f (CT_tens g h))
                         (eq_sym (app_assoc cs1 cs2 cs3)))

  (** ** Hexagon axioms for block braids

      In a strict symmetric monoidal category the braid decomposes
      additively in either argument (Mac Lane CWM Ch.VII §7;
      Joyal–Street §2; Selinger §3.2):

        σ_{m++n,p} ≈ (σ_{m,p} ⊕c id_n) ⊙c (id_m ⊕c σ_{n,p})     (hex-left)
        σ_{m,n++p} ≈ (id_n ⊕c σ_{m,p}) ⊙c (σ_{m,n} ⊕c id_p)     (hex-right)

      The LHS and RHS do not have matching types on the nose because
      concatenation on [list Colour] is associative only up to
      propositional [=], so both equations are stated in transport
      form via [eq_rect] against [app_assoc], analogous to
      [CTE_tens_assoc].

      Without these, e.g. [CT_braid [c1; c2; c3] [d1; d2]] is not
      provably equal to the layered composite of single-wire swaps,
      and the [BraidedMonoidal] layer beneath the [SymmetricMonoidal]
      instance on [CFreeCat S] cannot discharge [hexagon_identity] /
      [hexagon_identity_sym] for non-trivial colour words.

      ** Minimality note (nLab/Wikipedia, symmetric_monoidal_category)

      In a SYMMETRIC (as opposed to merely braided) monoidal category
      the two hexagons are NOT independent: given the symmetry equation
      [σ_{ds,cs} ⊙c σ_{cs,ds} ≈ id] ([CTE_braid_invol]) together with
      braid naturality ([CTE_braid_natural]), either hexagon implies
      the other.  So exactly one of [CTE_braid_hex_left] /
      [CTE_braid_hex_right] is logically necessary; the other is a
      derivable theorem we keep as a primitive constructor for
      ergonomics (the [eq_rect] transport bookkeeping makes the formal
      derivation tedious).  As with the unit-braid constructors below,
      the redundancy is sound and cannot make [CTermEq] inconsistent
      (every constructor is inhabited by the standard model in which a
      term denotes the colour-preserving permutation of its wires).
      Deriving one as a [Lemma] after the inductive would change only
      the axiom budget, not any [CTermEq]-judgement. *)

  | CTE_braid_hex_left (m n p : list Colour) :               (* symmetry: hexagon (left argument) *)
      CTermEq
        (* LHS: σ_{m++n,p} with source cast (m++n)++p → m++(n++p). *)
        (eq_rect ((m ++ n) ++ p)
                 (fun s => CTerm S s (p ++ (m ++ n)))
                 (CT_braid (m ++ n) p)
                 (m ++ (n ++ p))
                 (eq_sym (app_assoc m n p)))
        (* RHS: (σ_{m,p} ⊕c id_n) ⊙c (id_m ⊕c σ_{n,p})
           — the outer term needs both source and target casts to
           reach type CTerm S (m++(p++n)) (p++(m++n)); the inner term
           already has type CTerm S (m++(n++p)) (m++(p++n)). *)
        (CT_comp
           (eq_rect ((p ++ m) ++ n)
                    (fun t => CTerm S (m ++ (p ++ n)) t)
                    (eq_rect ((m ++ p) ++ n)
                             (fun s => CTerm S s ((p ++ m) ++ n))
                             (CT_tens (CT_braid m p) (CT_id n))
                             (m ++ (p ++ n))
                             (eq_sym (app_assoc m p n)))
                    (p ++ (m ++ n))
                    (eq_sym (app_assoc p m n)))
           (CT_tens (CT_id m) (CT_braid n p)))

  | CTE_braid_hex_right (m n p : list Colour) :              (* symmetry: hexagon (right argument) *)
      CTermEq
        (* LHS: σ_{m,n++p} with target cast (n++p)++m → n++(p++m). *)
        (eq_rect ((n ++ p) ++ m)
                 (fun t => CTerm S (m ++ (n ++ p)) t)
                 (CT_braid m (n ++ p))
                 (n ++ (p ++ m))
                 (eq_sym (app_assoc n p m)))
        (* RHS: (id_n ⊕c σ_{m,p}) ⊙c (σ_{m,n} ⊕c id_p)
           — outer source: n++(m++p) → (n++m)++p (app_assoc forward);
             inner source: (m++n)++p → m++(n++p) (eq_sym). *)
        (CT_comp
           (eq_rect (n ++ (m ++ p))
                    (fun s => CTerm S s (n ++ (p ++ m)))
                    (CT_tens (CT_id n) (CT_braid m p))
                    ((n ++ m) ++ p)
                    (app_assoc n m p))
           (eq_rect ((m ++ n) ++ p)
                    (fun s => CTerm S s ((n ++ m) ++ p))
                    (CT_tens (CT_braid m n) (CT_id p))
                    (m ++ (n ++ p))
                    (eq_sym (app_assoc m n p))))

  (** ** Unit-braid coherence

      In any symmetric monoidal category the braid involving the unit
      object collapses to the unitor: [σ_{I,X} = ρ_X^{-1} ∘ λ_X].  In
      the strict coloured-PROP setting on colour words, this becomes
      [CT_braid [] n ≈ CT_id n] and [CT_braid n [] ≈ CT_id n] modulo
      the boundary equation [n ++ [] = n] (which is propositional, not
      definitional — [app] is left-strict only, exactly like
      [Nat.add]).

      ** Minimality note (Joyal–Street §2 Prop. 2.1; Mac Lane CWM VII §1)

      In the literature these unit-braid equations are NOT independent
      axioms — they are theorems of [hexagon + naturality + invol +
      triangle].  Sketch of the derivation in our setting (we omit the
      formal proof's eq_rect bookkeeping for brevity):

        1. Instantiate [CTE_braid_hex_right] at [m := n], [n := []],
           [p := []]:
             σ_{n, [] ++ []} ≈ (id_[] ⊕c σ_{n,[]}) ⊙c (σ_{n,[]} ⊕c id_[]).
        2. Collapse the [id_[] ⊕c _] and [_ ⊕c id_[]] tensors via
           [CTE_tens_id0_left] / [CTE_tens_id0_right]:
             σ_{n, []} ≈ σ_{n, []} ⊙c σ_{n, []}                  (idempotency)
        3. By [CTE_braid_invol]: [σ_{[], n} ⊙c σ_{n, []} ≈ id_{n ++ []}
           ≈ id_n].  Compose both sides of (2) with [σ_{[], n}] on the
           left:
             σ_{[], n} ⊙c σ_{n, []} ≈ σ_{[], n} ⊙c (σ_{n, []} ⊙c σ_{n, []}).
             id_n        ≈  σ_{[], n} ⊙c σ_{n, []} ⊙c σ_{n, []}    (assoc)
             id_n        ≈  id_n ⊙c σ_{n, []}                      (involution)
             id_n        ≈  σ_{n, []}                              (id-left)
        4. The dual [σ_{[], n} ≈ id_n] follows by applying
           [CTE_braid_invol] once more to step (3)'s conclusion.

      We keep them as primitive constructors here for ergonomics: the
      formal derivation requires substantial [eq_rect] bookkeeping
      across hexagon-, strict-unit-, and involution-form transports
      (the unit-boundary cases of those transports do not reduce
      definitionally in [app]), and the downstream [SymmetricMonoidal]
      instance on [CFreeCat S] consumes the strict form directly.

      Adding sound redundant constructors is harmless (it cannot make
      [CTermEq] inconsistent — every constructor remains inhabited by
      the standard colour-preserving-permutation model).  A future
      refactor that derives these as [Lemma]s after the inductive
      declaration would not change any [CTermEq]-judgements, only the
      axiom budget. *)

  | CTE_braid_unit_left (n : list Colour) :                  (* symmetry: unit braid σ_{[],n} = id (derivable) *)
      CTermEq
        (* CT_braid [] n : CTerm S ([] ++ n) (n ++ []) = CTerm S n (n ++ []).
           Cast the target n ++ [] → n. *)
        (eq_rect (n ++ []) (fun t => CTerm S n t)
                 (CT_braid [] n)
                 n
                 (app_nil_r n))
        (CT_id n)

  | CTE_braid_unit_right (n : list Colour) :                 (* symmetry: unit braid σ_{n,[]} = id (derivable) *)
      CTermEq
        (* CT_braid n [] : CTerm S (n ++ []) ([] ++ n) = CTerm S (n ++ []) n.
           Cast the source n ++ [] → n. *)
        (eq_rect (n ++ []) (fun s => CTerm S s n)
                 (CT_braid n [])
                 n
                 (app_nil_r n))
        (CT_id n).

End CTermEq.

Arguments CTE_refl  {Colour S cs ds}.
Arguments CTE_sym   {Colour S cs ds}.
Arguments CTE_trans {Colour S cs ds}.
Arguments CTE_comp_cong {Colour S cs ds es}.
Arguments CTE_tens_cong {Colour S cs1 ds1 cs2 ds2}.
Arguments CTE_id_left  {Colour S cs ds}.
Arguments CTE_id_right {Colour S cs ds}.
Arguments CTE_assoc {Colour S cs ds es fs}.
Arguments CTE_tens_id {Colour S}.
Arguments CTE_interchange {Colour S cs ds es cs' ds' es'}.
Arguments CTE_braid_invol {Colour S}.
Arguments CTE_braid_natural {Colour S cs1 ds1 cs2 ds2}.
Arguments CTE_tens_id0_left {Colour S cs ds}.
Arguments CTE_tens_id0_right {Colour S cs ds}.
Arguments CTE_tens_assoc {Colour S cs1 ds1 cs2 ds2 cs3 ds3}.
Arguments CTE_braid_hex_left {Colour S}.
Arguments CTE_braid_hex_right {Colour S}.
Arguments CTE_braid_unit_left {Colour S}.
Arguments CTE_braid_unit_right {Colour S}.
