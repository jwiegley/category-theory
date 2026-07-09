Require Import Category.Lib.

From Coq Require Import Arith.

Generalizable All Variables.

(** * Signatures over PROPs

    A SIGNATURE is the data of a (one-sorted) symmetric monoidal
    theory: a family of typed generators indexed by their input/output
    arity.  Unlike an ordinary algebraic (Lawvere) theory, whose
    operations have a single output, a generator here may have any
    output coarity, so a signature is just the underlying object of
    the free-PROP adjunction, an element of [Set^(nat x nat)] (here in
    [Type]).  This is the standard "many-sorted signature in the
    arities-are-naturals setting" that PROPs are designed to capture
    syntactically.

    Concretely [Sig m n] is the [Type] of generator names that have
    [m] input wires (the domain/arity) and [n] output wires (the
    codomain/coarity).  In examples:

      - The empty signature [Empty_Sig m n := Empty_set] presents a
        PROP with NO non-structural generators (just identity,
        composition, tensor, braid).  Its free PROP on no generators
        is the permutation category: morphisms [m ~> n] are empty
        unless [m = n], in which case they are the braidings of [m]
        wires.  (NB: the free *hypergraph* PROP on no generators, which
        additionally quotients by the special-commutative-Frobenius
        axioms, is the PROP of cospans of finite sets; that extra
        structure is NOT imposed by the [FreePROP] of this development,
        which quotients only by the strict-SMC axioms.)
      - The commutative-monoid signature has one [Sig 2 1] (mul) and
        one [Sig 0 1] (unit).  Its free PROP-on-signature with the
        commutative-monoid equational theory is the PROP of finite
        sets and functions (i.e. FinSet, the prop for commutative
        monoids; multivalued/span semantics would instead require the
        comonoid generators of a bicommutative bimonoid).
      - For an electrical-circuit signature one might have [Sig 0 1]
        for a battery, [Sig 1 1] for a resistor, [Sig 2 1] for a
        Y-junction, etc.

    The signature is the INPUT to free-PROP constructions: given [S],
    [FreePROP S] is the strict symmetric monoidal category whose
    morphisms are [S]-labelled string diagrams modulo the
    strict-SMC axioms.  This file defines just [Signature]; the
    [Term] inductive and the [FreePROP] construction live in
    [Construction/PROP/Free.v] and successor files. *)

Definition Signature : Type := nat -> nat -> Type.

(** ** Examples *)

(** The empty signature.  Useful as a base case: [FreePROP Empty_Sig]
    is the PROP whose morphisms are exactly the strict-SMC syntactic
    rearrangements (identity, composition, tensor, braid) — the free
    PROP on no generators. *)
Definition Empty_Sig : Signature :=
  fun (_ _ : nat) => Empty_set.

(** The signature of a single generator [g : m -> n] (with [m] inputs
    and [n] outputs), with no other generators.  The generator's arity
    [(m, n)] is arbitrary, not fixed to a binary operation: [Sig a b]
    is [unit] exactly when [(a, b) = (m, n)] and [Empty_set] otherwise.
    Parameterised over the input and output arities
    so the same skeleton can present a Y-junction (2, 1), a fork (1, 2),
    a unit (0, 1), and so on. *)
Definition Single_Sig (m n : nat) : Signature :=
  fun a b => if Nat.eqb a m
             then if Nat.eqb b n then unit else Empty_set
             else Empty_set.

(** ** Operations on signatures

    Sum (disjoint union) of two signatures: a generator is a generator
    of one or the other.  This lets you build complex signatures from
    smaller ones — e.g. the commutative-monoid signature is the sum of
    [Single_Sig 2 1] (multiplication) and [Single_Sig 0 1] (unit). *)
Definition Sum_Sig (S T : Signature) : Signature :=
  fun m n => sum (S m n) (T m n).

(** Sub-signature: an arity-preserving family of generator
    relabellings into another signature — despite the name, no
    injectivity is required (generator collapses are allowed).
    Inhabited by [inl] / [inr] / nested projection chains. *)
Definition SubSig (Sub Sup : Signature) : Type :=
  forall m n, Sub m n -> Sup m n.

(** The identity sub-signature. *)
Definition SubSig_id (S : Signature) : SubSig S S :=
  fun _ _ s => s.

(** Sub-signature composition. *)
Definition SubSig_compose {S T U : Signature}
  (f : SubSig T U) (g : SubSig S T) : SubSig S U :=
  fun m n s => f m n (g m n s).
