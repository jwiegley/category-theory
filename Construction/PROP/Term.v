Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.

From Stdlib Require Import Arith.

Generalizable All Variables.

(** * Raw terms over a PROP signature

    The syntactic representation of morphisms in the free PROP on a
    signature [S].  A term of type [Term S m n] is a string-diagram
    expression with [m] input wires and [n] output wires, built up from:

      - identity wires [T_id n]
      - braids [T_braid m n] (the canonical "block braiding" that
        crosses an [m]-wide bundle past an [n]-wide bundle)
      - sequential composition [T_comp]
      - parallel composition (tensor) [T_tens]
      - signature-supplied generators [T_gen]

    This file defines just the SYNTAX — no equational theory.  The
    equational theory (associativity / unit / braid coherence /
    interchange) lives in a successor file [Construction/PROP/TermEq.v]
    and the full [FreePROP] category in [Construction/PROP/Free.v].

    The arity-indexing means [Term S] is naturally a "many-sorted on
    naturals" data structure: arities propagate up through sequential
    and parallel composition by the corresponding [Nat] operation. *)

Section Term.

Context (S : Signature).

Inductive Term : nat -> nat -> Type :=
  | T_id    : forall n, Term n n
  | T_braid : forall m n, Term (m + n) (n + m)
  | T_comp  : forall {m n p}, Term n p -> Term m n -> Term m p
  | T_tens  : forall {m1 n1 m2 n2},
              Term m1 n1 -> Term m2 n2 -> Term (m1 + m2) (n1 + n2)
  | T_gen   : forall {m n}, S m n -> Term m n.

End Term.

Arguments T_id    {S} n.
Arguments T_braid {S} m n.
Arguments T_comp  {S m n p} _ _.
Arguments T_tens  {S m1 n1 m2 n2} _ _.
Arguments T_gen   {S m n} _.

Declare Scope term_scope.
Delimit Scope term_scope with term.

Notation "f ⊙t g" := (T_comp f g) (at level 40, left associativity) : term_scope.
Notation "f ⊕t g" := (T_tens f g) (at level 30, right associativity) : term_scope.

(** ** Smart constructors *)

(** The "swap" braid on two single wires. *)
Definition T_swap {S : Signature} : Term S 2 2 :=
  T_braid 1 1.

(** Lift a generator under a signature embedding. *)
Definition T_inj {S T : Signature} (inc : SubSig S T)
                 {m n : nat} (t : Term S m n) : Term T m n.
Proof.
  induction t.
  - exact (T_id _).
  - exact (T_braid _ _).
  - exact (T_comp IHt1 IHt2).
  - exact (T_tens IHt1 IHt2).
  - exact (T_gen (inc _ _ s)).
Defined.

(** ** Examples *)

(** Identity on a single wire. *)
Definition wire {S : Signature} : Term S 1 1 := T_id 1.

(** Identity on two wires in parallel. *)
Definition wire2 {S : Signature} : Term S 2 2 := T_id 2.

(** The empty term: 0-input, 0-output. *)
Definition T_nothing {S : Signature} : Term S 0 0 := T_id 0.
