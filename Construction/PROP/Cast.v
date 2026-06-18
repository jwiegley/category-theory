Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.

From Coq Require Import Arith.
From Coq Require Import PeanoNat.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Transport infrastructure for the FreePROP construction

    The FreePROP needs to talk about morphisms between objects whose
    arity-naturals are PROPOSITIONALLY but not DEFINITIONALLY equal —
    e.g. [x + 0] and [x], or [(x + y) + z] and [x + (y + z)].
    [Nat.add] is left-strict but not right-strict in Coq, so these
    arity equations do not reduce definitionally and must be
    transported across.

    [T_cast e] is the identity term, transported across a nat
    equality.  Together with the associated rewrite lemmas it lets
    the Monoidal instance for FreeCat package up structural
    isomorphisms (unitors, associator) for the cases where the arity
    equality is not [eq_refl]. *)

(** The cast term: identity, transported across [e : m = n]. *)
Definition T_cast {S : Signature} {m n : nat} (e : m = n) : Term S m n :=
  match e in _ = k return Term S m k with
  | eq_refl => T_id m
  end.

(** Cast at [eq_refl] is the literal identity. *)
Lemma T_cast_refl {S : Signature} (m : nat) :
  @T_cast S m m eq_refl = T_id m.
Proof. reflexivity. Qed.

(** Composing two casts gives a cast along the transitive equation. *)
Lemma T_cast_compose
  {S : Signature} {m n p : nat} (e1 : m = n) (e2 : n = p) :
  TermEq S (T_comp (T_cast e2) (T_cast e1)) (T_cast (eq_trans e1 e2)).
Proof.
  destruct e1, e2.
  cbn.
  apply TE_id_left.
Qed.

(** Casting along [e] then along [eq_sym e] is the identity. *)
Lemma T_cast_inv
  {S : Signature} {m n : nat} (e : m = n) :
  TermEq S (T_comp (T_cast (eq_sym e)) (T_cast e)) (T_id m).
Proof.
  destruct e.
  cbn.
  apply TE_id_left.
Qed.

(** Casting along [eq_sym e] then along [e] is the identity. *)
Lemma T_cast_inv_sym
  {S : Signature} {m n : nat} (e : m = n) :
  TermEq S (T_comp (T_cast e) (T_cast (eq_sym e))) (T_id n).
Proof.
  destruct e.
  cbn.
  apply TE_id_left.
Qed.

(** Naturality of [T_cast]: a cast can be moved past any morphism
    along the same arity equation.  This is the key lemma used to
    discharge the naturality obligations of the unitors and the
    associator in the Monoidal instance on [FreeCat S]. *)
Lemma T_cast_natural
  {S : Signature} {m n : nat} (e : m = n) (f : Term S m m) (g : Term S n n)
  (Hfg : forall (q : m = n),
           TermEq S (T_comp (T_cast q) f)
                    (T_comp g (T_cast q))) :
  TermEq S (T_comp (T_cast e) f) (T_comp g (T_cast e)).
Proof. apply Hfg. Qed.

(** Degenerate naturality at [eq_refl]: a [T_cast eq_refl] is [T_id],
    so it commutes with any morphism trivially. *)
Lemma T_cast_natural_refl
  {S : Signature} {n : nat} (f : Term S n n) :
  TermEq S (T_comp (T_cast eq_refl) f) (T_comp f (T_cast eq_refl)).
Proof.
  cbn.
  apply TE_trans with f.
  - apply TE_id_left.
  - apply TE_sym, TE_id_right.
Qed.

(** Proof-irrelevance for nat-equation casts: any two proofs [e1 e2]
    of [m = n] give equal cast terms.

    [nat] has decidable equality, hence Uniqueness of Identity Proofs
    (UIP) holds for it without any axioms — proved by
    [Eqdep_dec.UIP_dec Nat.eq_dec].  This lets us replace one proof
    of a [nat] equation by another inside [T_cast]. *)
Lemma T_cast_irrelevant
  {S : Signature} {m n : nat} (e1 e2 : m = n) :
  T_cast (S := S) e1 = T_cast (S := S) e2.
Proof.
  rewrite (UIP_dec Nat.eq_dec e1 e2).
  reflexivity.
Qed.

(** Special case: any cast along an equation of [m = m] is the
    identity, because [eq_refl m] is the canonical proof of [m = m]
    and [T_cast eq_refl = T_id m] reduces definitionally. *)
Lemma T_cast_id
  {S : Signature} {m : nat} (e : m = m) :
  T_cast (S := S) e = T_id m.
Proof.
  rewrite (T_cast_irrelevant e eq_refl).
  reflexivity.
Qed.

(** ** Transport bridges for strict-PROP equations

    The strict-PROP right-unit and associativity axioms in [TermEq]
    are stated in [eq_rect] transport form (over [Nat.add_0_r] and
    [Nat.add_assoc] respectively).  Below we expose a small helper
    for use when downstream proofs need to work with both ends of
    the transport. *)

(** Transport-spelling bridge: the [eq_rect] transport of a term
    along [e : m = n] over the codomain index equals the [match]
    (dependent pattern-match) spelling of the same transport.  Both
    sides are [T_cast e] applied to [t]; this lemma just lets a proof
    switch between the [eq_rect] form used in [TermEq]'s strict-PROP
    axioms and the [match] form used by [T_cast].

    This is the standard "destruct the eq_rect" pattern, but bundled
    as a helper so the [T_cast]-level naturality proofs don't have
    to repeat it. *)
Lemma T_term_eq_rect_destruct
  {S : Signature} {m n : nat} (e : m = n) (t : Term S m m) :
  eq_rect m (fun k => Term S m k) t n e
  = match e in _ = k return Term S m k with
    | eq_refl => t
    end.
Proof. destruct e; reflexivity. Qed.

(** Dual: an [eq_rect_r] transport on the domain index reduces at
    [eq_refl] to the term itself.  More general transport shapes
    require a [destruct e] in context. *)
Lemma T_term_eq_rect_r_refl
  {S : Signature} {m : nat} (t : Term S m m) :
  eq_rect_r (fun k => Term S k m) t (eq_refl m) = t.
Proof. reflexivity. Qed.
