Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.

From Stdlib Require Import Arith.

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
