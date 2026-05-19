Require Import Category.Lib.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Cast.

From Coq Require Import Arith.

Generalizable All Variables.

(** * [T_cast] interaction with [T_tens]

    Bridge lemmas that the upcoming Monoidal instance on [FreeCat S]
    will need to discharge naturality of the structural isomorphisms.
    [T_tens] mixes two arities additively; [T_cast] rewrites a single
    arity along a propositional equation; the two interact via the
    [TE_tens_id] / [TE_interchange] constructors of [TermEq]. *)

Section CastTensor.

Context (S : Signature).

Open Scope nat_scope.

(** Tensoring identity casts on the left: a cast on the right factor
    can be pushed past an identity on the left factor.

    [(id_m ⊕ T_cast e) ≈ T_cast (cast (m + e))]   (informally)

    This lemma states the special case where both sides are pure
    identity-times-cast, with no other morphism between. *)
Lemma T_tens_id_cast_left {m a b : nat} (e : a = b) :
  TermEq S (T_tens (T_id m) (T_cast e))
           (T_cast (f_equal (fun k => m + k) e)).
Proof.
  destruct e.
  cbn.
  apply TE_tens_id.
Qed.

(** Symmetric variant: cast on the LEFT, identity on the RIGHT. *)
Lemma T_tens_cast_id_right {a b n : nat} (e : a = b) :
  TermEq S (T_tens (T_cast e) (T_id n))
           (T_cast (f_equal (fun k => k + n) e)).
Proof.
  destruct e.
  cbn.
  apply TE_tens_id.
Qed.

(** Both factors are identities — collapse to a single [T_cast eq_refl]
    via [TE_tens_id]. *)
Lemma T_tens_id_id (m n : nat) :
  TermEq S (T_tens (T_id m) (T_id n)) (T_id (m + n)).
Proof. apply TE_tens_id. Qed.

(** Pushing a cast past a tensor on one factor: equivalent to applying
    the same cast to that factor and identity-tensoring the other. *)
Lemma T_comp_cast_tens_left {m1 n1 m2 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_cast eq_refl) (T_tens f g))
           (T_tens f g).
Proof. cbn. apply TE_id_left. Qed.

Lemma T_comp_tens_cast_right {m1 n1 m2 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  TermEq S (T_comp (T_tens f g) (T_cast eq_refl))
           (T_tens f g).
Proof. cbn. apply TE_id_right. Qed.

End CastTensor.
