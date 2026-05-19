Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Cast.

From Coq Require Import Arith.

Generalizable All Variables.

(** * Structural isomorphisms for the free PROP

    Package the three structural maps of a monoidal category — left
    unitor, right unitor, associator — as isomorphisms in [FreeCat S]
    using [T_cast].

    The arity-equations are pure [Nat] facts:

      [Nat.add_0_l n]      : 0 + n = n              (left unit)
      [Nat.add_0_r n]      : n + 0 = n              (right unit)
      [Nat.add_assoc x y z] : x + (y + z) = (x + y) + z   (associator)

    Because [Nat.add] is left-strict in Coq, the left unitor at
    [0 + n] is the identity definitionally; the right unitor and the
    associator require non-trivial casts. *)

Open Scope nat_scope.

Section Structural.

Context (S : Signature).

(** ** Left unitor: [0 + n ≅ n] in FreeCat S.

    Definitionally [0 + n = n] so the cast is along [eq_refl] and the
    unitor is the literal identity. *)
Program Definition FreeCat_unit_left (n : nat) : @Isomorphism (FreeCat S) (0 + n) n := {|
  to   := T_cast (Nat.add_0_l n);
  from := T_cast (eq_sym (Nat.add_0_l n))
|}.
Next Obligation. apply T_cast_inv_sym. Qed.
Next Obligation. apply T_cast_inv. Qed.

(** ** Right unitor: [n + 0 ≅ n] in FreeCat S.

    [Nat.add_0_r] is propositional, not definitional, so the cast is
    along a non-trivial equation. *)
Program Definition FreeCat_unit_right (n : nat) : @Isomorphism (FreeCat S) (n + 0) n := {|
  to   := T_cast (Nat.add_0_r n);
  from := T_cast (eq_sym (Nat.add_0_r n))
|}.
Next Obligation. apply T_cast_inv_sym. Qed.
Next Obligation. apply T_cast_inv. Qed.

(** ** Associator: [(x + y) + z ≅ x + (y + z)] in FreeCat S.

    Likewise propositional via [Nat.add_assoc]. *)
Program Definition FreeCat_tensor_assoc (x y z : nat)
  : @Isomorphism (FreeCat S) ((x + y) + z) (x + (y + z)) := {|
  to   := T_cast (eq_sym (Nat.add_assoc x y z));
  from := T_cast (Nat.add_assoc x y z)
|}.
Next Obligation. apply T_cast_inv. Qed.
Next Obligation. apply T_cast_inv_sym. Qed.

End Structural.

Close Scope nat_scope.

Arguments FreeCat_unit_left  S n : assert.
Arguments FreeCat_unit_right S n : assert.
Arguments FreeCat_tensor_assoc S x y z : assert.
