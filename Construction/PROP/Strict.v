Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Monoidal.

From Coq Require Import Arith.

Generalizable All Variables.

(** * The Strict structure on the free PROP *)

(* nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   [FreeCat S] is STRICT monoidal: its objects are natural numbers, its
   tensor on objects is addition, and the arity equations

     [Nat.add_assoc x y z] : x + (y + z) = (x + y) + z   (associativity)
     [Nat.add_0_l x]       : 0 + x = x                   (left unit)
     [Nat.add_0_r x]       : x + 0 = x                   (right unit)

   are honest Leibniz equalities of objects — exactly the object-level
   strictness the [StrictMonoidal] class demands.  The comparison
   fields — that the structural isomorphisms of the monoidal structure
   coincide with the identity transported along those equalities — are
   reflexivity-grade here, because [Structural.v] BUILT the unitors and
   the associator as [T_cast] maps, and [T_cast e] is definitionally
   the very [match e in _ = T return _ ~> T with eq_refl => id end]
   shape that the class's fields ask for (with the SAME proof term [e]
   on both sides, so not even UIP is needed).

   Crucially, [strict_is_monoidal] is [FreeCat_Monoidal S] — THE shared
   [Monoidal] record from [Monoidal.v] that the Braided, Symmetric, and
   PROP instances also name — so all structure projections downstream
   agree definitionally.

   Following the [Free.v] discipline, the comparison proofs are
   standalone, named lemmas and the record is assembled with every
   field explicit, generating no Program obligations. *)

Section FreeStrict.

Context (S : Signature).

Open Scope nat_scope.

(** ** Comparison lemmas

    Each states that a structural map of [FreeCat_Monoidal S] equals
    the transported identity along the corresponding arity equation.
    Both sides are the same [match] on the same proof term, so each
    proof is [reflexivity]. *)

(** The associator [(x + y) + z ≅ x + (y + z)] is the transported
    identity along [eq_sym (Nat.add_assoc x y z)] — the orientation of
    [Structural.v]'s [to]. *)
Lemma FreeCat_strict_assoc_to (x y z : nat) :
  to (@tensor_assoc (FreeCat S) (FreeCat_Monoidal S) x y z)
  ≈ match eq_sym (Nat.add_assoc x y z) in _ = T
      return ((x + y) + z ~{ FreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(** The left unitor [0 + x ≅ x] is the transported identity along
    [Nat.add_0_l x] (definitionally trivial: [Nat.add] is left-strict). *)
Lemma FreeCat_strict_unit_left_to (x : nat) :
  to (@unit_left (FreeCat S) (FreeCat_Monoidal S) x)
  ≈ match Nat.add_0_l x in _ = T
      return (0 + x ~{ FreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(** The right unitor [x + 0 ≅ x] is the transported identity along
    [Nat.add_0_r x] (a genuinely propositional equation). *)
Lemma FreeCat_strict_unit_right_to (x : nat) :
  to (@unit_right (FreeCat S) (FreeCat_Monoidal S) x)
  ≈ match Nat.add_0_r x in _ = T
      return (x + 0 ~{ FreeCat S }~> T)
    with eq_refl => id end.
Proof. reflexivity. Qed.

(** ** The Strict instance over THE shared Monoidal record *)

Definition FreeCat_Strict : @StrictMonoidal (FreeCat S) := {|
  strict_is_monoidal    := FreeCat_Monoidal S;  (* THE shared record *)
  strict_assoc_obj      := fun x y z => eq_sym (Nat.add_assoc x y z);
  strict_unit_left_obj  := fun x => Nat.add_0_l x;
  strict_unit_right_obj := fun x => Nat.add_0_r x;
  strict_assoc_to       := fun x y z => FreeCat_strict_assoc_to x y z;
  strict_unit_left_to   := fun x => FreeCat_strict_unit_left_to x;
  strict_unit_right_to  := fun x => FreeCat_strict_unit_right_to x
|}.

End FreeStrict.

Arguments FreeCat_Strict S : assert.
