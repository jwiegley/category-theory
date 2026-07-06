Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Braided.

Generalizable All Variables.

(** * The symmetric monoidal structure on the free PROP *)

(* nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   A PROP is a SYMMETRIC strict monoidal category, so the braiding
   [T_braid m n] installed on [FreeCat S] by
   [Construction/PROP/Braided.v] must be its own inverse.  That is
   precisely the [TE_braid_invol] axiom of [TermEq]:

     σ_{n,m} ⊙ σ_{m,n} ≈ id_{m+n}

   — crossing an [m]-wide bundle of wires past an [n]-wide bundle and
   back again untangles completely.  Since the tensor of [FreeCat S]
   is [Nat.add] on objects, [m ⨂ n] and [m + n] agree definitionally
   and the axiom matches the [braid_invol] field of
   [SymmetricMonoidal] verbatim.

   The [symmetric_is_braided] field names [FreeCat_Braided S], whose
   own [braided_is_monoidal] field names THE shared [Monoidal] record
   [FreeCat_Monoidal S]: the Strict and bundled PROP instances
   downstream project this single record as well, so their agreement
   is definitional.

   The synonym lemma [braid_invol] of [Construction/PROP/Naturality.v]
   is deliberately not imported here: its name would shadow the
   [SymmetricMonoidal] projection of the same name (the [Free.v]
   discipline of standalone-lemma-then-explicit-record keeps the
   record literal free of Program obligations, but the field names
   themselves must still resolve to the class projections). *)

Section FreeSymmetric.

Context (S : Signature).

Open Scope nat_scope.

(** ** Braid involution

    The [braid_invol] field of [SymmetricMonoidal] at [x y]: the
    composite [σ_{y,x} ⊙ σ_{x,y} : x + y ⇒ x + y] is the identity.
    This is the primitive constructor [TE_braid_invol] applied at
    [m := x], [n := y]. *)

Lemma free_braid_invol (x y : nat) :
  TermEq S (T_comp (T_braid y x) (T_braid x y)) (T_id (x + y)).
Proof.
  apply TE_braid_invol.
Qed.

(** ** THE SymmetricMonoidal record on [FreeCat S]

    [symmetric_is_braided] names the ONE braided record
    [FreeCat_Braided S] (hence, through it, the ONE shared [Monoidal]
    record [FreeCat_Monoidal S]); the involution proof is the
    standalone lemma above.  Every field is explicit, so no Program
    obligations are generated. *)

Program Definition FreeCat_Symmetric : @SymmetricMonoidal (FreeCat S) := {|
  symmetric_is_braided := FreeCat_Braided S;
  braid_invol := fun x y => free_braid_invol x y
|}.

End FreeSymmetric.

Arguments FreeCat_Symmetric S : assert.
