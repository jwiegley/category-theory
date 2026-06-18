Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Either.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** Law proofs for the Either/sum [a + b] instances *)

(* nLab: https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   The instances themselves live in [Theory/Coq/Either.v]; here we record their
   lawfulness.  Fixing the left summand [E], the endofunctor [b ↦ E + b] is a
   genuine endofunctor on [Coq], and [Either_Functor : IsFunctor] discharges the
   two functor laws -- identity [fmap id = id] and composition
   [fmap (g ∘ f) = fmap g ∘ fmap f] -- by exhibiting it as an [AFunctor], exactly
   as the sibling [Maybe] and [Tuple] proof files do.  The three obligations are
   the [AFunctor] fields: [fmap] respects pointwise equality, and the identity
   and composition laws, each proven by case analysis on the [Left]/[Right] tag.

   Following the house pattern, only the [Functor] instance is proven lawful
   here; lawfulness of the applicative/monad structure is discharged per
   concrete use. *)

Program Definition Either_Functor {E} : IsFunctor (@Either_Functor E) := {|
  a_fmap := @Either_Functor E;
|}.
Next Obligation.
  proper.
  simpl.
  now rewrite H.
Qed.
Next Obligation.
  destruct x0; simpl; congruence.
Qed.
Next Obligation.
  destruct x0; simpl; congruence.
Qed.
