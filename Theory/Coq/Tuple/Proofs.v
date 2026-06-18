Require Import Coq.Lists.List.

Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Tuple.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** Law proofs for the pair/tuple [A * B] instances *)

(* nLab: https://ncatlab.org/nlab/show/product
   nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Functor_(functional_programming)

   These are the characterisation/law proofs for the tuple instances defined
   in [Theory.Coq.Tuple].  [uncurry_works] is the computation (β) rule for
   [uncurry], one direction of the currying iso [(a * b) → c ≅ a → (b → c)].
   [fst_snd] and [unsplit] are the surjective-pairing (η) law for the binary
   product, [⟨fst z, snd z⟩ = z] (nLab's uniqueness/reflection rule
   [⟨π₁ ∘ g, π₂ ∘ g⟩ = g]), the latter lifted pointwise through [map].
   [Tuple_Functor] witnesses that the second-argument functor [(x * −)] is a
   lawful endofunctor on [Coq], packaging it as an [IsFunctor].

   Equality here is plain Coq [=] (pairs are inductive with decidable
   structure), and the proofs are axiom-free. *)

Theorem uncurry_works : forall {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
  uncurry f (x, y) = f x y.
Proof. reflexivity. Qed.

(* Surjective pairing (the product η law): rebuilding a pair from its
   projections recovers the original. *)
Lemma fst_snd : forall a b (z : a * b),
  (let '(x, y) := z in (x, y)) = (fst z, snd z).
Proof. intros ? ? [?]; auto. Qed.

(* The same η law lifted through [map]: since [fun x => (fst x, snd x)] is the
   identity on pairs, mapping it over a list is the identity. *)
Lemma unsplit : forall a b (xs : list (a * b)),
  map (fun x => (fst x, snd x)) xs = xs.
Proof.
  intros.
  induction xs as [|x xs IHxs]; auto; simpl.
  rewrite IHxs.
  destruct x; auto.
Qed.

(* The second-argument functor [(x * −)] is a lawful endofunctor on [Coq]; as
   with [arrow_IsFunctor], the witness reuses the [Functor] instance for
   [a_fmap], and the only nontrivial obligation is that [prod_map] respects
   pointwise equality of functions. *)
Program Definition Tuple_Functor {x} : IsFunctor (Tuple_Functor x) := {|
  a_fmap := Tuple_Functor x;
|}.
Next Obligation.
  proper.
  simpl.
  now rewrite H.
Qed.
