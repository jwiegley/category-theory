Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.

Generalizable All Variables.

(** * The category of F-coalgebras *)

(* nLab:      https://ncatlab.org/nlab/show/coalgebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/F-coalgebra

   An F-coalgebra is an object [a] with a structure map [γ : a ~> F a]
   ([FCoalgebra F a] of Theory/Functor.v); a coalgebra morphism commutes with
   the structure maps.  This is exactly an [F^op]-algebra in [C^op], so the
   category is obtained by duality rather than re-proving the laws:

       FCoalg F := (FAlg (F^op))^op.

   Because the library's duality is definitional ([C^op^op = C] by
   reflexivity), the covariant components are the expected ones: objects are
   pairs [(a, γ : a ~> F a)] and the forgetful functor lands back in [C].  The
   final coalgebra (when it exists) is the greatest fixed point of [F];
   [lambek_final] (Theory/Lambek.v) makes its structure map an isomorphism. *)

Definition FCoalg `(F : C ⟶ C) : Category := (FAlg (F^op))^op.

(* A co-algebra hom-set of [FCoalg F] is, on the nose, an [F^op]-algebra hom of
   the opposite category. *)
Lemma fcoalg_hom `(F : C ⟶ C) (x y : FCoalg F) :
  (x ~{FCoalg F}~> y) = (y ~{FAlg (F^op)}~> x).
Proof. reflexivity. Qed.

(* The forgetful functor to the underlying category, by dualizing
   [FAlg_Forget] and using [C^op^op = C]. *)
Definition FCoalg_Forget `(F : C ⟶ C) : FCoalg F ⟶ C :=
  (FAlg_Forget (F^op))^op.
