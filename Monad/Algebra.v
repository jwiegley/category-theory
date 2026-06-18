Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.

Generalizable All Variables.

(** * Algebras over a monad (Eilenberg–Moore algebras) *)

(* nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   For a monad (T, ret, join) on a category C — with unit ret (η : Id ⟹ T)
   and multiplication join (μ : T ○ T ⟹ T) — a T-algebra on an object [a] is
   a structure map t_alg (h : T a ~> a) satisfying two laws. The unit law
   t_alg ∘ ret ≈ id (h ∘ η_a = id_a) says the structure map undoes the unit,
   and the action law t_alg ∘ fmap t_alg ≈ t_alg ∘ join (h ∘ T h = h ∘ μ_a)
   says it is compatible with the multiplication: flattening with μ first and
   acting once agrees with acting twice. These are the Eilenberg–Moore
   algebras; together with the morphisms below they form the Eilenberg–Moore
   category C^T (nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category),
   assembled in [Monad.Eilenberg.Moore]. The free algebra (T a, join) on each
   object recovers a left adjoint to the forgetful functor C^T ⟶ C. *)
Class TAlgebra `(T : C ⟶ C) `{@Monad C T} (a : C) := {
  t_alg : T a ~> a;

  t_id     : t_alg ∘ ret ≈ id;
  t_action : t_alg ∘ fmap t_alg ≈ t_alg ∘ join
}.

Arguments TAlgebra {C} T {_} a.

Notation "t_alg[ T ]" := (@t_alg _ _ _ _ T)
  (at level 9, format "t_alg[ T ]") : morphism_scope.

(* nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   A morphism of T-algebras (an algebra homomorphism) from (a, t_alg[F]) to
   (b, t_alg[G]) is an underlying arrow t_alg_hom (f : a ~> b) commuting with
   the structure maps: t_alg_hom ∘ t_alg[F] ≈ t_alg[G] ∘ fmap[T] t_alg_hom
   (f ∘ h_F = h_G ∘ T f). Equivalently, the square sending each algebra action
   through f agrees with first lifting f along T and then acting. *)
Class TAlgebraHom `(T : C ⟶ C) `{@Monad C T} (a b : C)
      (F : TAlgebra T a) (G : TAlgebra T b) := {
  t_alg_hom : a ~> b;

  t_alg_hom_commutes : t_alg_hom ∘ t_alg[F] ≈ t_alg[G] ∘ fmap[T] t_alg_hom
}.

Notation "t_alg_hom[ F ]" := (@t_alg_hom _ _ _ _ _ _ _ F)
  (at level 9, format "t_alg_hom[ F ]") : morphism_scope.
