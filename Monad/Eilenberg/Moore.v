Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.

Generalizable All Variables.

(** * The Eilenberg–Moore category of a monad. *)

(* nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   The Eilenberg–Moore category C^T of a monad (M, ret, join) = (T, η, μ) on C
   is the category of T-algebras and their homomorphisms (see Monad/Algebra.v).
   An object is a pair (a, ν) of a carrier a : C together with an action
   ν : T a ~> a (t_alg) satisfying the unit law ν ∘ η_a ≈ id and the
   associativity/action law ν ∘ T(ν) ≈ ν ∘ μ_a (t_id and t_action). A morphism
   (a, ν^a) ~> (b, ν^b) is an underlying C-morphism f : a ~> b that intertwines
   the actions, f ∘ ν^a ≈ ν^b ∘ T(f) (t_alg_hom_commutes).

   Identities and composition are inherited from C on the underlying carriers:
   id is id_a (which trivially commutes), and the composite of two algebra
   homomorphisms is again one — the obligation below pastes their two commuting
   squares, using fmap_comp for T(g ∘ f) and t_alg_hom_commutes twice.
   Equivalence of morphisms is equivalence of the underlying C-maps.

   The forgetful functor U^T : C^T → C, (a, ν) ↦ a, has the free-algebra
   functor F^T : C → C^T, x ↦ (T x, μ_x), as left adjoint, and the monad
   U^T ∘ F^T arising from F^T ⊣ U^T is exactly T. This is the terminal such
   resolution of T; the Kleisli category (see Monad/Kleisli.v) is the initial
   one, sitting inside C^T as the full subcategory of free algebras. *)

Program Definition EilenbergMoore `(T : C ⟶ C) `{@Monad C T} : Category := {|
  obj     := ∃ a : C, TAlgebra T a;
  hom     := fun x y => TAlgebraHom T ``x ``y (projT2 x) (projT2 y);
  homset  := fun _ _ => {| equiv := fun f g => t_alg_hom[f] ≈ t_alg_hom[g] |};
  id      := fun _ => {| t_alg_hom := id |};
  compose := fun _ _ _ f g => {| t_alg_hom := t_alg_hom[f] ∘ t_alg_hom[g] |}
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- t_alg_hom_commutes.
  rewrite <- !comp_assoc.
  rewrite <- t_alg_hom_commutes.
  reflexivity.
Qed.
