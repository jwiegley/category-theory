Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Monoidal natural transformations *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+natural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_natural_transformation

   Given lax monoidal functors (F, ε^F, μ^F) and (G, ε^G, μ^G) between the same
   monoidal categories, a natural transformation `N : F ⟹ G` is *monoidal* when
   its components are compatible with the monoidal comparisons of F and G. Two
   coherence conditions are imposed:

       lax_pure_transform : N_I ∘ ε^F ≈ ε^G            (unit compatibility),
       lax_ap_transform   : N_{x⊗y} ∘ μ^F_{x,y}
                              ≈ μ^G_{x,y} ∘ (N_x ⊗ N_y)  (tensor compatibility),

   following nLab and Wikipedia (`f_I ∘ ε_1 = ε_2` and
   `μ_2 ∘ (f_x ⊗ f_y) = f_{x⊗y} ∘ μ_1`). Equationally: comparing the unit, then
   transforming, agrees with the unit of the target; and tensoring two
   components, then comparing, agrees with comparing, then transforming. A
   monoidal natural transformation between symmetric monoidal functors is
   automatically a symmetric one, so no extra axiom is needed for that case. *)

Class LaxMonoidal_Transform `{@Monoidal C}
      `{!LaxMonoidalFunctor F}
      `{!LaxMonoidalFunctor G} (N : F ⟹ G) := {
  lax_pure_transform : lax_pure[G] ≈ transform[N] _ ∘ lax_pure[F];

  lax_ap_transform {x y} :
    lax_ap[G] ∘ transform[N] x ⨂ transform[N] y ≈ transform[N] _ ∘ lax_ap[F]
}.

Notation "lax_pure_transform[ N ]" := (@lax_pure_transform _ _ _ _ _ _ N _)
  (at level 9, format "lax_pure_transform[ N ]") : morphism_scope.
