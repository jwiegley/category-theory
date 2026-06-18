Require Import Category.Lib.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Applicative.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Natural.Transformation.Monoidal.

Generalizable All Variables.

(** Morphisms of applicative functors. *)

(* nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   A morphism of applicative functors -- McBride and Paterson's "applicative
   transformation" ("Applicative programming with effects", JFP 18(1), 2008,
   §5) -- is a natural transformation N : F ⟹ G between applicative functors
   that respects the applicative operations:

       N (pure x)  ≈ pure x,
       N (f <*> x) ≈ N f <*> N x.

   Since an applicative functor is here a strong lax monoidal endofunctor
   (see Functor/Applicative.v), and [pure]/[ap] are recovered from the lax
   monoidal comparison maps (lax_pure, lax_ap = η, μ) together with the
   strength, preserving the FP operations is equivalent to preserving that
   underlying structure.  Accordingly [Applicative_Transform] is packaged as a
   natural transformation that is simultaneously a [Strong_Transform] (commutes
   with the tensorial strength) and a [LaxMonoidal_Transform] (commutes with
   lax_pure and lax_ap) -- the transformation-level analogue of the way
   [Applicative] bundles [StrongFunctor] with [LaxMonoidalFunctor].  These two
   conditions jointly entail the [pure]- and [<*>]-preservation laws above.

   This is the categorical, law-respecting account; the lawless FP version
   lives in Theory/Coq/Applicative.v. *)

Class Applicative_Transform `{@ClosedMonoidal C}
  `{@Applicative C _ F}
  `{@Applicative C _ G} (N : F ⟹ G) := {
  applicative_transform_is_strong_transformation :
    @Strong_Transform C _ F _ G _ N;
  applicative_transform_is_lax_monoidal_transformation :
    @LaxMonoidal_Transform C _ F _ G _ N
}.
#[export] Existing Instance applicative_transform_is_strong_transformation.
#[export] Existing Instance applicative_transform_is_lax_monoidal_transformation.

Coercion applicative_transform_is_strong_transformation :
  Applicative_Transform >-> Strong_Transform.
Coercion applicative_transform_is_lax_monoidal_transformation :
  Applicative_Transform >-> LaxMonoidal_Transform.
