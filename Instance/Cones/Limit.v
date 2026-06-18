Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Cones.

Generalizable All Variables.

(** * Limit as a terminal cone *)

(* nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   Wikipedia: a limit "may also be characterized as terminal objects in the
   category of cones to F." nLab agrees: the limit lim F is the universal cone,
   "precisely the terminal object in the category of all cones over F", since
   every cone has a unique morphism into it.

   This file makes that characterization constructive: from a terminal object
   [T] of [Cones F] (see [Instance/Cones.v], the category whose objects are
   cones over F and whose morphisms are apex maps commuting with the legs) we
   build a [Limit F] (see [Structure/Limit.v]). The terminal cone becomes
   [limit_cone], and the universal property [ump_limits] is read off from
   terminality of [T]:

     - the mediating morphism on apexes is [`1 (one N)], the apex component of
       the unique cone map [! : N ~> T];
     - it satisfies the leg-factorization φ_x ∘ u ≈ ψ_x by [`2 (one N)], the
       commuting condition packaged into that cone morphism;
     - its uniqueness follows from [one_unique]: any apex map [v] carrying its
       own factorization proof [H] yields a cone morphism [(v; H)] into [T],
       which terminality forces to equal [one N] (hence v equals u on apexes).

   Dually, a colimit is the initial object of the category of cocones over F;
   that direction is obtained by instantiating this construction at [F^op] via
   [Cocones] (see [Instance/Cones.v]). *)
Program Definition Limit_Cones `(F : J ⟶ C) `{T : @Terminal (Cones F)} :
  Limit F := {|
  limit_cone := @terminal_obj _ T;
  ump_limits := fun N =>
    {| unique_obj := `1 (@one _ T N)
     ; unique_property := `2 (@one _ T N)
     ; uniqueness       := fun v H => @one_unique _ T N (@one _ T N) (v; H) |}
|}.
