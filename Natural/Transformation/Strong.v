Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Strong.

Generalizable All Variables.

(** Strong natural transformations (compatible with tensorial strength) *)

(* nLab: https://ncatlab.org/nlab/show/strong+natural+transformation
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   Given two strong endofunctors F, G : C ⟶ C on a monoidal category, each
   carrying a left strength strength[F], strength[G] (see Functor.Strong), a
   natural transformation N : F ⟹ G is *strong* when it is compatible with the
   two strengths, i.e. the square

     x ⨂ F y --- id ⨂ N_y ---> x ⨂ G y
        |                          |
     strength[F]               strength[G]
        |                          |
        v                          v
     F (x ⨂ y) --- N_{x⨂y} ---> G (x ⨂ y)

   commutes:  N_{x⨂y} ∘ strength[F] ≈ strength[G] ∘ (id_x ⨂ N_y).  This is the
   notion of morphism between strong functors that respects strength (Kock 1972;
   Moggi 1991; Ratkovic 2012, Def. 3.1.4); in the closed setting it corresponds
   to an enriched natural transformation between the induced C-enrichments.  No
   extra coherence beyond this single square is required: ordinary naturality of
   N already supplies the rest. *)

Class Strong_Transform {C : Category} `{@Monoidal C}
      {F : C ⟶ C} `{@StrongFunctor _ _ F}
      {G : C ⟶ C} `{@StrongFunctor _ _ G} (N : F ⟹ G) := {
  strength_transform {x y} :                         (* strength-compatibility square *)
    strength[G] ∘ id[x] ⨂ transform[N] y ≈ transform[N] _ ∘ strength[F]
}.
