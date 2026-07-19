Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.

Generalizable All Variables.

(** The arrow category C^→ (also written Arr(C), C², or [2, C]). *)

(* nLab: https://ncatlab.org/nlab/show/arrow+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   The arrow category of C has as objects the morphisms of C and as morphisms
   the commuting squares of C: a morphism from (f : a₀ ~> a₁) to (g : b₀ ~> b₁)
   is a pair (u : a₀ ~> b₀, v : a₁ ~> b₁) with g ∘ u ≈ v ∘ f, i.e. the square

       a₀  --u-->  b₀
        |           |
       f            g           commute, i.e.  g ∘ u ≈ v ∘ f.
        v           v
       a₁  --v-->  b₁

   It is here defined as the comma category (Id[C] ↓ Id[C]) of the identity
   functor against itself (see Construction/Comma.v); taking S = T = Id[C] in
   the comma construction collapses its objects (a, b, h : S a ~> T b) to plain
   morphisms a ~> b of C and its morphisms to commuting squares as above.

   Equivalently the arrow category is the functor category [2, C], where 2 is
   the interval (walking-arrow) category {0 → 1}; the standard notations C^→,
   Arr(C), C², and [2, C] all denote this category. The domain and codomain
   functors C^→ ⟶ C are the comma projections comma_proj1 and comma_proj2 of
   Construction/Comma.v specialized to S = T = Id[C]. *)

(* Morphisms as objects: lifting, factorization, and the self-indexing

   nLab: https://ncatlab.org/nlab/show/weak+factorization+system
   nLab: https://ncatlab.org/nlab/show/orthogonal+factorization+system
   nLab: https://ncatlab.org/nlab/show/codomain+fibration
   nLab: https://ncatlab.org/nlab/show/display+map
   nLab: https://ncatlab.org/nlab/show/adjoint+string

   The arrow category is the device that makes the morphisms of C
   first-class: statements about maps become ordinary category theory
   inside C ⃗.  A commuting square is no longer a diagram condition but a
   single morphism; a class of maps — monomorphisms, fibrations, display
   maps — is a full subcategory; and closure of such a class under
   retracts or under limits means retracts or limits computed in the
   arrow category.  Because Cat is cartesian closed, the [2, C] reading
   of the header exhibits the arrow category as an exponential, the
   directed path object of C: functors X ⟶ Arr(Y) correspond exactly to
   natural transformations between functors X ⟶ Y (nLab, arrow
   category), just as a natural transformation F ⟹ G is a functor out
   of C × 2 restricting to F and G at the two endpoints of the walking
   arrow (Riehl, "Category Theory in Context", Dover 2016) — a homotopy
   at the level of categories.  Defining [Arrow] as the comma
   (Id[C] ↓ Id[C]) obtains all of this from the already-proven comma
   machinery: the category laws arrive as instances, and
   [comma_proj_nat] of Construction/Comma.v specializes to the generic
   arrow, the natural transformation dom ⟹ cod whose component at an
   object f of the arrow category is f itself.  The projections moreover
   flank the identity-arrow functor x ↦ id[x] in an adjoint triple
   cod ⊣ ids ⊣ dom (nLab, adjoint string).

   The classical applications run through homotopy theory.  The lifting
   problems of Quillen's model categories (Quillen, "Homotopical
   Algebra", Springer Lecture Notes in Mathematics 43, 1967) are
   commuting squares — that is, morphisms e → m of the arrow category —
   and both classes of a weak factorization system are closed under
   retracts formed there, a model structure being precisely two
   interlocking such systems (nLab, weak factorization system; model
   category).  In this library, Theory/Orthogonality.v states unique
   lifting in exactly this square form and proves the retract closure
   [ortho_left_retract].  Orthogonal factorization systems — first
   studied by Mac Lane ("Duality for groups", Bull. AMS 56, 1950),
   essentially present in Freyd and Kelly ("Categories of continuous
   functors, I", J. Pure Appl. Algebra 2, 1972), and named by Bousfield
   ("Constructions of factorization systems in categories", J. Pure
   Appl. Algebra 9, 1977) — likewise live here: the two classes are
   replete subcategories of the arrow category (nLab, orthogonal
   factorization system), and the construction itself carries the
   classifying monad, an orthogonal factorization system on K being an
   Eilenberg–Moore algebra, appropriately defined, for the monad of the
   squaring endofunctor K ↦ K² on Cat (Korostenski and Tholen, "Factorization
   systems as Eilenberg-Moore algebras", J. Pure Appl. Algebra 85,
   1993).  In-tree the systems are the class [OFS] of
   Structure/Factorization.v.

   The codomain projection opens fibred category theory.  The codomain
   functor [comma_proj2] is always a Grothendieck opfibration, and is a
   fibration exactly when C has pullbacks — the cartesian lift of a map
   is its pullback square — with the slice categories C/c as fibres
   (Construction/Slice.v), whence its names "self-indexing" and
   "fundamental fibration" (nLab, codomain fibration).  This library
   proves the fibred presentation equivalent to the present one:
   Construction/Displayed/Codomain.v renders the arrow category
   displayed over C, establishes the isomorphism
   [Codomain_Total_Arrow_iso] in Cat, and builds the cartesian lifts
   from chosen pullbacks in [codomain_cleaving].  Pullback-closed full
   subcategories of the arrow category are Taylor's classes of display
   maps, the semantic counterpart of dependent types: a display map
   p : B → A models the judgement x:A ⊢ B(x), with substitution
   interpreted as pullback, and in homotopy type theory the display
   maps are the fibrations (Taylor, "Practical Foundations of
   Mathematics", CUP 1999; nLab, display map).  The [2, C] equivalence
   of the header, by contrast, remains documentation-level: no formal
   comparison with a functor category over the walking arrow [_2] of
   Instance/Two.v is developed in-tree, and the codomain isomorphism
   above is the comparison this library actually proves. *)

Definition Arrow {C : Category} : Category := (Id[C] ↓ Id[C]).

Notation "C ⃗" := (@Arrow C) (at level 90) : category_scope.
