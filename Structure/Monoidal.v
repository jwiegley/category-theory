Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Monoidal.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

   A monoidal category is a category equipped with a tensor product and a
   unit object that are associative and unital up to coherent isomorphism.
   The data are a unit object I, a tensor bifunctor ⊗ : C ∏ C ⟶ C, and three
   natural isomorphisms,

       lambda  : I ⊗ x ≅ x              ([unit_left]),
       rho     : x ⊗ I ≅ x              ([unit_right]),
       alpha   : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)   ([tensor_assoc]),

   the left unitor, the right unitor, and the associator respectively. The
   associator direction (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z) follows nLab; the opposite
   orientation appears in some sources and differs only by inverses.

   Naturality of each isomorphism is recorded explicitly, in both the forward
   (to) and inverse (from) directions, so rewriting and dualization work
   either way. For lambda this is the square g ∘ λ ≈ λ ∘ (id ⊗ g), and
   similarly for rho and alpha.

   Two coherence conditions govern the interaction of these isomorphisms:

       triangle:  (ρ ⊗ id) ≈ (id ⊗ λ) ∘ α   on   (x ⊗ I) ⊗ y
       pentagon:  (id ⊗ α) ∘ α ∘ (α ⊗ id) ≈ α ∘ α
                                              on  ((x ⊗ y) ⊗ z) ⊗ w

   The triangle identity relates the unitors to the associator across the
   unit; the pentagon identity makes the two reassociations of a fourfold
   tensor agree. By Mac Lane's coherence theorem these two laws force every
   formal diagram built from α, λ, ρ to commute. *)

(* Origins, coherence, and the reach of the tensor

   nLab:  https://ncatlab.org/nlab/show/monoidal+category
   Paper: Bénabou, "Catégories avec multiplication", C. R. Acad. Sci.
          Paris 256, 1963
   Paper: Mac Lane, "Natural Associativity and Commutativity", Rice
          University Studies 49(4), 1963
   Paper: Kelly, "On MacLane's conditions for coherence of natural
          associativities, commutativities, etc.", J. Algebra 1(4), 1964
   Paper: Joyal, Street, "The geometry of tensor calculus, I", Advances
          in Mathematics 88(1), 1991
   Paper: Baez, Stay, "Physics, Topology, Logic and Computation: A
          Rosetta Stone", 2009 (arXiv:0903.0340)

   The notion entered the literature twice in 1963: Bénabou introduced
   categories with a multiplication in the Comptes Rendus, and Mac Lane
   isolated the coherence question and proved the first coherence
   theorem.  Mac Lane's original axiom list was longer than the one
   below; Kelly (1964) showed the surplus redundant, deriving the
   remaining unit laws — among them λ_{x⊗y} ∘ α ≈ λ_x ⊗ id and
   λ_I ≈ ρ_I — from the pentagon, one triangle, and naturality.  That
   reduction is why the [Monoidal] class carries exactly two coherence
   fields, [triangle_identity] and [pentagon_identity], and why
   Structure/Monoidal/Proofs.v can restate Kelly's derived equations as
   rewriting lemmas rather than axioms.  Coherence also has a modern
   repackaging: every monoidal category is monoidally equivalent to a
   strict one, in which α, λ, ρ are identities (the strict notion is
   Structure/Monoidal/Strict.v) — though not, nLab cautions, to a
   skeletal strict one, with (Set, ×) the standard counterexample.

   The definition answers a precise design problem.  Many categories
   carry a combining operation that is associative and unital only up
   to isomorphism — the tensor product of vector spaces reassociates
   canonically but not equally — so demanding equality would exclude
   nearly every example, while demanding bare isomorphism would let two
   different composites of structural maps join the same bracketings.
   Taking λ, ρ, α as structure and imposing the triangle and pentagon
   is the middle course: Mac Lane proved it sufficient, and Kelly
   trimmed the axioms required to exactly these two.

   Equally deliberate is what the definition omits: [tensor] need not
   be the categorical product.  A cartesian tensor comes with diagonals
   and projections, so every object can be copied and deleted; a
   general tensor supplies neither, which is precisely the situation of
   quantum systems (no-cloning) and of the multiplicative conjunction
   of resources consumed exactly once (Girard, "Linear logic",
   Theoretical Computer Science 50, 1987).  Monoidal categories are
   thus the home of resource-like combination, the cartesian case being
   characterized by Fox's theorem in-tree
   (Structure/Monoidal/Heunen_Vicary.v, Structure/Monoidal/Markov/Fox.v).
   Under the Baez–Stay reading, composition ∘ is process in series and
   ⊗ is process in parallel: given f : x ~> y and g : z ~> w, the map
   f ⊗ g does both jobs at once.  Joyal and Street (1991) made the
   accompanying string-diagram notation rigorous — a diagrammatic
   equality holds precisely when it follows from these axioms, so
   deforming the picture is a sound and complete proof method for
   structural equations.

   Within category theory the class is load-bearing infrastructure.
   Endofunctor categories are strict monoidal under composition, and
   monoids in them are monads; monoid objects (Theory/Algebra/Monoid.v),
   enriched categories (Construction/Enriched.v), and Day convolution
   (Construction/Day.v) all presuppose a monoidal base; and a monoidal
   category is exactly a one-object bicategory — every field of
   Theory/Bicategory.v mirrors a field here, with the delooping realized
   in Theory/Bicategory/OneObject.v.  The structure-preserving functors
   live in Functor/Structure/Monoidal.v, whose lax variant, given a
   strength on Coq's cartesian structure, is the programmer's
   applicative functor (Functor/Applicative.v,
   Theory/Coq/Applicative/Proofs.v, Instance/Coq/Applicative.v).  The
   braided and symmetric towers (Structure/Monoidal/Braided.v,
   Structure/Monoidal/Symmetric.v), the linear-logic superstructure
   (Structure/Monoidal/StarAutonomous.v, after Seely 1989), and the
   effectful weakening to premonoidal categories (Structure/Premonoidal.v,
   with the equivalence in Structure/Premonoidal/Monoidal.v) all take
   this file as their root. *)

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;                        (* unit_obj *)
  tensor : C ∏ C ⟶ C where "x ⨂ y" := (tensor (x, y));

  unit_left  {x} : I ⨂ x ≅ x;  (* lambda *)
  unit_right {x} : x ⨂ I ≅ x;  (* rho *)

  tensor_assoc {x y z} : (x ⨂ y) ⨂ z ≅ x ⨂ (y ⨂ z);  (* alpha *)

  (* alpha, lambda and rho are all natural isomorphisms. *)

  to_unit_left_natural {x y} (g : x ~> y) :
    g ∘ unit_left << I ⨂ x ~~> y >> unit_left ∘ bimap id g;
  from_unit_left_natural {x y} (g : x ~> y) :
    bimap id g ∘ unit_left⁻¹ << x ~~> I ⨂ y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {x y} (g : x ~> y) :
    g ∘ unit_right << x ⨂ I ~~> y >> unit_right ∘ bimap g id;
  from_unit_right_natural {x y} (g : x ~> y) :
    bimap g id ∘ unit_right⁻¹ << x ~~> y ⨂ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap g (bimap h i) ∘ tensor_assoc
      << (x ⨂ z) ⨂ v ~~> y ⨂ w ⨂ u >>
    tensor_assoc ∘ bimap (bimap g h) i;

  from_tensor_assoc_natural
    {x y z w v u} (g : x ~> y) (h : z ~> w) (i : v ~> u) :
    bimap (bimap g h) i ∘ tensor_assoc⁻¹
      << x ⨂ z ⨂ v ~~> (y ⨂ w) ⨂ u >>
    tensor_assoc⁻¹ ∘ bimap g (bimap h i);

  (* The above observe the following coherence conditions:
     the triangle identity (unitors vs. associator) and the pentagon
     identity (the two reassociations of a fourfold tensor agree). *)

  triangle_identity {x y} :
    bimap unit_right id
      << (x ⨂ I) ⨂ y ~~> x ⨂ y >>
    bimap id unit_left ∘ tensor_assoc;

  pentagon_identity {x y z w} :
    bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
      << ((x ⨂ y) ⨂ z) ⨂ w ~~> x ⨂ (y ⨂ (z ⨂ w)) >>
    tensor_assoc ∘ tensor_assoc
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "x ⨂ y" := (@tensor _ _ (x%object, y%object))
  (at level 30, right associativity) : object_scope.
Notation "x ⨂[ M ] y" := (fobj[@tensor _ M] (x, y))
  (at level 30, only parsing, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.
Notation "f ⨂[ M ] g" := (bimap[@tensor _ M] f g)
  (at level 30, only parsing, right associativity) : morphism_scope.
