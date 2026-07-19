Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.

Section SymmetricMonoidal.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

   A symmetric monoidal category is a braided monoidal category whose braiding
   is its own inverse: the symmetry condition is

       braid ∘ braid ≈ id[x ⨂ y]

   i.e. β_{y,x} ∘ β_{x,y} = 1_{x ⨂ y}, "switching twice has no effect". A
   braided monoidal category carries two hexagon identities; under symmetry
   either one implies the other, so a symmetric monoidal category is fully
   determined by its underlying braided structure together with braid_invol. *)

(* Where symmetric monoidal categories come from, and what they are for

   nLab:
   https://ncatlab.org/nlab/show/coherence+theorem+for+symmetric+monoidal+categories
   Paper: Mac Lane, "Natural Associativity and Commutativity", Rice
          University Studies 49, 1963
   Paper: Mac Lane, "Categorical Algebra", Bull. Amer. Math. Soc. 71, 1965

   The axioms answer a question Mac Lane posed and settled in 1963: how to
   say that a tensor product commutes when it commutes only up to
   isomorphism.  In vector spaces, V ⊗ W and W ⊗ V are isomorphic but not
   equal, and the chosen isomorphisms must cohere with the associator and
   unitors (Mac Lane 1963, above; the nLab records contemporaneous
   treatments by Bénabou, C. R. Acad. Sci. Paris 258, 1964, and by
   Eilenberg and Kelly, "Closed Categories", in the La Jolla proceedings,
   1966).  The braided axioms alone do not settle the matter: they allow
   the double crossing x ⨂ y ~> y ⨂ x ~> x ⨂ y to be a nontrivial
   automorphism, as it genuinely is in categories of braids and ribbons
   (Joyal, Street, "Braided tensor categories", Advances in Mathematics
   102, 1993).  The single law [braid_invol] removes exactly that freedom,
   and the reward is Mac Lane's coherence theorem for the symmetric case:
   every diagram built from associators, unitors, and symmetries commutes,
   provided its two sides induce the same permutation of the tensor
   factors.  It follows that one may reason as though an iterated tensor
   were a multiset of factors, and that every symmetric monoidal category
   is equivalent to a permutative one, strictly associative and strictly
   unital.  The lemmas [bimap_braid] and [braid_bimap_braid] below are
   small instances of this collapse, and [hexagon_rotated] shows one
   hexagon absorbing the other, as the header remarks.

   Read computationally, [braid] swaps two parallel wires, and
   [braid_invol] says the wires cross with no memory of the crossing —
   precisely where the symmetric case parts from the braided one, whose
   over- and under-crossings differ.  Coherence then licenses tracking
   only the permutation when replumbing a parallel composite, the
   soundness behind string-diagram calculi such as the signal-flow graphs
   of Fong and Spivak ("An Invitation to Applied Category Theory", CUP
   2019, ch. 5).  Cartesian categories supply the everyday examples: Set,
   Cat, and any category with finite products, where the braiding is the
   argument swap, realized in-tree as [CC_SymmetricMonoidal] in
   Structure/Monoidal/Internal/Product.v.

   The definition organizes whole subjects downstream.  Mac Lane's PROPs
   ("Categorical Algebra", 1965, from joint work with Adams) are strict
   symmetric monoidal categories whose objects are the natural numbers
   and whose tensor is addition; their models are symmetric monoidal
   functors ([SymmetricMonoidalFunctor] in
   Functor/Structure/Monoidal/Braided.v), and they present structures
   such as bialgebras that neither operads nor Lawvere theories reach —
   the library's free-PROP spine (Construction/PROP.v, whose class
   carries [prop_symmetric]) rests on this file.  In logic, closed
   symmetric monoidal categories model multiplicative intuitionistic
   linear logic (Girard 1987): the tensor is conjunction of resources,
   and the missing contraction rule means a consumed resource is gone;
   the classical case asks in addition for a dualizing object (Seely,
   "Linear logic, *-autonomous categories and cofree coalgebras", 1989),
   which Structure/Monoidal/StarAutonomous.v adds atop its [SymMonClosed]
   base.  Resource theories in the sense of Coecke, Fritz, and Spekkens
   ("A mathematical theory of resources", Information and Computation
   250, 2016) are symmetric monoidal categories outright — objects are
   resources, morphisms are the free transformations — a reading
   continued by the copy/discard and Markov developments
   (Structure/Monoidal/CopyDiscard.v, Structure/Monoidal/Markov.v), while
   Baez and Stay ("Physics, Topology, Logic and Computation: A Rosetta
   Stone", 2009) take closed symmetric monoidal categories as the grammar
   shared by Hilbert spaces, cobordisms, proofs, and programs.  For the
   semantics of effects, Kock's theorem matches commutative monads with
   symmetric monoidal monads over a symmetric monoidal closed base (Kock,
   "Strong functors and monoidal monads", Archiv der Mathematik 23,
   1972); in-tree, the Kleisli category of a commutative monad is again
   symmetric monoidal ([Kleisli_Symmetric] in
   Monad/Kleisli/Commutative.v), so independent effectful computations
   may be scheduled in either order.  Traced monoidal structure layers
   feedback on the same symmetric base (Structure/Monoidal/Traced.v, with
   [traced_is_symmetric] a coercion into this class). *)

Class SymmetricMonoidal := {
  (* The underlying braided monoidal structure (braiding + hexagon laws). *)
  symmetric_is_braided : @BraidedMonoidal C;

  (* Symmetry: the braiding is its own inverse, β_{y,x} ∘ β_{x,y} = id. *)
  braid_invol {x y} : braid ∘ braid ≈ id[x ⨂ y];
}.
#[export] Existing Instance symmetric_is_braided.

Coercion symmetric_is_braided : SymmetricMonoidal >-> BraidedMonoidal.

Context `{SymmetricMonoidal}.

(* A rotated form of the hexagon identity, available once the braiding is
   symmetric: the second hexagon is recovered from the first via braid_invol. *)
Lemma hexagon_rotated {x y z} :
  tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc ⁻¹
    << x ⨂ (y ⨂ z) ~~> y ⨂ (x ⨂ z) >>
  id ⨂ braid ∘ tensor_assoc ∘ braid.
Proof.
  rewrite <- (id_right (id ⨂ braid ∘ tensor_assoc ∘ braid)).
  rewrite <- (iso_to_from tensor_assoc).
  rewrite comp_assoc;
  rewrite <- (comp_assoc _ tensor_assoc braid);
  rewrite <- (comp_assoc _ (tensor_assoc ∘ braid) _).
  rewrite hexagon_identity.
  rewrite !comp_assoc.
  rewrite <- bimap_comp; rewrite id_left.
  rewrite braid_invol.
  cat.
Qed.

(* Naturality of the braiding, transposed: braid commutes a tensor of two
   morphisms past itself, swapping the order of the factors. *)
Lemma bimap_braid {x y z w} (f : x ~> z) (g : y ~> w) :
  g ⨂ f ∘ braid ≈ braid ∘ f ⨂ g.
Proof.
  spose (braid_natural _ _ f _ _ g) as X.
  normal.
  apply X.
Qed.

(* Conjugating a swapped tensor by the braiding on both sides recovers the
   original tensor; combines bimap_braid with the symmetry law braid_invol. *)
Lemma braid_bimap_braid {x y z w} (f : x ~> z) (g : y ~> w) :
  braid ∘ g ⨂ f ∘ braid ≈ f ⨂ g.
Proof.
  rewrite <- comp_assoc.
  rewrite bimap_braid.
  rewrite comp_assoc.
  rewrite braid_invol.
  cat.
Qed.

End SymmetricMonoidal.

Require Export Category.Structure.Monoidal.Balanced.

(* A balanced monoidal category whose twist is the identity is symmetric: the
   balancing axiom braid ∘ twist ⨂ twist ∘ braid ≈ twist then degenerates to
   the symmetry law braid ∘ braid ≈ id. *)
Program Definition balanced_twist_id_is_symmetric
  `{@BalancedMonoidal C}
  (to_twist : ∀ x : C, to twist ≈[C] to (@iso_id _ x)) :
  @SymmetricMonoidal C := {|
  braid_invol := _;
|}.
Next Obligation.
  pose proof (@balanced_to_commutes _ _ x y).
  rewrite <- to_twist.
  rewrite <- X; clear X.
  comp_left.
  rewrite <- id_left at 1.
  comp_right.
  rewrite !to_twist.
  now rewrite bimap_id_id.
Qed.

(* ncatlab: "Every symmetric monoidal category is balanced in a canonical way;
   in fact, the identity natural transformation (on the identity functor of
   BB) is a balance on BB if and only if BB is symmetric. Thus balanced
   monoidal categories fall between braided monoidal categories and symmetric
   monoidal categories." *)

Program Definition symmetric_is_balanced `{@SymmetricMonoidal C} :
  @BalancedMonoidal C := {|
  twist := @iso_id C
|}.
Next Obligation.
  rewrite bimap_id_id.
  rewrite id_right.
  apply braid_invol.
Qed.
Next Obligation.
  rewrite bimap_id_id.
  rewrite id_right.
  apply braid_invol.
Qed.
