Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Naturality.

Generalizable All Variables.

Section BraidedMonoidal.

Context {C : Category}.

(** Braided monoidal category. *)

(* nLab: https://ncatlab.org/nlab/show/braided+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category

   A braided monoidal category is a monoidal category equipped with a natural
   isomorphism, the braiding,

       beta : x ⊗ y ≅ y ⊗ x              ([braid]),

   that is compatible with the associator (alpha = [tensor_assoc]) by way of
   two hexagon identities. Writing the equations in this library's notation
   (composition reads right to left), they are

       alpha ∘ beta ∘ alpha
         = (id ⨂ beta) ∘ alpha ∘ (beta ⨂ id)
                                          ([hexagon_identity]),

       alpha⁻¹ ∘ beta ∘ alpha⁻¹
         = (beta ⨂ id) ∘ alpha⁻¹ ∘ (id ⨂ beta)
                                          ([hexagon_identity_sym]),

   where on the upper path the middle [braid] is the braiding of one object
   past a whole tensor product (B_{x, y⊗z} and B_{x⊗y, z} respectively). The
   first hexagon braids x past y ⊗ z; the second braids x ⊗ y past z, and uses
   the inverse associator throughout. Both follow the nLab orientation; the
   coherence consequence on triple tensors is the Yang-Baxter equation proved
   below. Adding the further axiom beta ∘ beta = id yields a symmetric
   monoidal category (see Structure/Monoidal/Symmetric.v).

   Only the braiding's naturality is asked for: the two hexagons are equations
   between fixed composites and so need no separate respectfulness. *)

(* Where the braiding comes from, and what it is for

   nLab:  https://ncatlab.org/nlab/show/Yang-Baxter+equation
   nLab:  https://ncatlab.org/nlab/show/periodic+table
   Paper: Joyal, Street, "Braided tensor categories", Advances in
          Mathematics 102, 1993

   Braided monoidal categories were introduced by Joyal and Street in a
   pair of Macquarie Mathematics Reports (85-0067, 1985; 86-0081, 1986),
   revised as the paper above, and were arrived at independently by
   Lawrence Breen ("Une lettre à P. Deligne au sujet des 2-catégories
   tressées", 1988).  The name points to Artin's braid groups (Artin,
   "Theorie der Zöpfe", Abh. Math. Sem. Univ. Hamburg 4, 1925; "Theory of
   Braids", Annals of Mathematics 48, 1947): on n-fold tensor powers the
   coherence isomorphisms of a braided category act through the braid
   group B_n rather than the symmetric group S_n, and this is precisely
   what separates the notion from symmetry.  Coherence is accordingly
   conditional, unlike Mac Lane's for plain monoidal categories: a diagram
   built from associators, unitors and braidings commutes whenever both
   sides have the same underlying braid, and in the free braided monoidal
   category only then (Joyal-Street 1993).  Distinct braids can therefore
   name genuinely distinct morphisms — the double braiding
   [braid] ∘ [braid] need not be the identity, and requiring it to be so
   collapses B_n back onto S_n.

   The definition answers a precise question: what commutativity remains
   when the swap is an isomorphism that remembers how the swap was
   performed?  The hexagons are exactly compatibility with the associator
   — braiding one object past a whole tensor product agrees with braiding
   it past the two factors in adjacent steps — and from them together
   with [braid_natural] alone follows [Yang_Baxter_equation], the
   categorical form of Artin's braid relation on adjacent generators and
   of the third Reidemeister move.  That equation predates the
   categorical notion, arising twice in physics: in Yang's
   one-dimensional many-body problem (Physical Review Letters 19, 1967)
   and as the star-triangle relation of Baxter's eight-vertex model
   (Annals of Physics 70, 1972); the joint name is due to Faddeev in the
   late 1970s.  In the periodic table of k-tuply monoidal n-categories
   (Baez, Dolan, "Higher-dimensional algebra and topological quantum
   field theory", 1995), braided monoidal sits at k = 2, n = 1: two
   compatible monoidal structures on one category, merged by the
   Eckmann-Hilton argument into a single tensor carrying a braiding,
   while a third structure already stabilizes at symmetric.  Braided
   monoidal is thus the maximally noncommutative commutativity — the last
   stop before stabilization.

   The utility runs through algebra, topology and physics.  Modules over
   a quasitriangular Hopf algebra — Drinfeld's quantum groups (Drinfeld,
   "Quantum Groups", Proceedings of the ICM, Berkeley 1986) — form a
   braided category whose braiding is induced by the universal R-matrix;
   ribbon categories built on braidings yield the functorial
   Reshetikhin-Turaev invariants of links and 3-manifolds, the Jones
   polynomial among them (Shum, "Tortile tensor categories", J. Pure
   Appl. Algebra 93, 1994; Reshetikhin, Turaev, "Invariants of
   3-manifolds via link polynomials and quantum groups", Inventiones
   Mathematicae 103, 1991).  In topological quantum computation the
   exchange statistics of anyons are braid-group representations, so a
   braided fusion category models the physics — tensor as fusion, [braid]
   as particle exchange — and quantum gates are braids (Kitaev,
   "Fault-tolerant quantum computation by anyons", Annals of Physics 303,
   2003; Freedman, Kitaev, Larsen, Wang, "Topological quantum
   computation", Bulletin of the AMS 40, 2003).

   Within the library the reading is concrete.  The free PROP realizes
   the braiding as the literal block crossing [T_braid] of one wire
   bundle past another (Construction/PROP/Braided.v); the Drinfeld centre
   produces braided structure from any monoidal category
   ([Drinfeld_Braided] in Structure/Monoidal/Drinfeld.v); the cartesian
   swap gives the degenerate case ([CC_BraidedMonoidal] in
   Structure/Monoidal/Internal/Product.v); Structure/Monoidal/Symmetric.v
   adds the involution [braid_invol], under which either hexagon yields
   the other; Structure/Monoidal/Balanced.v adds a twist compatible with
   the double braiding — given duals that respect the twist, the ribbon
   notion behind Shum's theorem; for a monoidal functor, being braided is
   a property rather than structure ([BraidedMonoidalFunctor] in
   Functor/Structure/Monoidal/Braided.v); and Structure/Monoidal/Closed.v
   derives [flip] for internal homs from [BraidedMonoidal] alone, no
   symmetry required. *)

Class BraidedMonoidal := {
  braided_is_monoidal : @Monoidal C;

  (* The braiding beta : x ⊗ y ≅ y ⊗ x, natural in both arguments. *)
  braid {x y} : x ⨂ y ~> y ⨂ x;
  braid_natural : natural (@braid);

  (* First hexagon: braiding x past the tensor product y ⊗ z. *)
  hexagon_identity {x y z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
    id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id;

  (* Second hexagon: braiding the tensor product x ⊗ y past z. *)
  hexagon_identity_sym {x y z} :
    tensor_assoc⁻¹ ∘ braid ∘ tensor_assoc⁻¹
      << x ⨂ (y ⨂ z) ~~> (z ⨂ x) ⨂ y >>
    braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ braid;
}.
#[export] Existing Instance braided_is_monoidal.

Coercion braided_is_monoidal : BraidedMonoidal >-> Monoidal.

Context `{BraidedMonoidal}.

(* The hexagons imply the Yang-Baxter equation on a triple tensor product:
   the two ways of fully reversing a ⊗ b ⊗ c by adjacent braidings agree. *)
Theorem Yang_Baxter_equation {a b c : C} :
  braid ⨂ id[a] ∘ tensor_assoc⁻¹
    ∘ id[b] ⨂ braid ∘ tensor_assoc
    ∘ braid ⨂ id[c] ∘ tensor_assoc⁻¹
    ≈ tensor_assoc⁻¹ ∘ id[c] ⨂ braid
        ∘ tensor_assoc ∘ braid ⨂ id[b]
        ∘ tensor_assoc⁻¹ ∘ id[a] ⨂ braid.
Proof.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite iso_to_from, id_right.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite (@comp_assoc _ _ _ _ _ _ tensor_assoc⁻¹).
  rewrite iso_to_from, id_left.
  spose (braid_natural a _ id _ _ (@braid _ b c)) as X.
  rewrite bimap_id_id in X.
  rewrite id_right in X.
  rewrite X.
  rewrite bimap_id_id.
  rewrite id_right.
  reflexivity.
Qed.

End BraidedMonoidal.
