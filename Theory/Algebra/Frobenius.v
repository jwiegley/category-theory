Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.

Generalizable All Variables.

(** * Frobenius algebras in a monoidal category

    nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
    Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra

    A Frobenius algebra on [X] is a monoid [(X, mu, eta)] and a comonoid
    [(X, delta, epsilon)] on the same object, satisfying the Frobenius
    compatibility law:

        (id ⨂ mu) ∘ (delta ⨂ id) ≈ delta ∘ mu ≈ (mu ⨂ id) ∘ (id ⨂ delta)

    (up to suitable insertions of the tensor associator).  Per nLab, the two
    equalities collapse into the single condition equating the outer
    composites, [(id ⨂ mu) ∘ (delta ⨂ id) ≈ (mu ⨂ id) ∘ (id ⨂ delta)], with
    the middle [delta ∘ mu] recovered using (co)unitality; together they
    encode that [delta] is a bimodule map.

    To keep the statement first-order in the tensor associator (rather than
    awkward two-sided compositions) we follow the standard nLab convention
    and rephrase as

        (mu ⨂ id) ∘ α⁻¹ ∘ (id ⨂ delta) ≈ delta ∘ mu

    and dually

        (id ⨂ mu) ∘ α ∘ (delta ⨂ id) ≈ delta ∘ mu.

    Together these two axioms recover the standard double Frobenius equation. *)

(* Where Frobenius algebras come from, and what they are for

   Book:  Kock, "Frobenius Algebras and 2D Topological Quantum Field
          Theories", LMS Student Texts 59, CUP 2003;
          https://mat.uab.cat/~kock/TQFT.html
   Paper: Carboni, Walters, "Cartesian bicategories I", JPAA 49, 1987
   Paper: Lack, "Composing PROPs", Theory Appl. Categ. 13(9), 2004

   The classical objects predate the categorical definition by most of a
   century.  Frobenius studied finite-dimensional hypercomplex algebras in
   "Theorie der hyperkomplexen Größen" (1903); systematic study — and the
   name — came with Brauer and Nesbitt ("On the regular representations of
   algebras", Proc. Nat. Acad. Sci. USA 1937), and Nakayama opened the
   duality theory ("On Frobeniusean algebras I, II", Ann. of Math. 1939,
   1941).  Classically a Frobenius algebra is a finite-dimensional unital
   associative algebra with a nondegenerate bilinear pairing that
   associates with the multiplication; group algebras of finite groups
   are standard examples.  The diagrammatic form recorded in this file
   is younger.  Per Kock's account, Lawvere knew the categorical
   characterization by 1967 and published an equational version in
   "Ordinal sums and equational doctrines" (1969), yet the first explicit
   appearance of the Frobenius equation in print is the "discreteness
   axiom" of Carboni and Walters (1987), recognized only later as
   Lawvere's condition.  Over vector spaces the two definitions agree: a
   counit for which [epsilon ∘ mu] is a nondegenerate pairing identifies
   the algebra with its linear dual and thereby forces finite dimension
   (per the nLab page cited in the header above).

   The law is one of the two canonical, inequivalent ways a monoid and a
   comonoid on the same object can interact.  The bialgebra law makes
   [delta] a homomorphism of monoids; the Frobenius law instead makes the
   pairing [epsilon ∘ mu] and the copairing [delta ∘ eta] exhibit [X] as
   its own dual.  Composing the PROPs for commutative monoids and
   cocommutative comonoids by the two available distributive laws yields
   Cospan(FinSet) on the Frobenius side and Span(FinSet) on the bialgebra
   side (Lack 2004).  The self-duality reading is realized in-tree:
   Structure/Monoidal/CompactClosed.v equips every object of a hypergraph
   category with itself as dual, and the snake identities there follow
   from the Frobenius law alone, without appeal to specialness.

   Diagrammatically the law is a principle of topological invariance: both
   sides of the Frobenius equation are the same surface up to deformation.
   Pushed to its conclusion this becomes the classification of
   two-dimensional topological quantum field theories by commutative
   Frobenius algebras, stated as a folk theorem in Dijkgraaf's thesis ("A
   geometrical approach to two-dimensional Conformal Field Theory",
   Utrecht 1989) and proved by Abrams ("Two-dimensional topological
   quantum field theories and Frobenius algebras", J. Knot Theory
   Ramifications 1996); Kock's book is the standard treatment, and the
   commutative case where the correspondence lives is
   Theory/Algebra/CommutativeFrobenius.v.

   The computational readings are genuine.  In categorical quantum
   mechanics a commutative dagger-Frobenius monoid in finite-dimensional
   Hilbert spaces is exactly an orthogonal basis, orthonormal exactly when
   special: the comultiplication copies basis vectors and the counit
   deletes them, axiomatizing classical — copyable, deletable — data
   inside a quantum universe (Coecke, Pavlovic, Vicary, "A new description
   of orthogonal bases", arXiv:0810.0812, 2008).  In network theory
   Frobenius structure is the algebra of interconnection: Cospan(FinSet)
   is the PROP for special commutative Frobenius monoids (Lack 2004;
   Construction/Cospan/SCFA.v builds the canonical instance on cospans),
   corelations the PROP for extraspecial ones (Coya, Fong, "Corelations
   are the prop for extraspecial commutative Frobenius monoids", TAC 32,
   2017), and a hypergraph category carries the structure on every object
   (Structure/Monoidal/Hypergraph.v).  Both readings meet in the spider
   calculus: in the special commutative case a connected composite of
   [mu], [eta], [delta] and [epsilon] collapses to a canonical spider, the
   fusion rule of the ZX-calculus (Coecke, Duncan, "Interacting Quantum
   Observables", New J. Phys. 13, 2011; see Instance/ZX.v), and
   Structure/Monoidal/Hypergraph/Spider.v restates [frob_law_left] and
   [frob_law_right] as [spider_frobenius] and [spider_frobenius_sym].

   Downstream, Theory/Algebra/CommutativeFrobenius.v adds compatibility
   with the braiding and Theory/Algebra/SpecialCommutativeFrobenius.v the
   special law [mu_delta_id].  A no-go theorem delimits the whole subject:
   Structure/Monoidal/Collapse.v proves that a Frobenius object in a
   semicartesian monoidal category is isomorphic to the unit, so the
   notion trivializes over a cartesian tensor and carries content only
   where the tensor is resource-sensitive. *)

Section Frobenius.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Frobenius (X : C) : Type := {
  frob_monoid   : Monoid X;     (* the multiplication [mu] and unit [eta] *)
  frob_comonoid : Comonoid X;   (* the comultiplication [delta] and counit [epsilon] *)

  (* Frobenius law, left form: [(mu ⨂ id) ∘ α⁻¹ ∘ (id ⨂ delta) ≈ delta ∘ mu]. *)
  frob_law_left :
    bimap (@mu _ _ _ frob_monoid) id[X]
      ∘ from (@tensor_assoc C M X X X)
      ∘ bimap id[X] (@delta _ _ _ frob_comonoid)
    ≈ (@delta _ _ _ frob_comonoid) ∘ (@mu _ _ _ frob_monoid);

  (* Frobenius law, right form: [(id ⨂ mu) ∘ α ∘ (delta ⨂ id) ≈ delta ∘ mu]. *)
  frob_law_right :
    bimap id[X] (@mu _ _ _ frob_monoid)
      ∘ to (@tensor_assoc C M X X X)
      ∘ bimap (@delta _ _ _ frob_comonoid) id[X]
    ≈ (@delta _ _ _ frob_comonoid) ∘ (@mu _ _ _ frob_monoid)
}.
#[export] Existing Instance frob_monoid.
#[export] Existing Instance frob_comonoid.

Coercion frob_monoid   : Frobenius >-> Monoid.
Coercion frob_comonoid : Frobenius >-> Comonoid.

End Frobenius.

Arguments frob_monoid   {C M X _}.
Arguments frob_comonoid {C M X _}.

(** ** Flat projections

    Convenience aliases paralleling [scfa_mu] / [scfa_eta] /
    [scfa_delta] / [scfa_epsilon] (in
    [Theory/Algebra/SpecialCommutativeFrobenius.v]) and [cfrob_*]
    (in [Theory/Algebra/CommutativeFrobenius.v]).  Project a
    [Frobenius X] to its underlying [mu] / [eta] / [delta] /
    [epsilon] without going through [frob_monoid] / [frob_comonoid]
    one-by-one.

    The instance arguments are explicit so downstream code can
    write e.g. [frob_mu F] unambiguously. *)

Section FrobeniusProjections.

Context {C : Category}.
Context `{M : @Monoidal C}.

Definition frob_mu {X : C} (F : Frobenius X) : (X ⨂ X)%object ~> X :=
  @mu _ _ _ (frob_monoid (X := X)).

Definition frob_eta {X : C} (F : Frobenius X) : @I _ _ ~> X :=
  @eta _ _ _ (frob_monoid (X := X)).

Definition frob_delta {X : C} (F : Frobenius X) : X ~> (X ⨂ X)%object :=
  @delta _ _ _ (frob_comonoid (X := X)).

Definition frob_epsilon {X : C} (F : Frobenius X) : X ~> @I _ _ :=
  @epsilon _ _ _ (frob_comonoid (X := X)).

End FrobeniusProjections.

Arguments frob_mu      {C M X} F.
Arguments frob_eta     {C M X} F.
Arguments frob_delta   {C M X} F.
Arguments frob_epsilon {C M X} F.
