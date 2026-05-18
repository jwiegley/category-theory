Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(** * Hypergraph structure on [CospanCat C]

    Mathematical content (cf. Carboni–Walters, Fong–Spivak):

    Given a category [C] with finite colimits (coproducts + pushouts), the
    cospan category [CospanCat C] is a symmetric monoidal category with
    tensor given by the coproduct of [C]:

      X ⨂ Y   :=  X + Y               (in C)
      I       :=  0                    (initial object of C)
      f ⨂ g  :=  the obvious cospan on coproducts

    Each object [X] carries a canonical special commutative Frobenius algebra,
    built from the cocartesian structure of [C]:

      μ_X     : X + X ~> X            given by codiagonal [id ▽ id]
      η_X     : 0 ~> X                given by [zero]
      δ_X     : X ~> X + X            but read backwards as a cospan,
                                       so the cospan is [X --id--> X <--id-- X+X]
      ε_X     : X ~> 0                similarly read backwards as a cospan

    Then [(μ_X, η_X, δ_X, ε_X)] satisfies the SCFA axioms, and the canonical
    coherence  [SCFA(X + Y) ≈ canonical SCFA(X) SCFA(Y)]  follows from the
    universal property of coproducts.

    --------------------------------------------------------------------

    Status: in V1 we record only the categorical infrastructure
    ([CospanCat], [Hypergraph], algebras, [Pushout]).  Showing
    [CospanCat C] is symmetric monoidal requires building a [Monoidal]
    instance on [CospanCat C] (tensor functor + unitors + associator) in
    the cospan setoid, which is a moderate effort but mathematically
    straightforward.  Equipping each object with an SCFA is then a
    bookkeeping exercise.

    For downstream consumers in V1, the recommended pattern is:
    instantiate [Hypergraph] directly for the concrete category of interest
    (typically [Cospan(Sets)] in the rewriting/automata setting), supplying
    the SCFA witnesses by hand using the cospan algebraic structure
    described above.  V2 will deliver a generic
    [Cospan_Hypergraph : @Hypergraph (CospanCat C) _] for any [C] with the
    appropriate finite-colimit structure.

    See [docs/HYPERGRAPH_MIGRATION.md] for the recommended migration
    workflow. *)

(* TODO(V2): SymmetricMonoidal (CospanCat C) when C has finite colimits. *)

(* TODO(V2): Hypergraph (CospanCat C) when C has finite colimits. *)
