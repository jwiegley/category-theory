Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Adjunction.GAFT.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Adjoints.

Generalizable All Variables.

(** * The General Adjoint Functor Theorem, run at [Sets] *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   [GAFT] (Adjunction/GAFT.v:241) has the shape, its named hypotheses
   rewritten here as arrows,

     GAFT (U : C ⟶ D) : @Complete C
                        → @PreservesImageLimit C D U
                        → (∀ d : D, SolutionSet U d)
                        → { F : D ⟶ C & F ⊣ U }

   and before this file no closed constant of the library applied it.
   [Adjunction/SAFT.v:278] does call it, but [SAFT] is itself never applied;
   [Adjunction/GAFT/Examples.v] exercises the universal-arrow half
   [GAFT_from_initials], which consumes comma-category initial objects
   directly and so meets none of the three premises above.  This file applies
   [GAFT] itself, at a concrete functor, with each premise supplied by an
   in-tree construction.

   THIS IS A TOY, AND SAYING SO IS THE POINT

   The functor is [Id : Sets ⟶ Sets], so the left adjoint the theorem returns
   is naturally isomorphic to [Id] again -- [GAFT_at_Sets_Id_is_Id] proves
   that rather than leaving it to be taken on trust.  Nothing about the
   CONCLUSION is news.  What is new is that the three premises are
   simultaneously met by objects this library builds, so [GAFT] is now a
   theorem the library has run and not only a theorem it has proved:

     [@Complete Sets]                     [Sets_Complete]
                                          (Instance/Sets/Complete.v), the
                                          tree's first [Complete] instance;

     [@PreservesImageLimit Sets Sets Id]  [right_adjoint_PreservesImageLimit]
                                          (Construction/Comma/Limit.v:264) at
                                          [adj_id] (Instance/Adjoints.v:42);

     [∀ d, SolutionSet Id d]              [Sets_Id_SolutionSet] below: the
                                          one-member family at [d] itself,
                                          with [sol_arr := id].

   Of the three, only [Complete] wanted an inhabitant.  The second has had a
   general in-tree supply all along -- [right_adjoint_PreservesImageLimit]
   discharges it for EVERY right adjoint, and [Instance/Adjoints.v]'s [adj_id]
   and [Adjunction/Diagonal/Product.v]'s [Δ ⊣ ×] are concrete right adjoints
   to feed it -- and the third is routine at any [d] once [U] is [Id].
   docs/INHABITATION.md records the resulting row.

   WHY [Id], AND WHAT A REAL APPLICATION WOULD NEED

   The solution set is the hard input: it is where the smallness condition of
   Freyd's proof does its work (Mac Lane CWM V.6).  At [U := Id] it collapses
   to the identity arrow, which is why this application is cheap.  A
   non-degenerate one would want a [U] whose comma categories carry small
   weakly initial families -- the forgetful functor of an algebraic category
   is the standard choice.  The library has no such forgetful functor into
   [Sets] with its solution set constructed, and none is attempted here.

   THE UNIVERSE INSTANCE, DISCLOSED

   [GAFT] is a [Qed]-opaque [Theorem], so its universe context is frozen at
   whatever its own proof needed, and that context pins the hom and proof
   universes of both categories to [Set] ([About GAFT], re-wrapped, the
   hypotheses elided):

     GAFT@{u u0 u1 u2 u3 u4} :
       ∀ {C : Category@{u1 Set Set}} {D : Category@{u2 Set Set}}
         (U : C ⟶ D), ...

   Applying it therefore instantiates [Sets@{o so}] at [o := Set]:

     GAFT_at_Sets_Id@{u u0 u1} :
       ∃ F : Sets@{Set u} ⟶ Sets@{Set u}, F ⊣ Id[Sets@{Set u}]

   [Sets@{Set u}] is the category of setoids whose carriers, and whose
   equivalences, live in [Set].  It is a genuine and inhabited instance --
   [Sets_bool] of Instance/Sets/Products.v is one of its objects -- but it is
   ONE instance of the polymorphic [Sets@{u0 u}], the smallest, where
   [Sets_Complete] and [Sets_HasIndexedProducts] are stated polymorphically
   and hold at every instantiation.  So the application demonstrates [GAFT] at
   a concrete category, not at [Sets] in the generality in which the rest of
   this development speaks of it.  The restriction comes from [GAFT], predates
   this file, and is not lifted by it.

   A BY-PRODUCT: EQUALIZERS IN [Sets]

   [Complete_HasEqualizers] (Adjunction/GAFT.v:193) turns any [Complete]
   category into a [HasEqualizers] one.  At [Sets_Complete] it yields
   [Sets_HasEqualizers], the tree's only inhabitant of that class.  It is left
   a [Definition] rather than an [Instance]: no in-tree consumer resolves
   [HasEqualizers] by typeclass search -- [Theory/WeaklyInitial.v:94] takes it
   as an explicit argument and [GAFT] passes [Complete_HasEqualizers] by hand
   -- so registering it would add resolution surface with no consumer.  Unlike
   [GAFT_at_Sets_Id] it carries no [Set] pinning; it stands at the same
   [Sets@{u0 u}] as [Sets_Complete].

   STATUS: axiom-free.  [Print Assumptions] reports "Closed under the global
   context" for every constant below; the Makefile's [print-assumptions]
   target audits [GAFT_at_Sets_Id] and [Sets_HasEqualizers]. *)

(** ** The three premises *)

(* [Id] is a right adjoint -- to itself, by [adj_id] -- so the general bridge
   of Construction/Comma/Limit.v supplies its cone-level preservation. *)
Definition Sets_Id_PreservesImageLimit : @PreservesImageLimit Sets Sets Id :=
  right_adjoint_PreservesImageLimit (@adj_id Sets).

(* A solution set at [d] for [Id]: the one-member family whose single object
   is [d] and whose single arrow is [id[d]].  Every [h : d ~> c] factors as
   [fmap[Id] h ∘ id ≈ h], which is [id_right].

   [Build_SolutionSet] is applied with all four of its parameters written out.
   That is not stylistic: it was forced by a measured break.  A record literal
   [{| sol_arr := fun _ => id ; ... |}] elaborates its fields before the
   ascribed type has fixed [U] and [D], so [id] is elaborated against
   [?d ~{?D}~> fobj[?U] d].  Rocq 9.1 resolves that from the ascription; Coq
   8.19 and 8.20 do not, and report "The term id{?Category} ... is expected to
   have type ?d ~{?D}~> fobj[?U] d" (observed on both, through
   [nix build .#category-theory_8_19 .#category-theory_8_20]).  Naming the
   parameters removes the metavariables.  Closing the covering equation with
   [exact (id_right h)] rather than [apply id_right] is defensive against the
   same class of problem and was not separately measured: [exact] settles
   [fmap[Id] h ∘ id ≈ h] by CONVERSION, [fmap[Id]] beta-iota-reducing to the
   identity, instead of leaving that reduction to unification. *)
Definition Sets_Id_SolutionSet (d : Sets) : SolutionSet (@Id Sets) d.
Proof.
  unshelve refine (@Build_SolutionSet Sets Sets (@Id Sets) d
                     poly_unit
                     (fun _ : poly_unit => d)
                     (fun _ : poly_unit => @id Sets d)
                     _).
  intros c h.
  exists ttt.
  exists h.
  exact (id_right h).
Defined.

(** ** The application *)

(* [GAFT] at [Id : Sets ⟶ Sets], all three premises discharged by in-tree
   constructions.  See the header for the [Set] pinning this inherits from
   [GAFT]'s frozen universe context. *)
Definition GAFT_at_Sets_Id : { F : Sets ⟶ Sets & F ⊣ Id } :=
  GAFT (@Id Sets) Sets_Complete
    Sets_Id_PreservesImageLimit Sets_Id_SolutionSet.

(* The produced left adjoint is naturally isomorphic to [Id], as it must be:
   left adjoints to a fixed functor are unique up to natural isomorphism
   ([left_adjoint_iso], Theory/Adjunction.v:404), and [adj_id] exhibits [Id]
   as a second left adjoint to [Id].  This is what makes the "toy" label
   above a proved statement rather than an editorial one. *)
Definition GAFT_at_Sets_Id_is_Id : projT1 GAFT_at_Sets_Id ≈ @Id Sets :=
  left_adjoint_iso (@Id Sets) (projT1 GAFT_at_Sets_Id) (@Id Sets)
    (projT2 GAFT_at_Sets_Id) (@adj_id Sets).

(** ** By-product: equalizers in [Sets] *)

(* The first [HasEqualizers] inhabitant in the library, read off completeness
   by [Complete_HasEqualizers].  Kept a [Definition]; see the header. *)
Definition Sets_HasEqualizers : HasEqualizers Sets :=
  Complete_HasEqualizers Sets_Complete.
