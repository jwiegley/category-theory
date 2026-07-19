Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.

Generalizable All Variables.

(** * Complete and cocomplete categories *)

(* nLab:      https://ncatlab.org/nlab/show/complete+category
   Wikipedia: https://en.wikipedia.org/wiki/Complete_category

   Wikipedia: "a category C is complete if every diagram F : J → C (where J is
   small) has a limit in C." Dually, C is cocomplete if every such diagram has
   a colimit. nLab: a category "has all small limits" when "every small diagram
   F : D → C where D is a small category has a limit in C." In library notation
   the completeness condition reads:

       ∀ (D : Category) (F : D ⟶ C), Limit F,

   i.e. there is a [Limit] (a terminal/universal cone, see [Structure/Limit.v])
   for every diagram F of shape D in C. Cocompleteness is the exact dual,
   asking for a [Colimit] of every diagram; since [Colimit F := Limit (F^op)],
   C is cocomplete iff C^op is complete, matching the duality recorded by both
   sources.

   On the index class: both sources restrict J (here D) to be *small*. Wikipedia
   notes that demanding limits for *all* (proper-class-sized) diagrams "is too
   strong to be practically relevant" — such a C would be forced to be thin. The
   definitions below quantify over [∀ (D : Category)] without an explicit
   smallness hypothesis; the size discipline is instead carried implicitly by
   the library's universe polymorphism. When [Complete]/[Cocomplete] are
   instantiated, the universe levels of D become constrained relative to those
   of C, which is the universe-polymorphic stand-in for "D small relative to C".
   So these state "has a limit for every (suitably small) diagram" rather than
   the inconsistent all-diagrams reading. The morphism-level equality is the
   setoid [≈] of C, supplied inside [Limit]/[Cone]; it does not appear here. *)

(* Completeness as a working hypothesis

   nLab:  https://ncatlab.org/nlab/show/complete+small+category
   nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Paper: Hyland, "A small complete category", Annals of Pure and Applied
          Logic 40, 1988

   [Complete] is the blanket limit hypothesis: rather than checking, per
   construction, that this pullback or that wide product exists, a
   development records once that every (small) diagram has a limit and
   then draws arbitrary limit shapes on demand.  The hypothesis is
   checkable because limits reduce to two constructions: a category with
   all small products and equalizers of parallel pairs has all small
   limits, each limit arising as an equalizer between two products
   (Mac Lane, Categories for the Working Mathematician, 1971, Theorem
   V.2.1; Riehl, Category Theory in Context, 2016, Theorem 3.4.12).  This
   is how Set, Top, Grp, Ab, and module categories are shown complete,
   and the property propagates: presheaf categories inherit all small
   limits and colimits objectwise from the category of sets (nLab,
   "category of presheaves"), and monadic functors create limits, so
   algebras for a monad on a complete category are again complete (nLab,
   "complete category").  The products half of the reduction lives
   in-tree as [iprod] in Structure/Limit/Product.v, limits of discrete
   diagrams.

   The smallness discipline the header describes is not decoration.
   Freyd proved that a category with products of families as large as its
   own morphism set is a preorder (Abelian Categories, Harper & Row,
   1964, exercise D of ch. 3): were some hom-set to hold two distinct
   arrows, the product indexed by all morphisms would yield a hom-set of
   cardinality at least 2^|Mor|, exceeding |Mor| by Cantor's theorem.  It
   follows that complete small categories are preorders — up to
   equivalence, complete lattices (Adámek–Herrlich–Strecker, Abstract and
   Concrete Categories, Theorem 12.7; Shulman, "Set theory for category
   theory", arXiv:0810.1279, Theorem 2.1).  In this library the same
   ledger is kept by universes: the header of Adjunction/SAFT.v records a
   concrete instance, noting that instantiating [Complete] forces the
   diagram category's hom universe to coincide with that of C.

   Completeness is one of the engine hypotheses of the adjoint functor
   theorems, which originate in the same exercise section of Freyd's book
   (nLab, "adjoint functor theorem"; the solution-set condition is called
   pre-adjointness in Freyd–Scedrov, Categories, Allegories, 1990).  GAFT
   concludes a left adjoint from a limit-preserving functor out of a
   complete, locally small category with a solution set; SAFT trades
   the solution set for well-poweredness and a cogenerating set.  The
   in-tree consumers apply [Complete] exactly as stated: Adjunction/GAFT.v
   derives binary equalizers by applying the hypothesis at the walking
   parallel pair ([Complete_HasEqualizers]), Construction/Comma/Limit.v
   lifts completeness along the comma construction ([Comma_Complete]),
   and Adjunction/SAFT.v builds its cogenerator products and powers
   ([cogen_prod], [cogen_power]) from the same source.  Yet
   Theory/WeaklyInitial.v deliberately takes its two products as explicit
   hypotheses rather than harvesting them from a [Complete] instance, so
   that the size of the index — and with it the universe constraints —
   remains in the caller's hands.

   Both definitions below are Type-valued data, not mere propositions: an
   inhabitant of [Complete] is a function assigning to every diagram a
   chosen limit, a limit oracle applied downstream like any other
   function.  Dually, Theory/Adamek/Corollaries.v applies [Cocomplete] at
   the ordinal ω and the chain of an endofunctor to obtain the colimit
   that Adámek's initial-algebra construction consumes
   ([adamek_cocomplete]).  Finally, Freyd's collapse is essentially
   classical.  Hyland exhibited, inside the effective topos, a complete
   small category that is not a preorder, built from partial equivalence
   relations (Hyland, "A small complete category", 1988), so the thinness
   theorem cannot be proved constructively.  The stake is the semantics
   of impredicative polymorphism: interpreting ∀X.T as a product over all
   objects of a small complete subcategory of Set is classically
   impossible (Reynolds, "Polymorphism is not set-theoretic", 1984), yet
   realizably consistent — the foundation of the PER models of System F.
   A complete small category is, in this reading, a type of all types
   closed under products over itself. *)

(* C is complete: every diagram F : D ⟶ C has a limit (terminal cone) in C. *)
Definition Complete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Limit F.

(* C is cocomplete: every diagram F : D ⟶ C has a colimit in C — the dual of
   completeness, equivalently completeness of C^op. *)
Definition Cocomplete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Colimit F.
