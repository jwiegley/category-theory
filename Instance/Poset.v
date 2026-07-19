Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Proset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The category of a partially-ordered set. *)

(* nLab: https://ncatlab.org/nlab/show/poset
   Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

   A partially-ordered set forms a category directly from its preorder,
   since a poset is precisely a preorder (a [Proset]) satisfying the extra
   antisymmetry condition: x ≤ y ≤ x implies x = y. Antisymmetry adds nothing
   to the underlying [Category] construction (the hom-sets are unchanged); it
   only makes the resulting thin category skeletal, so that isomorphic objects
   are equal. nLab characterizes a poset as exactly "a skeletal thin category",
   equivalently "a skeletal (0,1)-category". (See also [Pos], the category of
   posets, whose objects are posets and whose morphisms are monotone maps.)

   Wikipedia: "Every poset (and every preorder) may be considered as a category
   in which every hom-set has at most one element. More explicitly, let
   hom(x, y) = {(x, y)} if x ≤ y (and otherwise the empty set) and
   (y, z) ∘ (x, y) = (x, z). Such categories are sometimes called thin.

   Posets are equivalent to one another if and only if they are isomorphic. In
   a poset, the smallest element, if it exists, is an initial object, and the
   largest element, if it exists, is a terminal object. Also, every preordered
   set is equivalent to a poset. Finally, every subcategory of a poset is
   isomorphism-closed." *)

(* Order theory as category theory: the collapse dictionary

   nLab:  https://ncatlab.org/nlab/show/Galois+connection
   Paper: Ore, "Galois connexions", Transactions of the AMS 55, 1944
   Paper: Lawvere, "Metric spaces, generalized logic, and closed
          categories", Rendiconti del Seminario Matematico e Fisico di
          Milano 43, 1973; Reprints in TAC 1, 2002

   In a thin category all parallel morphisms are equal, so every diagram
   commutes and every coherence condition holds vacuously.  Each
   categorical concept therefore collapses to its order-theoretic
   shadow, and [Poset] installs the resulting dictionary: an adjunction
   between posets is exactly a monotone Galois connection
   (Theory/Adjunction.v); a monad is a closure operator, the unit giving
   extensivity and the multiplication idempotency (Theory/Monad.v); a
   product is a meet, and more generally the limit over a subset is its
   greatest lower bound (nLab, "meet"); a coproduct is a join
   (Structure/Cocartesian.v).  Theorems proved for categories thereby
   specialize to classical order theory, and intuitions trained on
   orders lift to categories with proof relevance switched on.

   The dictionary predates category theory.  The name Galois connection
   honours the inclusion-reversing correspondence between intermediate
   fields and subgroups in the fundamental theorem of Galois theory; the
   abstract notion, in its antitone form, is due to Ore (1944), after
   Birkhoff's Lattice Theory (AMS Colloquium Publications 25, 1940) had
   treated the power-set polarities induced by a binary relation; the
   modern survey is Erné, Koslowski, Melton, Strecker, "A primer on
   Galois connections", Annals of the New York Academy of Sciences 704,
   1993.  Closure operators go back to E. H. Moore's Introduction to a
   Form of General Analysis (1910), and around 1930 Tarski abstracted
   logical deduction to a finitary closure operator on sets of sentences
   — the consequence operator, in this dictionary a monad on the poset
   of theories (Wikipedia, "Closure operator").  Lawvere then made the
   dictionary itself the object of study: "Adjointness in Foundations"
   (Dialectica 23, 1969) exhibits the quantifiers as the adjoint triple
   ∃ ⊣ substitution ⊣ ∀, and the 1973 paper cited above reads a poset as
   a skeletal category enriched over the truth values — realized in-tree
   by [Enriched_Two_preorder] and [EnrichedFunctor_Two_monotone] in
   Construction/Enriched/Two.v, over the walking arrow of Instance/Two.v
   — while the same recipe over ([0, ∞], ≥, +) makes a metric space a
   category whose composition law is the triangle inequality (nLab,
   "Lawvere metric space").

   Thinness also marks a size boundary in the adjoint functor theorems.
   Between small preorders, a functor that preserves all small meets
   from a complete domain has a left adjoint outright, the candidate
   value being a meet over everything (nLab, "adjoint functor theorem").
   For genuine categories that computation is out of reach: by Freyd's
   observation, any complete small category is a preorder, which is
   exactly why the general theorem in Adjunction/GAFT.v must carry a
   [SolutionSet] hypothesis.

   The working uses run through the same corner.  Abstract
   interpretation (Cousot and Cousot, "Abstract Interpretation: A
   Unified Lattice Model for Static Analysis of Programs by Construction
   or Approximation of Fixpoints", POPL 1977) takes an abstraction to be
   a Galois connection between concrete and abstract domains and reads a
   loop as a Knaster–Tarski least fixed point in a complete lattice;
   formal concept analysis organizes object–attribute data by the
   concept lattice of a power-set Galois connection (Ganter and Wille,
   1999); and the opening chapter of Fong and Spivak's Seven Sketches
   in Compositionality (2018) — "Generative Effects: Orders and Galois
   Connections" in its 2019 Cambridge edition — takes a generative
   effect to be an observation that does not preserve joins, detected
   by a Galois connection.  The computational reading beneath all of
   these is proof irrelevance: under the [Proset] construction a
   hom-set is the mere proposition x ≤ y — identity is reflexivity,
   composition is transitivity, and the trivial setoid on each hom-set
   declares all proofs of an entailment equal — so an abstract domain
   is a poset precisely because an analyzer needs only that an
   approximation holds, never a witness.  Instance/Props.v is the
   logical instance, propositions ordered by entailment;
   Instance/Rel.v sits one level up, each hom-set itself ordered by
   inclusion — locally posetal rather than posetal. *)

Lemma eq_equiv {C : Type} : @Equivalence C eq.
Proof.
  split; auto. intros x y z; apply eq_trans.
Qed.

Definition Poset {C : Type} `{R : relation C}
           `(P : PreOrder C R) `{@Antisymmetric C eq eq_equiv R} : Category := Proset P.

Section Examples.
Definition LessThanEqualTo_Category : Category :=
  @Poset nat PeanoNat.Nat.le PeanoNat.Nat.le_preorder
    (partial_order_antisym PeanoNat.Nat.le_partialorder).
End Examples.
