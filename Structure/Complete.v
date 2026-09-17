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
   limits (Instance/Fun/Limit.v's [Presheaf_Complete]) and colimits (nLab,
   "category of presheaves") from Sets, and monadic functors create limits, so
   algebras for a monad on a complete category are again complete (nLab,
   "complete category").  The reduction is Structure/Limit/FromProducts.v's
   [Complete_from_products_equalizers] over [HasIndexedProducts] and
   [HasEqualizers], each limit the equalizer [limit_of_products_equalizer].

   The smallness discipline the header describes is not decoration.
   Freyd proved that a category with products of families as large as its
   own morphism set is a preorder (Abelian Categories, Harper & Row,
   1964, exercise D of ch. 3): were some hom-set to hold two distinct
   arrows, the product indexed by all morphisms would yield a hom-set of
   cardinality at least 2^|Mor|, exceeding |Mor| by Cantor's theorem.  It
   follows that complete small categories are preorders — up to
   equivalence, complete lattices (Adámek–Herrlich–Strecker, Abstract and
   Concrete Categories, Theorem 12.7; Shulman, arXiv:0810.1279, Thm 2.1).
   Here it is Structure/Complete/Freyd.v's [small_complete_is_thin]
   (arrows indexed by a type, [Complete], a DECIDABLE hom-setoid ⇒ [Thin])
   with [complete_has_glbs]; and instantiating [Complete] forces the
   diagram category's hom universe to coincide with C's (SAFT.v's header).

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
   theorem cannot be proved constructively — which is why Freyd.v takes
   the decider [DecHom] as an explicit hypothesis and stays axiom-free;
   its [freyd_no_separated_pair] is the constructive kernel.  The stake is
   the semantics of impredicative polymorphism: interpreting ∀X.T as a
   product over all objects of a small complete subcategory of Set is
   classically impossible (Reynolds 1984), yet realizably consistent —
   the PER models of System F: a type of all types closed under products. *)

(* ---------------------------------------------------------------------
   THE SIZE NOTE: solution sets, shape universes, and propositional
   equality.  AUTHORITATIVE; cite it, do not restate it.

   This is the library's single statement of why the adjoint functor
   theorems are hard to APPLY at a concrete algebraic category, and of what
   this library does about it.  docs/INHABITATION.md's preamble carries a
   two-paragraph echo and names this block as the authority; the headers of
   Adjunction/GAFT.v, Adjunction/SpanningArrow.v, Instance/Mod/TensorAFT.v
   and Instance/Grp/FreeAFT.v cite it rather than re-deriving the
   arithmetic.  What it does NOT cover is [Complete]'s own four universe
   binders: those are the block immediately below, and are not repeated
   here.

   1. THREE LINES OF SIZE ARITHMETIC.  Measured with [About] under
      [Set Printing Universes]; the readbacks and the two refusals are
      pinned in Test/ProbePropEquiv.v (:211, :218, :310, :328):

        PropRelSpace@{u}   : Type@{u} → Type@{u}
        CRelSpace@{u v}    : Type@{u} → Type@{v}     with u < v
        Setoid@{u u} A     : Type@{u+1}, one level above the carrier

      A [Prop]-valued relation on a carrier in [Type@{u}] is itself a type
      in [Type@{u}].  A [Type]-valued one is NOT: ascribing the same space
      at the carrier's own level ([CRelSpace_small], Test/ProbePropEquiv.v:
      310) is refused, "The term "A → A → Type" has type "Type@{u+1}" while
      it is expected to have type "Type@{u}"".

      This library's `≈` is [Type]-valued -- [equiv : crelation A],
      Lib/Setoid.v:33 -- and stays so, because in [Cat] an [F ≈ G] IS a
      family of isomorphisms (Theory/Functor.v:149, [Functor_Setoid]):
      data, which truncation would discard.  CONSEQUENCE: for a setoid
      whose `≈` is [Type]-valued, the congruences on its carrier -- and so
      the family of quotient presentations of a term model, which is what
      Mac Lane's §V.7 solution-set argument produces -- form a type one
      universe ABOVE that carrier.

   2. THE CONSTRAINT CHAIN OF THE ADJOINT FUNCTOR THEOREM.  Three links,
      each measured.

      (a) [Complete] leaves its shape-object universe free (next block).

      (b) Adjunction/GAFT.v applies a [Complete] to the DISCRETE category
          on the solution-set index ([DiscreteCat_Functor (wif_obj W)],
          Adjunction/GAFT.v:348), so the index universe of a solution set
          EQUALS the shape-object universe of the completeness hypothesis.
          Measured: [GAFT] carries [@Complete@{h h h cobj} C] beside
          [SolutionSet@{h dobj cobj h}], and [representability_theorem]
          carries [Complete@{h h h cobj}] beside [ElementSolutionSet@{cobj
          h su h}] -- the same [h] in the shape-object slot and in the
          index slot.  This is not an artifact of the formalisation: it is
          the constraint mathlib states as [HasLimitsOfSize.{w,w}] with
          [ι : Type w], and the 1lab as [is-complete ℓ ℓ] with
          [{index} : Type ℓ].

      (c) The equalizer of all endomorphisms of the product, taken in the
          same proof, forces that one shape-object universe to dominate the
          AMBIENT HOM universe as well (mathlib's [LocallySmall.{w}]); the
          mechanism is written out at Adjunction/GAFT.v's [GAFT] header.

      And the cap from the other side: [Sets_Complete@{u u0} :
      Complete@{u u u u0}] (Instance/Sets/Complete.v:196) puts the
      shape-object universe AT the carrier universe [u], because the limit
      carrier quantifies over the shape's objects and must itself be a
      carrier.  [Ab_Complete] and [RMod_Complete] inherit that shape through
      limit creation over [Sets].

   3. CONSEQUENCE, AND THE ROUTES THAT DO NOT ESCAPE IT.  A solution set
      indexed by a Σ over the OBJECTS of a concrete algebraic category --
      [SpanningArrowsOutOf] (Adjunction/SpanningArrow.v), a record over its
      carrier -- sits one universe above where 2(b) needs it; so does one
      indexed by [Type]-valued congruences, by 1.  Each of the following
      was compiled and refused, and none removes the gap: a universe lift
      of the category (the setoid-object records are non-cumulative);
      [Set Polymorphic Inductive Cumulativity] (it moves terms up, not
      types down); an SProp-valued `≈` (an SProp relation cannot inhabit
      [crelation] at all); a [Prop]-truncated kernel eliminated into a
      [Type]-sorted goal (refused even when `≈` is [eq], because the sort
      of [equiv x y] is judged from the declared type of [equiv] --
      Test/ProbePropEquiv.v:261); propositional resizing (the index is not
      an hProp, and the core is axiom-free); and an index-free "large
      completeness" ([RMod@{u}] has no object-indexed products at its own
      universe).  The surviving in-tree refusal is recorded verbatim in
      Instance/Mod/TensorAFT.v and pinned in Test/ProbeModTensorAFT449.v.

      SEPARATELY, and now HISTORY: until the PR "algebraic carriers are
      sets" (2026-09-17) a literal [Set] appeared in these signatures as
      well.  It was a universe-minimization artifact of the unannotated
      [DiscreteCat_Functor] (Instance/Discrete.v:81), not part of the size
      condition; annotating that donor removed every such [Set] and, as
      measured beforehand, left the refusals of this paragraph exactly
      where they were.  Prose quoting a [Set]-carrying signature predates
      that PR.

   4. THE RESOLUTION ADOPTED BY THIS PR.  Concrete algebraic categories
      (CMon, Ab, RMod, Grp, Rig/Rng) are categories of SETS with structure,
      and this library now says so in their object records: each carries
      [PropEquiv] (Lib/Setoid/Propositional.v:127), the property that the
      carrier's `≈` is logically a [Prop]-valued relation.  By 1 the
      congruences on a term model are then [Prop]-valued and carrier-sized,
      so they index a solution set at exactly the shape-object universe
      2(b)+(c) demands.  The consumers are Instance/Mod/TensorAFT.v (the
      tensor product of modules and the balanced maps),
      Instance/Rng/AFT.v (the free ring over Sets and over Ab) and
      Instance/Grp/FreeAFT.v (the free group), which obtain their objects
      from [representability_theorem] / [GAFT] with no hypothesis beyond
      the ring or the setoid.  Mac Lane's Lemma V.7.2 -- "the spanning
      codomains are quotients of the term module, hence a set" -- becomes
      [SmallUpToIso] of the spanning family (Adjunction/GAFT/Resize.v, with
      [SmallType] in Theory/Size.v), proved through the congruence index.

      WHAT IS IN TREE: all of it.  An earlier revision of this paragraph
      was headed "WHAT IS ALREADY IN TREE AS THIS BLOCK IS WRITTEN" and
      listed the [PropEquiv] class, its transports, Test/ProbePropEquiv.v
      and the universe hygiene of item 2, saying that "the object records
      of the algebraic categories, the unconditional tensor and free group,
      and [SmallUpToIso] land in later commits of the same PR" and that a
      reader who found one of those missing should read this item as the
      plan it was.  Those commits landed, and the item is now measured
      throughout rather than planned.  Concretely: the class and its
      elimination lemma are Lib/Setoid/Propositional.v:127 and :188, the
      transports through Sets and [LocallyPropositional] are
      Instance/Sets/Propositional.v:91/:132/:169/:203/:240; the object
      records carry the field at Instance/CMon.v:70 ([cmon_prop], reaching
      Ab, RMod, Rg and their satellites by coercion),
      Theory/Algebra/Rig.v:180 ([rig_prop], reaching Ring, Rng, CRng and
      Field) and Instance/Grp.v:228 ([grp_prop]); hom-setoids inherit it
      pointwise and limit vertices from their legs, with no hypothesis on
      the limit ([alim_prop], [glim_prop], [rlim_prop]); the resizing
      vocabulary is Adjunction/GAFT/Resize.v with [SmallType] at
      Theory/Size.v:214; and the applications named above are
      unconditional, with Mac Lane's own spanning family proved small up
      to isomorphism at Instance/Mod/TensorAFT.v:2138 and fed to the
      theorem at :2163.  Every constant of that work is reported "Closed
      under the global context" and gated.

      WHAT IS STILL NOT IN TREE, so that this item is not read as more
      than it is: a solution set indexed by a Sigma over the OBJECTS of a
      concrete algebraic category remains refused, which is item 3 and is
      unchanged.  [tensor_esols_direct] is still refused as a direct
      premise (its index carries carrier < index where the congruence
      index carries carrier <= index); Mac Lane's own [Subgroup G]-indexed
      family for the free group is not built, the congruence index
      replacing it rather than resizing it; and [GAFT_from_spanning],
      although its hand-written [Set] annotation was deleted in the same
      PR, is still refused at [RMod R], the widened statement wanting
      objects at or below homs where [RMod R] has homs strictly below
      objects.  The one new side condition the resolution costs is
      [Set] < the carrier universe -- the sort of [Prop] reaching the
      index universe -- measured slot by slot against the conditional
      forms, costing nothing in practice and nothing at all at [Ab].

      SCOPE, because the property is deliberately narrow: [PropEquiv] is a
      property of a SETOID, not a change to [Class Setoid], and internal
      algebra in an arbitrary category (the Theory/Algebra/ files) keeps the
      ambient `≈` and carries no such field.  Nothing here makes `≈` propositional
      anywhere it was not already.
   --------------------------------------------------------------------- *)

(* THE FOUR UNIVERSES, NAMED, BECAUSE DOWNSTREAM STATEMENTS TURN ON WHICH
   OF THEM IS WHICH.  Read in the declared order:

     [r]   the level of the resulting [Type] (the limit datum's own),
     [so]  the SHAPE's object universe -- the level at which diagram
           categories [D] may be indexed,
     [h]   the shape's AND the ambient's hom-and-proof universe: [Limit]
           identifies the two, where [Cone] keeps them apart, and that
           identification is inherited here rather than introduced,
     [o]   the AMBIENT category's object universe.

   The two declared constraints, [so <= r] and [h <= r], are [Limit]'s own
   and say only that the datum lives above the levels it quantifies over.
   NOTHING here relates [so] to [h] or to [o]: a complete category may be
   indexed by shapes at any level.  What ties them is the APPLICATION --
   Adjunction/GAFT.v:348 applies a [Complete] at a discrete shape whose
   objects are a solution-set index, and Adjunction/GAFT.v's own binders
   record the identification that forces there.

   The measured readback is

     Complete@{r so h o} : Category@{o h h} → Type@{max(r,so+1,h+1,o)}
     (* r so h o |= so <= r / h <= r *)

   -- and, since Instance/Discrete.v:81's [DiscreteCat_Functor] was
   annotated in the PR "algebraic carriers are sets" (2026-09-17), with no
   literal [Set] in it.  An earlier revision of this file's consumers
   quoted [Complete@{Set Set Set u}] and [Complete@{u0 u0 Set u2}]; those
   [Set]s were a universe-minimization artifact of that donor and are
   gone. *)

(* C is complete: every diagram F : D ⟶ C has a limit (terminal cone) in C. *)
Definition Complete@{r so h o | so <= r, h <= r} {C : Category@{o h h}} :=
  ∀ (D : Category@{so h h}) (F : D ⟶ C), Limit@{r so h o} F.

(* C is cocomplete: every diagram F : D ⟶ C has a colimit in C — the dual of
   completeness, equivalently completeness of C^op.  Same four universes in
   the same order. *)
Definition Cocomplete@{r so h o | so <= r, h <= r} {C : Category@{o h h}} :=
  ∀ (D : Category@{so h h}) (F : D ⟶ C), Colimit@{r so h o} F.
