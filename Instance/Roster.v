Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Metacategory.General.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.

(* Sets and set-like categories. *)
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ens.
Require Import Category.Instance.EnsV.
Require Import Category.Instance.Rel.
Require Import Category.Instance.Rel.Dagger.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Instance.Sets.Par.
Require Import Category.Instance.Coq.Par.

(* Algebraic categories. *)
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Matr.

(* Order, shape and graph categories. *)
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Instance.Simplex.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Concrete.

(* SEGREGATED: the two entries below are the file's entire non-Closed
   axiom footprint, and they are required here only so that the roster
   is complete in one place.  Instance/Top and its satellites run
   through the standard library reals (Instance/Top/Interval.v), so
   every constant mentioning them carries stdlib axioms; see the AXIOMS
   paragraph of the header. *)
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Homotopy.

(* SEGREGATED: Instance/Comp.v is a Leibniz-equality development that
   invokes [functional_extensionality] (the caveat Instance/Ab.v's
   header records).  It is REQUIRED WITHOUT IMPORT, both to keep that
   axiom off this file's other constants and because its record field
   names ([carrier], [eq], [map]) would shadow the library's; every
   reference below is fully qualified. *)
Require Category.Instance.Comp.

Generalizable All Variables.

(** * Roster: the standard large categories, in one place

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.1
    (printed pp. 8-9), the metacategory examples, and §I.2 (printed
    pp. 10-12), the roll-call of large categories that the rest of the
    book quotes without further comment
    [maclane:I.1:construction2, maclane:I.2:construction12]; Awodey,
    "Category Theory", 2nd ed., §1.4, the category of structured sets
    and structure-preserving functions
    [awodey:1.4:construction-structured-sets]; Riehl, "Category Theory
    in Context", §1.1, Example 1.1.3's clause-by-clause list of large
    concrete categories and Example 1.1.4's list of categories whose
    objects are not sets [riehl:1.1:example3, riehl:1.1:example4].
    nLab: https://ncatlab.org/nlab/show/concrete+category
    Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

    WHAT THIS FILE IS.  An INDEX, not a construction, and the contract
    is meant literally: every entry of the four surveys listed above —
    Mac Lane's §I.1 metacategory examples and §I.2 roll-call, Awodey's
    §1.4 structured sets, Riehl's Examples 1.1.3 and 1.1.4, and Riehl's
    Example 1.6.15 initial/terminal survey — is EITHER exhibited here
    from the tree (the category, and its evident forgetful functor or
    initial/terminal instance where the tree packages one) OR listed in
    the OUT OF SCOPE section below with the reason it is absent.  There
    is no third case: an entry that appears in none of the sections
    below is an omission, not a silent judgement.  The value is the
    single point of reference — a reader who wants to know whether this
    library has "the category of rings", or what it calls it, or
    whether "the category of measurable spaces" exists, should need to
    open one file.  Nothing is re-proved here.  Two things are
    genuinely new: [Mon_Sets], the residual instantiation named in the
    section below, and — in the companion Instance/Field.v — the
    category of fields together with the determination of its
    monomorphisms and the absence of initial and terminal objects,
    which is the one roster entry that asks for mathematics rather
    than bookkeeping.

    HOW TO READ AN ENTRY.  Each entry is one or two [Example] lines
    naming the category at its declared type and, where the tree
    packages one, the functor down to [Sets] or to the neighbouring
    structure.  An [Example] that typechecks is the claim: this
    category exists, under this name, with this shape.  Where the tree
    packages no forgetful functor, that is said rather than patched —
    building one is the business of the file that owns the entry, not
    of an index.

    THE MAC LANE ROSTER (§I.2), entry by entry.  Set is [Sets] (setoids
    — see Instance/Sets.v on why the library's "sets" carry an
    equivalence rather than Leibniz equality) with [Coq] the strict
    variant and [Ens]/[EnsV] Mac Lane's own set-within-a-universe
    readings; Set_* is [PointedSets]; Ens_V is [EnsV]; Mon is
    [Mon_Sets] below (internal monoids in (Sets, ∏)) with [CMon] the
    commutative set-level variant; Grp is [Grp]; Ab is [Ab]; Rng is
    [Rng] with [CRng] its commutative full subcategory; R-Mod is
    [RMod R], Mod-R is [ModR R], and bimodules are the record
    [Bimodule]; Vct_K is [Vct_F] with [FdVect] the finite-dimensional
    refinement carrying chosen coordinates; Top is [Top]; Toph is
    [Toph]; Top_* is [Top_pointed] and Toph_* is [Toph_pointed]; Cat is
    [Cat] with [StrictCat] the strict-functor-equality variant;
    Preord/Pos are [Proset]/[Pos] (see the erratum below); Δ is
    [Simplex]; Matr_K is [Matr]; Rel is [Rel]; and the arrows-only
    metacategory of §I.1 is [Metacategory], with
    [Category_from_Metacategory] the passage back.

    A NAMING ERRATUM, recorded because it has misled before.
    Instance/Poset.v's [Poset] TAKES an [Antisymmetric] hypothesis and
    then DISCARDS it: its body is literally [Proset P].  So it turns
    ONE preorder into a thin category, the antisymmetry contributes
    nothing to the category produced, and it is not the category of
    posets under another name.  The category whose OBJECTS are posets
    is Instance/Pos.v's [Pos].  Riehl 1.1.3's "Poset" clause is [Pos];
    Mac Lane's "Preord" is Instance/Ord.v's [Ord] (#372), NOT [Proset],
    which is ONE preorder.  [Pos] and [Proset] are exhibited below, side
    by side; [Ord] is NOT exhibited here (it would add Instance/Ord.v to
    this file's closure and move its measured counts), which is disclosed.

    RIEHL 1.1.4, the non-concrete entries.  Clause (i), the matrix
    category Mat_R, is [Matr] (Instance/Matr.v).  Clause (ii), the
    delooping BG of a group or monoid, is Construction/Deloop.v's
    [Deloop] — cited, not required here, to keep this file's dependency
    cone to the roster proper.  Clause (vii), the category Measure of
    almost-everywhere classes of measurable maps, is out of scope; see
    below.

    OUT OF SCOPE, each with its reason.  These are disclosures, not
    apologies: the reason in every case is a missing piece of
    mathematics elsewhere in the tree, named so that a later issue can
    pick it up.

      - Compact Hausdorff spaces AS A ROSTER ENTRY WITH ITS FORGETFUL
        STORY.  The full subcategory itself EXISTS and is exhibited
        below ([CompactHausdorffSpaces], Instance/Top.v).  What stays
        out is the reason the books list it: the underlying-set functor
        with its left adjoint (the Stone-Čech compactification) and the
        ultrafilter-monad monadicity theorem.  The first is obstructed
        by the universe stratification Instance/Top/Forgetful.v proves
        out — Top's homs sit strictly above its points, so the
        forgetful functor lands in a HIGHER [Sets] and the packaged
        [Adjunction] record is unformable — and the second needs
        ultrafilters, which the tree has not got.

      - Ringed spaces.  There is no sheaf-of-rings machinery over
        [Top]: Theory/Sheaf.v's [Sheaf] predicate is per-leg and, as
        Theory/Sheaf/Category.v's header discloses, vacuous beyond
        subsingleton fibres, so a structure sheaf could not be stated
        honestly.  Gated on the matching-family re-founding that ships
        with sheafification.

      - Man, smooth manifolds and smooth maps.  No differential
        structure of any kind exists in the tree — no charts, no
        atlases, no smoothness predicate — and Instance/Rng/Frac.v
        already descopes the Lie-algebra half of its own exercise for
        the same reason.

      - Meas, measurable spaces, and Measure, its quotient by
        almost-everywhere equality [riehl:1.1:example4].  σ-algebras
        and null sets are both absent.  Worth recording as a FUTURE
        TARGET rather than a permanent gap: Measure is a natural test
        of this library's setoid discipline, since a.e.-equality is
        exactly a hom-setoid coarser than pointwise equality, which is
        what [homset] is for, and Construction/Quotient.v already has
        the hom-congruence quotient the construction would use.

      - ℕ with the recursive functions as morphisms.  Computability
        theory is out of scope; nothing in the tree formalizes a model
        of computation.  (Instance/Lambda/ formalizes the simply-typed
        lambda calculus over de Bruijn syntax — the internal language
        of a cartesian closed category — which is a different subject:
        a term language with its own semantics, not the partial
        recursive functions.)

      - Chain complexes Ch_R and their chain maps.  There is no graded
        machinery — no ℤ-graded objects, no differentials, no
        homology — so the entry would have no content beyond a record
        declaration.  Riehl's §E.2 material is tracked separately.

      - Model_T, the category of models of a full first-order theory.
        What the tree has is the EQUATIONAL fragment: Instance/Comp.v's
        [Algs] for an operation signature, together with its equational
        refinement (see the segregated section below), and
        Theory/Lawvere/Model.v's [Models T C] for a Lawvere theory.
        Relation symbols, quantifiers and non-equational axioms are
        absent, so "the category of models of T" is delivered only for
        algebraic T.

      - SIMPLE GRAPHS (Riehl 1.1.3's graph clause, in the symmetric
        irreflexive reading).  What the tree has is QUIVERS — directed
        multigraphs with an edge TYPE between each ordered pair
        ([QuiverCategory], exhibited below).  Simple graphs, with a
        symmetric irreflexive relation and no parallel edges, are not
        constructed.  The clause is worth its own row rather than
        folding into the quiver one, because it is the clause with the
        interesting initial/terminal behaviour: the empty graph is
        initial, but there is NO terminal simple graph, since a
        terminal one would have to receive the one-vertex-with-a-loop
        graph and hence carry a loop, which irreflexivity forbids.
        With no simple graphs in tree, neither half is statable.

      - Awodey's TWO REAL-ANALYSIS ROSTER ENTRIES: ℝ with the
        continuous maps, and the open subsets of ℝ with the continuous
        maps between them.  The INGREDIENTS exist —
        Instance/Top/Presheaf.v builds the real line as a space
        ([R_Top], its metric topology carried by a ball structure) and
        the open subspaces ([OpenSub]) with their subspace topology
        identified — but neither roster CATEGORY is assembled: not the
        endomorphism monoid of ℝ read as a one-object category, and not
        the full subcategory of [Top] on the open subspaces of ℝ.
        Nothing downstream consumes either, which is why they were
        never built; both are short given the ingredients, and both
        would land in the reals-carrying group.

      - The DERIVATIVE as a functor — the assignment sending a smooth
        map to its Jacobian, which is the standard first example of a
        functor whose action on morphisms is the interesting part.
        Same root cause as Man: there is no differential structure in
        the tree, so neither the domain category nor the morphism
        action can be written down.

      - The determination of the monomorphisms of the category of
        fields, and the absence of initial and terminal objects there,
        are NOT here: they are Instance/Field.v, which owns the
        category and both theorems, and which discloses in its own
        header the exact constructive strength of each.  The entry
        points are cross-referenced in the initial/terminal section
        below.

    AXIOMS, measured per constant rather than sampled, and the
    measurement is FINER than the section headings would suggest.  The
    count is docs/AXIOMS.md's: everything the module declares, which
    for this file is 96 constants — 94 [Example]s, the two
    [Definition]s of the [Mon_Sets] section, and no [Program]
    obligations, since no declaration here generates any.  Of those 96,
    90 are "Closed under the global context".  The other six are these,
    and only these:

      - [roster_Toph], [roster_TophProj], [roster_Toph_pointed],
        [roster_Toph_pointed_Proj] carry BOTH stdlib axioms
        ([ClassicalDedekindReals.sig_forall_dec] and
        [FunctionalExtensionality.functional_extensionality_dep]);

      - [roster_Group_variety] and [roster_Group_variety_witness] carry
        [functional_extensionality_dep] alone.

    Two consequences are worth stating because they correct the obvious
    guess.  FIRST, [Top] is NOT a reals-carrying entry: [roster_Top],
    [roster_Top_Forget], [roster_Top_Discrete],
    [roster_Top_Indiscrete], [roster_HausdorffSpaces],
    [roster_CompactHausdorffSpaces] and [roster_Top_pointed] are all
    Closed.  The reals enter only with the HOMOTOPY relation, which
    needs the unit interval (Instance/Top/Interval.v) — so it is the
    quotient categories Toph and Toph_*, not the topology, that pay.
    SECOND, [roster_Algs] and [roster_GroupOp] are Closed as well:
    Instance/Comp.v's signature and category machinery is axiom-free,
    and [functional_extensionality] is spent only in [GroupEq]'s
    naturality proof, hence only by the two constants that mention the
    group VARIETY.  The body is ordered so that in each segregated
    section the Closed constants come first and the six exceptions come
    last, contiguously. *)

(** ** Sets and the set-like categories *)

(* Mac Lane's Set, in the library's two readings: setoids, and the
   strict category of Coq types with functions. *)
Example roster_Sets : Category := Sets.
Example roster_Coq : Category := Coq.

(* Mac Lane's Ens and Ens_V: sets carrying membership, and the sets
   within a universe V presented as codes with a decoding.  [EnsV] is
   Mac Lane's own device for making "the category of all sets" a
   legitimate object; [Spanned] is its general form. *)
Example roster_Ens : Category := Ens.
Example roster_EnsT (T : Type) : Category := EnsT T.
Example roster_EnsV {V : Type} (El : V → Type) : Category := EnsV El.
Example roster_EnsV_Incl {V : Type} (El : V → Type) : EnsV El ⟶ Coq :=
  EnsV_Incl El.

(* Finite sets, in both presentations: the skeletal one on [nat], and
   finite setoids carrying their counting, with the comparison. *)
Example roster_FinSet : Category := FinSet.
Example roster_Set_f : Category := Set_f.
Example roster_FinSet_Incl : FinSet ⟶ Set_f := FinSet_Incl.

(* Mac Lane's Set_*: pointed sets and basepoint-preserving maps.  The
   underlying-set functor is still not packaged in
   Instance/Sets/Pointed.v and is not built here, but it now EXISTS:
   [Pointed_Forget], Instance/Sets/Pointed/Free.v, built directly for
   Mac Lane III.1 Ex 3's basepoint row.  The coslice presentation
   ([Pointed_Coslice_iso], Instance/Sets/Pointed/Coslice.v) remains an
   alternative route and is not the one taken. *)
Example roster_PointedSets : Category := PointedSets.

(* Partial maps, in both readings: over setoids and over types. *)
Example roster_Part : Category := Part.
Example roster_Par : Category := Par.

(* Rel, with the wide embedding of functions as relations.  Note the
   direction: [Relation_Functor] goes from [Coq], not from [Sets]. *)
Example roster_Rel : Category := Rel.
Example roster_Relation_Functor : Coq ⟶ Rel := Relation_Functor.

(** ** The algebraic categories, with their forgetful functors *)

(* Commutative monoids at the set level. *)
Example roster_CMon : Category := CMon.
Example roster_CMon_Forget : CMon ⟶ Sets := CMon_Forget.

(* Groups and abelian groups. *)
Example roster_Grp : Category := Grp.
Example roster_Grp_Forget : Grp ⟶ Sets := Grp_Forget.
Example roster_Ab : Category := Ab.
Example roster_Ab_Forget : Ab ⟶ Sets := Ab_Forget.

(* Rigs, and rings under Mac Lane's name, with the commutative full
   subcategory and both forgetful functors. *)
Example roster_Rig : Category := Rig.
Example roster_Rig_Forget_CMon : Rig ⟶ CMon := Rig_Forget_CMon.
Example roster_Rng : Category := Rng.
Example roster_Rng_Forget : Rng ⟶ Sets := Rng_Forget.
Example roster_Rng_Forget_Ab : Rng ⟶ Ab := Rng_Forget_Ab.
Example roster_CRng : Category := CRng.

(* Modules on both sides, and the bimodule record that justifies the
   right-module definition. *)
Example roster_RMod (R : RingObject) : Category := RMod R.
Example roster_RMod_Forget (R : RingObject) : RMod R ⟶ Sets :=
  RMod_Forget R.
Example roster_RMod_Forget_Ab (R : RingObject) : RMod R ⟶ Ab :=
  RMod_Forget_Ab R.
Example roster_ModR (R : RingObject) : Category := ModR R.
Example roster_Bimodule (R S : RingObject) : Type := Bimodule R S.

(* Vector spaces over a field, and the finite-dimensional refinement
   whose objects carry chosen coordinates. *)
Example roster_Vct_F (F : FieldObject) : Category := Vct_F F.
Example roster_FdVect (F : FieldObject) : Category := FdVect F.
Example roster_FdVect_Forget (F : FieldObject) : FdVect F ⟶ Vct_F F :=
  FdVect_Forget F.

(* Fields.  The category and the determination of its monomorphisms
   are Instance/Field.v's; only the entry is recorded here. *)
Example roster_Field : Category := Field.
Example roster_Field_Forget : Field ⟶ Sets := Field_Forget.
Example roster_Field_Rng : Field ⟶ Rng := Field_Rng.

(* Representations of a group over a ring. *)
Example roster_Rep (K : RingObject) (G : GrpObject) : Category :=
  Rep K G.

(* Matrices over a rig, with Awodey's ℕ-matrix and Mac Lane's integer
   instantiations. *)
Example roster_Matr (R : RigObject) : Category := Matr R.
Example roster_Matr_N : Category := Matr_N.
Example roster_Matr_Z : Category := Matr_Z.

(** ** The Mon residual: internal monoids in (Sets, ∏) *)

(* Theory/Algebra/Monoid/Hom.v defines [Mon] inside a section over an
   arbitrary monoidal category, so Mac Lane's roster entry Mon — THE
   category of monoids — has existed in the tree only as a section
   variable waiting for its base.  Instantiating it at [Sets] with the
   cartesian monoidal structure of Instance/Sets.v supplies the entry
   and names it.  This is not a new construction: Theory/Algebra/Rig.v
   already lands in exactly this category ([Rig_Forget_Mon], the
   multiplicative half of a rig), which the third example below records
   by having that functor typecheck at the new name. *)
Definition Mon_Sets : Category := @Mon Sets Sets_Product_Monoidal.

Definition Mon_Sets_Forget : Mon_Sets ⟶ Sets :=
  @Mon_Forget Sets Sets_Product_Monoidal.

Example roster_Mon_Sets : Category := Mon_Sets.
Example roster_Mon_Sets_Forget : Mon_Sets ⟶ Sets := Mon_Sets_Forget.
Example roster_Rig_Forget_Mon : Rig ⟶ Mon_Sets := Rig_Forget_Mon.

(* One pointer, and no comparison is owed here.  An object of
   [Mon_Sets] is an INTERNAL monoid in (Sets, ∏) — not assumed
   commutative — whereas [CMonObject] is a set-level COMMUTATIVE monoid
   presented as a record.  The two are the two halves of a rig, and
   Theory/Algebra/Rig.v projects onto each: the multiplicative half by
   [Rig_Forget_Mon] into [Mon_Sets], the additive half by
   [Rig_Forget_CMon] into [CMon].  A full dictionary between the
   internal and the set-level presentations belongs to whichever issue
   wants it; the roster needs only that both entries exist. *)

(** ** Order categories, and the Poset/Proset erratum *)

(* ONE preorder as a thin category (Mac Lane's Preord is [Ord]).  The
   witness is (ℕ, ≤). *)
Example roster_Proset {A : Type} {R : A → A → Prop}
  (P : RelationClasses.PreOrder R) : Category := Proset P.
Example roster_Proset_nat : Category := Proset PeanoNat.Nat.le_preorder.

(* The category whose OBJECTS are posets — Riehl 1.1.3's Poset clause.
   Instance/Poset.v's identically-spelled [Poset] is NOT this: it is
   [Proset] under another name, antisymmetry discarded.  See the
   erratum in the header. *)
Example roster_Pos : Category := Pos.
Example roster_Pos_Forget : Pos ⟶ Sets := Pos_Forget.

(** ** Categories of categories, shapes and graphs *)

Example roster_Cat : Category := Cat.
Example roster_StrictCat : Category := StrictCat.

(* Graphs, in Riehl's sense: the category of quivers.  Its three
   candidate underlying-set functors are Construction/Free/Quiver/
   Concrete.v's, and which of them is faithful is the content there. *)
Example roster_QuiverCategory : Category := QuiverCategory.
Example roster_QuiverVertices : QuiverCategory ⟶ Sets := QuiverVertices.
Example roster_QuiverArrows : QuiverCategory ⟶ Sets := QuiverArrows.

(* The simplicial category Δ, with its wide inclusion into finite
   sets — faithful, and provably not full. *)
Example roster_Simplex : Category := Simplex.
Example roster_Simplex_FinSet : Simplex ⟶ FinSet := Simplex_FinSet.

(* Mac Lane's §I.1 arrows-only presentation, and the passage from it
   back to a category. *)
Example roster_Metacategory : Type := Metacategory.
Example roster_Category_from_Metacategory (M : Metacategory) : Category :=
  Category_from_Metacategory M.

(** ** Initial and terminal objects across the roster

    Riehl, "Category Theory in Context", §1.6 Example 1.6.15 (printed
    p. 38) [riehl:1.6:example15]: the standard categories surveyed for
    their initial and terminal objects.  The entries are cited, not
    rebuilt — each is an instance already registered in the file that
    owns the category — and the two genuinely negative clauses are the
    interesting ones.

    THE PATTERN.  In the algebraic entries the two coincide: the
    trivial object is a ZERO object, which is what [ZeroObject] records
    and what makes the zero morphism available.  In [Sets] and [Cat]
    they differ (the empty set/category against the singleton).  In
    [Top] they differ AND there is provably no zero object.  In [Field]
    NEITHER exists.

    THE UNITAL-RING DISCRIMINATION.  ℤ is initial in [Rng] and the
    zero ring is terminal, both exhibited below.  What makes this the
    discriminating case in the books — that dropping the unit from the
    morphism notion changes the answer — IS now checkable: [Rg], the
    category of non-unital rings, is Instance/Rg.v, and there the zero
    rng is BOTH initial and terminal, since a rng homomorphism is not
    required to preserve 1.  So [Rg] has a zero object, and [Rng]
    does not -- the latter being
    Structure/Kernel/Universal/Examples.v:359's [Rng_no_zero_object].
    Instance/Rg.v's [Rng_Rg_zero_object_contrast] pairs the zero object
    with the sharper elementary fact that no unital homomorphism runs
    from the zero ring to Z, which is what forces terminal and initial
    apart here; this roster is not extended to [Rg] itself, which would
    pull Instance/Rg.v into a file that already carries most of the
    library.  The contrast is no longer prose. *)

(* Sets and the strict variant: the two differ. *)
Example roster_Sets_Terminal : @Terminal Sets := Sets_Terminal.
Example roster_Sets_Initial : @Initial Sets := Sets_Initial.
Example roster_Coq_Terminal : @Terminal Coq := Coq_Terminal.
Example roster_Coq_Initial : @Initial Coq := Coq_Initial.
Example roster_FinSet_Terminal : @Terminal FinSet := FinSet_Terminal.
Example roster_FinSet_Initial : @Initial FinSet := FinSet_Initial.

(* Pointed sets: the singleton is a genuine zero object, which is what
   distinguishes Set_* from Set. *)
Example roster_PointedSets_Zero : ZeroObject PointedSets :=
  PointedSets_Zero.

(* The algebraic entries, where initial and terminal coincide. *)
Example roster_CMon_Zero : ZeroObject CMon := CMon_Zero.
Example roster_Grp_Zero : ZeroObject Grp := Grp_Zero.
Example roster_Ab_Zero : ZeroObject Ab := Ab_Zero.
Example roster_RMod_Zero (R : RingObject) : ZeroObject (RMod R) :=
  RMod_Zero R.

(* Rings: ℤ initial, the zero ring terminal — and they do NOT coincide,
   which is why no [ZeroObject Rng] is cited.  The non-unital contrast
   named in the disclosure above is proved in Instance/Rg.v
   ([Rg_Zero], [Rng_Rg_zero_object_contrast]). *)
Example roster_Rng_Terminal : @Terminal Rng := Rng_Terminal_zero.
Example roster_Rng_Initial : @Initial Rng := Rng_Initial_Z.

(* Relations: a zero object, by self-duality. *)
Example roster_Rel_Zero : ZeroObject Rel := Rel_Zero.

(* Categories of categories. *)
Example roster_Cat_Terminal : @Terminal Cat := Cat_Terminal.
Example roster_Cat_Initial : @Initial Cat := Cat_Initial.
Example roster_StrictCat_Terminal : @Terminal StrictCat :=
  StrictCat_Terminal.

(* FIELDS HAVE NEITHER.  The two theorems are Instance/Field.v's; the
   separating pair is ℚ against F₂, characteristic 0 against
   characteristic 2, and both proofs are constructive.  The
   object-level readings there say it without choosing a candidate: no
   object of [Field] is initial and none is terminal. *)
Example roster_Field_no_initial : @Initial Field → False :=
  Field_no_initial.
Example roster_Field_no_terminal : @Terminal Field → False :=
  Field_no_terminal.

(** ** SEGREGATED SECTION 1: topological entries

    The topology itself is axiom-free; see the AXIOMS paragraph.  Every
    constant in the first half of this section is Closed, and the four
    at the end — the homotopy quotients, which need the unit
    interval — are where the standard library's reals axioms enter.
    The stratification note in the header explains why [Top_Forget]
    lands in a HIGHER [Sets] than the one the algebraic entries use,
    and why the adjunctions are transposition isomorphisms rather than
    packaged [Adjunction] records. *)

Example roster_Top : Category := Top.
Example roster_Top_Forget : Top ⟶ Sets := Top_Forget.
Example roster_Top_Discrete : Sets ⟶ Top := Top_Discrete.
Example roster_Top_Indiscrete : Sets ⟶ Top := Top_Indiscrete.

(* Top's initial and terminal objects differ, and — unlike every
   algebraic entry above — there is provably no zero object: the empty
   space and the point are not isomorphic, and Instance/Top.v proves
   the non-existence outright rather than leaving it to inspection. *)
Example roster_Top_Terminal : @Terminal Top := Top_Terminal.
Example roster_Top_Initial : @Initial Top := Top_Initial.
Example roster_Top_no_zero : @ZeroObject Top → False := Top_no_zero_object.

(* The separation full subcategories.  [CompactHausdorffSpaces] is the
   roster entry; its forgetful/monadicity story is disclosed out of
   scope in the header. *)
Example roster_HausdorffSpaces : Category := HausdorffSpaces.
Example roster_CompactHausdorffSpaces : Category :=
  CompactHausdorffSpaces.

(* Top_*: based spaces and based maps.  Still axiom-free — a basepoint
   costs nothing. *)
Example roster_Top_pointed : Category := Top_pointed.

(* THE FOUR REALS-CARRYING CONSTANTS OF THIS FILE.  Toph and Toph_*:
   spaces and homotopy classes of maps, as hom-congruence quotients of
   [Top] and [Top_pointed], with their identity-on-objects
   projections.  The homotopies are parametrized by the unit interval
   of Instance/Top/Interval.v, which is built over the standard library
   reals; that is the whole of the dependency. *)
Example roster_Toph : Category := Toph.
Example roster_TophProj : Top ⟶ Toph := TophProj.
Example roster_Toph_pointed : Category := Toph_pointed.
Example roster_Toph_pointed_Proj : Top_pointed ⟶ Toph_pointed :=
  Toph_pointed_Proj.

(** ** SEGREGATED SECTION 2: universal algebra (functional
       extensionality)

    Instance/Comp.v is a Leibniz-equality development and invokes
    [functional_extensionality] (the caveat Instance/Ab.v's header
    records).  It does NOT invoke it everywhere: the signature and
    category machinery below is axiom-free, and the axiom is spent in
    [GroupEq]'s naturality proof alone, so only the last two constants
    of this file carry it.  References go through the module alias [UA]
    rather than an [Import], because that file's record fields
    ([carrier], [eq], [map]) would shadow the library's. *)

Module UA := Category.Instance.Comp.UniversalAlgebra.

(* The category of algebras for an operation signature — the equational
   fragment of Model_T.  Axiom-free. *)
Example roster_Algs (S : UA.OpSignature) : Category := @UA.Algs S.
Example roster_GroupOp : UA.OpSignature := UA.GroupOp.

(* THE TWO FUNEXT-CARRYING CONSTANTS OF THIS FILE.  The group variety,
   at the level Instance/Comp.v supplies it: a signature, its
   equations, and the TYPE of algebras satisfying them.  There is no
   category of [Group]s there — [Algs] is taken over an operation
   signature alone, with the equations imposed objectwise — so the
   variety is recorded here as the type it is, and the roster's
   "category of groups" entry is Instance/Grp.v's [Grp] above.  The
   witness is that file's ℤ/2 under exclusive or. *)
Example roster_Group_variety : Type := UA.Group.
Example roster_Group_variety_witness : UA.Group := UA.Bool.
