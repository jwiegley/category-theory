# CLAUDE.md

This codebase is a comprehensive formalization of category theory in Coq/Rocq. It contains 1,603 proof files with 225,209 lines implementing core categorical concepts with zero axioms in the core theory.

## Commands

### Building the Library

```bash
# Build the entire library (default: Rocq 9.1)
make

# Build for specific version (if using Nix)
nix-shell -p coqPackages_9_1.coq --run make

# Build using Nix flake
nix build .#category-theory

# Clean build artifacts
make clean
make fullclean  # removes Makefile.coq as well

# Install library
make install

# Check for admitted proofs or TODOs
make todo
```

### Single File Development

```bash
# Compile a single file
coqc -R . Category Theory/Category.v

# Interactive development (in coqide/vscoq)
# Ensure _CoqProject is loaded with: -R . Category
```

### Proof Development Patterns

The library uses custom tactics in `Lib/Tactics.v`:
- `cat` - standard simplification for category proofs
- `cat_simpl` - more aggressive simplification with program obligations
- `proper` - for proving morphism respectfulness
- `equivalence` - for proving equivalence relations

## Architecture

### Core Abstraction Hierarchy

The library implements category theory through **setoid-based morphisms** where morphisms form equivalence classes rather than using strict equality. This fundamental design choice cascades through the entire architecture:

```
Category (homsets are setoids with ≈ equivalence)
    ↓
Functor (preserves equivalence, not just equality)
    ↓
Natural Transformation (naturality respects ≈)
    ↓
Adjunction/Monad/Kan Extension
```

### Universe Polymorphism Strategy

The library uses three universe parameters `{o h p}` throughout:
- `o` - objects universe level
- `h` - hom-sets universe level
- `p` - proof/proposition universe level
- Constraint: `h <= p` ensures morphism proofs can reference morphisms

This allows categories of categories at any level without universe inconsistencies.

### Duality Architecture

**Key insight**: Duality is built into definitions so `C^op^op = C` by reflexivity.

This requires symmetric laws in core definitions:
- `comp_assoc` AND `comp_assoc_sym` in Category
- `naturality` AND `naturality_sym` in Natural transformations

Benefits:
- Comonads are one line: `Definition Comonad := @Monad (C^op) (M^op)`
- Dual proofs are often automatic
- No code duplication for dual concepts

### Proof Obligation Management

The library uses Coq's Program mechanism extensively:
1. Definitions use `Program Instance` to defer proof obligations
2. `Obligation Tactic := cat_simpl` automates most proofs
3. Remaining obligations proven with specific tactics
4. This separates mathematical content from proof details

### Instance Resolution Strategy

Categories are discovered through:
1. Type classes for concepts (Category, Functor, etc.)
2. `Existing Instance` for conditional instances
3. Notation-driven inference with category hints
4. Explicit category parameters when inference fails

Example: `f ∘[C] g` specifies category C when needed.

## Key Files and Concepts

### Theory Core
- **Theory/Category.v**: Defines categories with setoid hom-sets
- **Theory/Functor.v**: Functors preserve equivalence
- **Theory/Natural/Transformation.v**: Natural transformations
- **Theory/Adjunction.v**: The most important concept - adjunctions
- **Theory/Monad.v**: Monads as endofunctors with structure
- **Monad/Strong.v**: Strong monads — a monad whose functor carries a tensorial strength compatible with η and μ (Kock/Moggi)
- **Comonad/Core.v**: Covariant comonad API over the one-line `Comonad := @Monad (C^op) (M^op)` — extract/duplicate/extend as definitional op-reads; co-Kleisli category (Comonad/CoKleisli.v), co-Eilenberg-Moore coalgebras (Comonad/Coalgebra.v), costrength (Comonad/Strong.v), and the adjunction-induced comonad with co-resolutions by duality (Comonad/Duality.v); Env/Store/Traced instances in Instance/Coq/Comonad/. Monad resolutions: the Kleisli and Eilenberg-Moore free/forgetful adjunctions in Monad/Kleisli/Adjunction.v and Monad/Eilenberg/Moore/Adjunction.v
- **Monad/Monadicity/Beck.v**: Monadicity — the Eilenberg-Moore comparison functor with both triangle theorems and the `Monadic` predicate (Monad/Comparison.v, over a transparent `Adjunction_Induced_Monad`); split coequalizers with absoluteness and reflexive pairs (Structure/Coequalizer/{Split,Reflexive}.v); the Beck engine room — canonical split forks, `EM_Forget` reflects isos and creates U-split coequalizers (Monad/Monadicity/BeckObjects.v); crude monadicity fully proven (Monad/Monadicity/Crude.v); Beck's precise theorem with conservativity derived from creation and the `monadic_creates` converse at `EM_Forget` (Monad/Monadicity/Beck.v); the Dubuc adjoint-triangle lifting theorem (Monad/Lifting.v); identity-monad witness (Monad/Monadicity/Examples.v)
- **Theory/Kan/Extension.v**: Universal property of Kan extensions
- **Theory/Equivalence.v**: Equivalence of categories — quasi-inverse class with the Full+Faithful+essentially-surjective characterization (Equivalence/FullFaithful.v), adjoint equivalences (Equivalence/Adjoint.v), preservation/reflection/creation of limits and transport of adjunctions and monoidal structure along equivalences (Equivalence/{Limit,Adjunction,Monoidal,Bundled}.v); RAPL/LAPC in Adjunction/Continuity.v over the preservation vocabulary of Structure/Limit/Preservation.v; adjunction composition in Adjunction/Compose.v
- **Theory/Bicategory.v**: Bicategories (weak 2-categories) — the full class over hom-categories `bicat x y`, with horizontal composition `hcompose` as a bifunctor, the Godement product `hcomp2 := fmap[hcompose]`, left/right unitors and associator as 2-isomorphisms with to-direction naturality, and the triangle/pentagon coherence laws (every field mirroring Structure/Monoidal.v under delooping: tensor↔hcompose, I↔bi1id), plus the smart constructor `Build_Bicategory'`; pseudofunctors with identity/composite and the associativity hexagon (Theory/Bicategory/Pseudofunctor.v); lax/oplax transformations and the pseudonatural mixin per Johnson–Yau (Theory/Bicategory/Lax.v); modifications and the category of lax transformations (Theory/Bicategory/Modification.v); adjunctions in a bicategory with both swallowtail triangles, uniqueness of adjoints up to invertible 2-cell (`adjoint_unique`), and the general Kelly unit coincidence `λ_I ≈ ρ_I` derived from pentagon+triangle (Theory/Bicategory/Adjunction.v); the mates correspondence `mate`/`mate_iso`/`mate_roundtrip_{left,right}` as a bijection of 2-cell setoids in Sets, factored through the precomp/postcomp hom-adjunctions with both round-trips from the zig-zag identities (Theory/Bicategory/Mates.v — functoriality under pasting is ledger 10); a monoidal category as a one-object bicategory by direct delooping (Theory/Bicategory/OneObject.v). Cat is the motivating bicategory with `bicat C D ≡ [C, D]` definitionally (Instance/Cat/Bicategory.v, raw `Build_Bicategory` so record-eta holds, reconciling Fun.v's reversed unitor names), where a bicategorical adjunction coincides with `F ∹ U` hence `F ⊣ U`, precomposition is the `⌊−⌋` transpose, and the general mate unfolds to the Kelly–Street formula `Cat_mate_unfold` (Instance/Cat/Bicategory/Adjunction.v)
- **Theory/DoubleCategory.v**: Pseudo double categories — strict vertical category, weak horizontal composition; squares `dsq h u v k` form setoids with the boundary-coercion calculus `dsq_coerce` (groupoid laws + derived lemma pack — the Phase-10 displayed `dtransport` pattern re-applied), strict vertical laws stated through coercion, horizontal pasting with `dinterchange`, and invertible GLOBULAR `dassoc`/`dunit_left`/`dunit_right` (sigma packaging, named accessors) under triangle+pentagon coherence at square level; header discloses the coherence-only scope (horizontal identity squares on verticals, unit-interchange, and coherence naturality are not required — both models satisfy them) and the associator orientation (opposite to Bicategory's `hassoc`). Companions and conjoints with the vertical zigzag in its standard representability form (`companion_name`/`companion_eval` transposition bijection) and uniqueness up to canonical invertible globular square under the `DoubleCoerceComp` mixin (coercion-vs-composition interchange, mirroring Displayed's `dtransport_comp_l/r`, underivable from the class) in Theory/DoubleCategory/Companion.v. Models: the commuting-squares double category `Sq C` where `dsq h u v k := (k ∘ u ≈ v ∘ h)` is a proposition, every morphism is its own companion, and conjoints exist EXACTLY for isomorphisms (`Sq_companion`, `Sq_conjoint`, `Sq_conjoint_iso` — a plan erratum corrected to the standard characterization; Construction/Sq.v); and the cospans double category over chosen pushouts with genuinely proof-relevant squares, unitors/associator from the pushout UMP, and the FULL pentagon proved via the single pasting principle `pushout_jointly_epic` (Construction/Cospan/Double.v)
- **Adjunction/GAFT.v**: The adjoint functor theorems — GAFT concluded through the in-tree proven universal-arrow assembly (`Theory/Universal/Arrow.v`'s `AdjunctionFromUniversalArrows`): `SolutionSet`, `GAFT_from_initials` (immediate from a family of comma-initial objects), and `GAFT` routed solution-set ⇒ weakly-initial family ⇒ initial object ⇒ adjoint. The weakly-initial crux is the product+equalizer-of-all-endomorphisms Freyd construction (`Theory/WeaklyInitial.v`: `initial_from_weakly_initial`, with the endomorphism-indexed product kept an explicit input so smallness stays caller-chosen); limit creation in the comma `=(d) ↓ U` is `Comma_Complete` (`Construction/Comma/Limit.v`) stated over the honest cone-level `PreservesImageLimit` — the in-tree apex-only `PreservesLimit` is genuinely insufficient (its legs are unconstrained), and every right adjoint satisfies the cone-level form (`right_adjoint_PreservesImageLimit`). SAFT is a GAFT corollary with the well-powered/cogenerator hypotheses packaged as data since the library has no smallness/image-factorization machinery (`Adjunction/SAFT.v`: `SubobjectIndex`, `Cogenerator`, `SAFT`; the separation⇒monic content internalized as `cogenerator_canonical_monic`). Indexed products as discrete-diagram limits (`Structure/Limit/Product.v`: `iprod`/`iprod_proj`/`iprod_ump` over `Instance/Discrete.v`'s `DiscreteCat`); a GAFT integration witness reconstructing Δ ⊣ (×) with the reflector shown `≅ Δ` (`Adjunction/GAFT/Examples.v`). Reflective/coreflective subcategories over `Construction/Subcategory.v` with the full-reflective counit-iso lemma (`Construction/Reflective.v`) and the idempotent-monad correspondence both ways plus the Eilenberg–Moore equivalence (`Construction/Reflective/Idempotent.v`: `IdempotentMonad`, reflective ⟺ idempotent monad, `EM ≃` the local subcategory); orthogonal-subcategory localization (`Construction/Localization.v`: `WLocal`, the full subcategory `C_W`, `reflector_inverts_W`) with the universal property up to natural iso (`Construction/Localization/Universal.v`: `localization_universal`, the orthogonal form — calculus of fractions descoped, ledger 15)
- **Theory/Lawvere.v**: Lawvere theories — the `LawvereTheory` class mirroring the PROP class's relaxed shape (`law_of_nat` naming function + propositional strictness equalities on OBJECTS; bijectivity deliberately not required, consumers state reachability), with `law_pow`/`law_pow_one`; the skeletal base `FinSetOp_Lawvere` on `FinSet^op` whose strictness fields compute by `eq_refl` even at open variables (Instance/FinSet/Lawvere.v); models as Cartesian+Terminal-preserving functors with the model category `Models T C` a full subcategory of the functor category, pack/unpack mutually inverse (Theory/Lawvere/Model.v); Sets-models with the underlying-set functor `ev1` and `ev1_Faithful` under an explicit reachability hypothesis — the honest price of the relaxed class, trivially witnessed on the base by `FinSetOp_reach` (Theory/Lawvere/Sets.v); the finitary-monad connection hypothesis-scoped over a given left adjoint `L ⊣ ev1` — `Lawvere_Monad` via the transparent induced monad, `Lawvere_EM_Comparison`, and `Lawvere_crude_monadicity` re-exposing the crude-monadicity hypotheses verbatim (full equivalence ledger 2; Theory/Lawvere/Monad.v); the PROP-spine bridge — cartesian monoidal/braided/symmetric structure via the CC_* instances and the interpretation tower `Lawvere_PROP_interp` (+Monoidal/Strict/Braided/Symmetric) from the FreePROP universal property under a disclosed strictness hypothesis pack (`coh := eq_refl` on skeletal instances, remaining equalities by nat induction), with the Fox-theorem pointer joining the cartesian and copy/discard spines (Theory/Lawvere/PROP.v)
- **Theory/Multicategory.v**: Symmetric multicategories with zipper single-slot composition — `mcomp {Γ₁ Γ₂ Δ b c} : mhom (Γ₁++b::Γ₂) c → mhom Δ b → mhom (Γ₁++Δ++Γ₂) c` (no heterogeneous-list telescopes), boundary casts `mcast` with the groupoid pack and any-proof law variants, unit laws through a named splice-equation kit, both associativity shapes (nested + disjoint over their boundary equations); the symmetric action `msym` indexed by the Type-valued `tperm` witness (plan erratum: stdlib `Permutation` is Prop with no elimination into Type; `tperm_Permutation` bridges back) with a disclosed SCOPE note (witness-indexed action; symmetric-group descent and slot-crossing equivariance deferred — every in-tree instance satisfies both). Multifunctors with the heterogeneous setoid (Theory/Multicategory/Functor.v); the representable multicategory of a symmetric monoidal category via `tensor_list`/`tfold` folds and a braid-built `perm_arrow`, developed once over an object realization `ob : A → C` — `RepresentableMulticategory` threads UIP-on-object-lists (Grothendieck/Strict precedent) and `ColouredPROP_Multicategory` derives it from the colour decider by axiom-free Hedberg (Theory/Multicategory/Representable.v); the endomorphism operad `pow`/`EndOperad` with the genuine fork-algebra braid action and nat-level UIP normalization (Theory/Multicategory/Endomorphism.v); operads as one-object multicategories with `ohom` accessors and the two-sided presentation round trip (Theory/Multicategory/Operad.v); operad algebras `OperadAlgebra := MultiFunctor` into `EndOperad` with the convenience constructor (+ `alg_act_Build` sanity), the category `OperadAlgebras`, and the Comm example — algebras of the terminal operad in Sets are commutative monoids, both directions, connecting Instance/CMon.v (Theory/Multicategory/Algebra.v)

### Structures (Internal Properties)
- **Structure/Cartesian.v**: Products via universal property
- **Structure/Closed.v**: Exponentials and internal hom
- **Structure/Monoidal.v**: Tensor products with coherence
- **Structure/Monoidal/CopyDiscard.v**: Copy/discard (gs-monoidal) categories — comonoid supply with no naturality; deterministic morphisms and the wide subcategory Det in CopyDiscard/Deterministic.v
- **Structure/Monoidal/Markov.v**: Markov categories (copy/discard + semicartesian); Fox's theorem in Markov/Fox.v (all-deterministic ⟺ cartesian)
- **Structure/Premonoidal.v**: Premonoidal categories over Structure/Binoidal.v — centre Z(C) as a monoidal wide subcategory (Binoidal/Central.v, Premonoidal/Centre.v), Monoidal ⟺ all-central premonoidal (Premonoidal/Monoidal.v), Freyd/effectful categories (Premonoidal/Freyd.v); Kleisli premonoidal structure and thunkability in Monad/Kleisli/{Premonoidal,Commutative}.v and Monad/Thunkable.v; graded monads in Monad/Graded.v; strict premonoidal = monoid in (StrictCat, □) in Instance/StrictCat/Premonoid.v
- **Structure/Monoidal/Drinfeld.v**: The Drinfeld (monoidal) centre `Z(C)` — `HalfBraiding` (a natural family satisfying the half-braiding hexagon), objects `(x, half-braiding)` with intertwiner morphisms (proof-irrelevant witness), `Drinfeld_Monoidal`, `Drinfeld_Braided` (a braided monoidal category with BOTH hexagon identities at full strength), and the forgetful `Drinfeld_Forget`; this is the monoidal centre, distinct from the premonoidal centre of Binoidal/Central + Premonoidal/Centre
- **Structure/Monoidal/StarAutonomous.v**: Star-autonomous categories (definition level) over a genuine general base `SymMonClosed` — symmetric monoidal closed, introduced in-file because the in-tree `ClosedMonoidal` bundles `CartesianMonoidal` (over a cartesian closed base a dualizing object forces a preorder by Joyal's no-go, excluding Rel/FdVect/coherence spaces); provides the dual/linear-negation functor `(- ⇒ ⊥) : C^op ⟶ C`, the double-dual endofunctor, and the `StarAutonomous` class (dualizing object, closed transpose, double-dual iso with naturality), with par/linear-distributivity and the canonicity coherence ledgered
- **Structure/Limit.v**: Limits and colimits
- **Structure/Abelian.v**: The additive-structure spine — zero objects with the tunnelled `zero_mor` (Structure/ZeroObject.v), UMP-form biproducts (Structure/Biproduct.v), commutative-monoid hom-enrichment with opt-in `addition_scope` (Structure/Preadditive.v), the two semiadditivity theorems (Structure/Semiadditive.v: biproducts compute the enrichment; a bicartesian category with invertible coproduct-to-product comparison is preadditive, by Eckmann–Hilton), additive categories with negation (Structure/Additive.v), the elementary fork API `IsEqualizer` (Structure/Equalizer/Fork.v), kernels/cokernels with normality and the cokernel⇒regular-epi bridge (Structure/Kernel.v), and abelian categories with the full epi-mono factorization (`image_mediator_epic` by the Freyd/Borceux chase) assembled as `Abelian_OFS`; the concrete semiadditive witness is CMon (Instance/CMon.v, Instance/CMon/Biproduct.v — commutative monoids over setoids, universe-polymorphic)
- **Structure/Factorization.v**: Orthogonal factorization systems — `MorphismClass` vocabulary (Theory/Morphisms/Classes.v), orthogonal lifting `e ⫫ m` with left-class closure (Theory/Orthogonality.v), `Factorization`/`OFS` with uniqueness up to unique iso and the Fact.v comparison, strong epis (Factorization/StrongEpi.v: composition, cancellation, split ⇒ strong, strong+mono ⇒ iso); pullback pasting/stability toolkit in Theory/Morphisms/Stability.v (apex-pinned `IsPullback`, pasting both ways, monos/isos pullback-stable, `pullback_transport`); elementary cofork API `IsCoequalizer` with Colimit conversions in Structure/Coequalizer.v; regular categories in Structure/Regular.v (kernel pairs, `RegularEpi`, stability field) with the (RegularEpi, Mono) image factorization `Regular_OFS` in Regular/Factorization.v (double-cover monicity argument); concrete images in Instance/Sets/Image.v
- **Structure/Coend.v**: The coend calculus — covariant coend accessors (`coend_obj`, `coend_inj`, the cowedge condition, `coend_ump`/`coend_med`/`coend_med_eq`, and the smart constructor `Build_Coend`) over the definitional `Coend F := @End (C^op)(D^op)(F^op)`; the end and coend in `Sets` funext-free (Instance/Sets/End.v as the subsetoid of compatible families, Instance/Sets/Coend.v as the inductive setoid quotient by exactly the dinaturality relation); the ninja (co-)Yoneda reductions and the Fubini interchange (Theory/Coend/{Yoneda,Fubini}.v); profunctors `C ⇸ D := C^op ∏ D ⟶ Sets` with representables, composition by the coend `∫^d P(c,d) × Q(d,e)`, the unit/associator laws, and `representable_adjunction : (F ⊣ U) ↔ (Repr_left F ≅ Repr_right U)` (Theory/Profunctor.v, Construction/Profunctor/{Compose,Laws}.v, Theory/Profunctor/Adjunction.v); Day convolution `∫^{a,b} C(a ⨂ b, -) × F a × G b` with unitors and associator (Construction/Day.v)

### Constructions (External Combinators)
- **Construction/Opposite.v**: Op categories with auto-duality
- **Construction/Product.v**: Product categories C × D
- **Construction/Comma.v**: Comma categories (F ↓ G)
- **Construction/Slice.v**: Slice C/c and coslice c/C
- **Construction/PROP/**: Free PROP on a signature, complete spine — shared Monoidal/Braided/Symmetric/Strict instances, bundled FreePROP, interpretation with universal property (Interp.v, Universal.v), models (Algebra.v), presented PROPs by generators and equations with factorization (Presentation.v, Presentation/Universal.v), Tietze/definitional extensions (Tietze.v); generic hom-congruence quotients in Construction/Quotient.v; skeletal FinSet with computable coproducts in Instance/FinSet.v
- **Construction/ColouredPROP/**: Coloured PROPs, complete — coloured signatures and terms over list-of-colour boundaries, free coloured PROP instantiating the class with definitional coherence, interpretation + universal property, presentations, colour base change with identity/composition functoriality laws up to hom_cast (pseudofunctor coherence cells not formalized), per-colour selective supplies (Fong–Spivak) with linear fan-out discipline, and the LNL bridge; generic comonoid tensor in Theory/Algebra/Comonoid/Tensor.v
- **Construction/Funny.v**: Funny tensor product C □ D — same objects as C × D, morphisms freely generated by one-sided steps with no interchange law; satellites in Construction/Funny/ (bifunctor, unitors, swap, associator, comparison to ×, unnatural-transformation hom ⟦-,-⟧, closed structure), symmetric monoidal instance on StrictCat in Instance/StrictCat/Funny.v
- **Construction/FAlg.v** / **Construction/FCoalg.v**: The categories of F-(co)algebras — `FAlg F` bundles carriers `∃ a, FAlgebra F a` with the `FAlgHom` commuting-square hom class; `FCoalg F := (FAlg (F^op))^op` by duality with covariant accessors and `FCoalg_Forget`. The initial-algebra / final-coalgebra theory rides these: the ω-chain `Chain F : Omega ⟶ C` (Construction/Chain.v) over the ordinal ω (Instance/Omega.v, a Type-valued `le_t` order avoiding stdlib `le`, with `Cochain` by duality); Lambek's lemma both ways (`lambek : F μ ≅ μ`, `lambek_final : ν ≅ F ν`, Theory/Lambek.v); catamorphism/anamorphism universal properties (`cata`/`ana` with commutes/unique/fusion, Theory/Recursion.v); Adámek's theorem over the honest `AdamekData` hypothesis (`adamek : AdamekData → Initial (FAlg F)`, Theory/Adamek.v — the `PreservesColimit → AdamekData` leg-agreement bridge is withheld, ledger 17) with the `Cocomplete` corollary and the `NatF` note (Theory/Adamek/Corollaries.v); concrete witnesses `list A` as the initial `ListF`-algebra on Coq (Instance/Coq/Lists.v, axiom-free) and streams as the final `StreamF`-coalgebra on Sets via bisimilarity (Instance/Sets/Streams.v)

- **Construction/Karoubi.v**: The Karoubi envelope — objects are idempotents, the identity of `(x, e)` is `e` itself; fully faithful embedding, every envelope idempotent splits (`SplitIdempotent` witnesses). Universal property in Karoubi/Universal.v: `IdempotentsSplit` (chosen splittings, satisfied by every envelope), `Karoubi_Extend` along the embedding with `Extend ∘ Embed ≈ G` and uniqueness up to `≈`, `CauchyComplete := IdempotentsSplit`, and split idempotents ⇒ the embedding is an equivalence (forward direction); Sets is Cauchy complete (Instance/Sets/Karoubi.v via the fixed-point sub-setoid)
- **Construction/Grothendieck.v**: Displayed categories, fibrations, and the Grothendieck construction — `Displayed C` (Theory/Displayed.v) as the primitive with `dtransport` and the interchange fields `dtransport_comp_l`/`dtransport_comp_r` (underivable from the base laws by a 2-cocycle countermodel in the header, and load-bearing — without them the total category's composition is not a congruence); the total category `Total`/`Total_Proj` (Construction/Displayed/Total.v); fibrations in both presentations (Theory/Fibration.v: `DCartesian`, `Cleaving`, `CartesianMorphism`, `ClovenFibration`, `SplitCleaving`, opfibrations by `Displayed_op`); the coherent pseudofunctor-lite `IndexedCat` (Construction/Indexed.v, with an honesty note on why a bare `Functor B Cat` is insufficient in a setoid library — a central-automorphism twist of `fmap_comp` breaks the cross-application cocycle); the Grothendieck construction `Grothendieck_Displayed`/`Grothendieck`/`Grothendieck_Proj` with every displayed law discharged from the `IndexedCat` coherence pack; the projection is a split opfibration (Construction/Grothendieck/Fibration.v); fibre categories and the fibre equivalence `fiber_grothendieck_equiv` (Construction/Grothendieck/Fiber.v); constructors from strict functors under fibrewise UIP with an inline axiom-free Hedberg (Construction/Grothendieck/Strict.v: `IndexedCat_of_StrictFunctor`, `Constant_IndexedCat`, `Grothendieck_Constant_iso : Grothendieck (constant D) ≅[Cat] B ∏ D`); the fibred-to-indexed round-trip `IndexedCat_of_SplitCleaving` with `RoundTrip_Comparison` fully faithful and the full `RoundTrip_Equivalence` (Construction/Grothendieck/RoundTrip.v, over a split opfibration of P — the split laws are provably inert, so a cloven cleaving already suffices); and the codomain displayed category with cartesian-lifts-iff-pullbacks `codomain_cleaving`/`codomain_cleaving_pullbacks` (Construction/Displayed/Codomain.v)

- **Construction/Enriched/Natural.v**: The enriched upgrade over Construction/Enriched.v — V-natural transformations `EnrichedTransform` with the unitor-conjugated V-naturality square `enaturality` (typed-equality `<< A ~~> B >>` form) and componentwise setoid; identity/composite enriched functors and both whiskerings (Construction/Enriched/Compose.v); the ordinary category of V-functors `Enriched_Fun` with vertical composition by `ecompose` under the inverse unitor at I (Construction/Enriched/Fun.v — genuine V-category hom-OBJECTS need ends in the base, ledger 11); V=Sets recovers ordinary category theory at all three levels, the transformation level being `EnrichedTransform_is_Transform` over the two in-tree `Defined` round trips (Construction/Enriched/Sets.v); enrichment in the walking arrow = preorders both ways with enriched functors = monotone maps (`Enriched_Two_preorder`, `EnrichedFunctor_Two_monotone`, Construction/Enriched/Two.v, over Instance/Two/Monoidal.v's cartesian `Two_Monoidal`). Sets-weighted (co)limits by representability with `HomDiagram`/`WeightedLimit`/`WeightedColimit` and the conical case `conical_weighted` proved in both directions (Structure/Limit/Weighted.v; V-valued weights need ends, ledger 11)

### Concrete Instances
- **Instance/Sets.v**: Category of setoids (not strict sets!)
- **Instance/Coq.v**: Category of Coq types and functions
- **Instance/Cat.v**: Category of categories
- **Instance/Fun.v**: Functor categories [C, D]
- **Instance/Lambda/**: Full lambda calculus formalization

### Applied Programming (Theory/Coq/)
Bridges pure theory with practical Coq programming:
- Applicative functors proven via monoidal functors
- Traversable functors with laws
- Monad transformers with coherence conditions

## Critical Design Patterns

### Equivalence Over Equality
Never use `=` for morphisms. Always use `≈`:
```coq
(* WRONG *)
Lemma foo : f ∘ id = f.

(* RIGHT *)
Lemma foo : f ∘ id ≈ f.
```

### Proper Morphisms
All operations must respect equivalence:
```coq
Program Instance Foo_Proper {C : Category} :
  Proper (equiv ==> equiv ==> equiv) (@foo C).
```

### Notation Precedence
- `~>` morphisms (level 90)
- `∘` composition (level 40, left associative)
- `⟶` functors between categories
- `⟹` natural transformations

### Proof Automation
Standard proof pattern:
```coq
Proof.
  intros.
  cat.          (* tries simplification + rewriting *)
  proper.       (* if proving Proper *)
  equivalence.  (* if proving Equivalence *)
Qed.
```

## Common Development Tasks

### Adding a New Category Instance
1. Define objects and morphisms
2. Define equivalence relation on morphisms (setoid)
3. Prove it forms a category (id, compose, laws)
4. Place in Instance/ directory
5. Add to _CoqProject

### Proving Functoriality
1. Define object mapping F_obj
2. Define morphism mapping F_map
3. Prove F_map respects equivalence
4. Prove F preserves id and composition
5. Use `Program Instance` to manage obligations

### Establishing Adjunctions
1. Define functors F : C ⟶ D and G : D ⟶ C
2. Define unit η : Id ⟹ G ○ F
3. Define counit ε : F ○ G ⟹ Id
4. Prove triangle identities
5. Or use hom-set adjunction definition

## References and Learning

When working with specific concepts, reference:
- **nLab**: https://ncatlab.org/nlab/show/[concept_name]
- **README.md**: Contains detailed notation guide (lines 193-247)
- **EXPLORATION_INDEX.md**: Quick navigation to key files
- **EXPLORATION_SUMMARY.md**: Mathematical concept guide

## Versioning

Default version: Rocq 9.1 (flake.nix line 187)
Supported: Coq 8.14-8.20, Rocq 9.0-9.1
Equations dependency required for some parts (versions matched to Coq)

## Testing Individual Theorems

To test a specific construction:
```bash
# Extract just the files needed
coqdep -R . Category Theory/MyConstruction.v | grep -v "^#"

# Compile dependencies first
make Theory/Category.vo Theory/Functor.vo

# Then compile your file
coqc -R . Category Theory/MyConstruction.v
```