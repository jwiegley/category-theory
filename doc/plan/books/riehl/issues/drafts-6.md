```yaml
title: "Riehl 6.1: Kan extensions as representations — the candidate category, terminality, and essential uniqueness"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.1:def-unit-counit, riehl:6.1:exii, riehl:6.1:exv]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (author's recompiled copy — **not** the Dover/AMS pagination; printed = PDF − 20), §6.1 "Kan extensions". The unnumbered boldfaced paragraph naming the unit and counit and restating Definition 6.1.1 as a representability statement, printed pp. 222–223 (PDF pp. 242–243); Exercise 6.1.ii and Exercise 6.1.v, printed p. 224 (PDF p. 244). Items: `riehl:6.1:def-unit-counit`, `riehl:6.1:exii`, `riehl:6.1:exv`.

Paraphrase: the 2-cell of a left Kan extension is called its **unit** and that of a right Kan extension its **counit**; the defining property says exactly that composing with the unit is a bijection from natural transformations out of the extension to natural transformations out of the restricted diagram, so a left Kan extension of `F` along `K` is precisely a *representation* of the functor sending `G` to the natural transformations `F ⇒ G K`. Dually, a right Kan extension is a *terminal* object of the category of candidate pairs. Two consequences are set as exercises: any two left Kan extensions of the same functor are isomorphic by a *unique* isomorphism compatible with the units, and the right Kan extension is the terminal object of an explicitly describable category.

## Background

Every universal property is a representability statement, and the Kan-extension one is no exception: extensions of `F` along `K` are the elements of a functor on the target functor category, and the extension itself represents it. See [nLab: Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and [nLab: representable functor](https://ncatlab.org/nlab/show/representable+functor).

## Current state in the library

The `∃!`-form of the universal property is fully present; the representability and terminality packaging is not.

- `Theory/Kan/Extension.v:234` — `Class LocalLeftKan (X : A ⟶ C) := { LocalLan : B ⟶ C; lan_transform : X ⟹ LocalLan ◯ F; ump_lan (M : B ⟶ C) (ε : X ⟹ M ◯ F) : ∃! δ, ε ≈ δ ⊲ F ∙ lan_transform }`, and dually `LocalRightKan` at `:154` with `ran_transform` / `ump_ran`.
- The file already **names** these transformations Riehl's unit and counit in its own comments (`:157`, `:237`), so the naming half of the unnumbered definition is in force and must not be reintroduced under a new name.
- The `∃!` is `Lib/Setoid.v:97`'s `Unique` (witness + property + uniqueness up to `≈`), **not** Coq's stdlib `unique` over Leibniz equality; the verification pass confirmed this, so `ump_lan` already says that the composition map `δ ↦ (δ ⊲ F) ∙ η` has singleton fibres — i.e. exactly Riehl's bijection, in the sanctioned setoid rephrasing.

What is missing:

1. **The representing functor is never formed.** Nothing in the tree builds `[A,C](X, − ◯ F) : [B,C] ⟶ Sets`, and no lemma identifies a `LocalLeftKan X` with a representation of it in the sense of `Functor/Representable.v:46` (`Class Representable … repr_obj : C; represented : [Hom repr_obj,─] ≅ F`); that class is applied nowhere near `Theory/Kan/Extension.v`. **Sharpening from the verification pass:** the *global* form of the representability statement genuinely is in tree — `lan_adjoint : Lan ⊣ Induced` (`Theory/Kan/Extension.v:222`) over `Theory/Adjunction.v:130`'s `adj {x y} : Isomorphism Sets (hom C (F x) y) (hom D x (U y))` with `to_adj_nat_l` / `to_adj_nat_r` *is* the natural bijection in `M`. But it holds only under the much stronger hypothesis that the extension of **every** diagram along `F` exists. It is the single-extension form that has no counterpart.
2. **The category of candidate pairs is never formed.** It is `Induced ↓ =(X)` (for the right-hand statement) and `=(X) ↓ Induced` (for the left), constructible from `Construction/Comma.v` but never built; `rg 'Terminal.*↓|↓.*Terminal'` returns 0 hits, so no comma category in the tree carries a `Terminal` instance. `Theory/Universal/Arrow.v:127` packages only the initial direction (`arrow_initial : @Initial (=(c) ↓ F)`) and there is no couniversal dual (0 hits for `couniversal`/`CoUniversalArrow`). A wording correction the verifier recorded: the comment at `Theory/Universal/Arrow.v:23–24` merely states what the dual *is*; it does not say the dual is undeveloped — the non-development is established by search, not by that comment.
3. **No uniqueness statement about Kan extensions exists.** `Theory/Adjunction.v:404` — `Theorem left_adjoint_iso `(G : D ⟶ C) (F F' : C ⟶ D) : F ⊣ G → F' ⊣ G → F ≈ F'` — specialises to the *global* `Lan` (since `Class LeftKan` is literally an adjoint of `Induced`), but it is never so specialised, it says nothing about the local extension of a single functor, its proof (`:406–440`) builds the isomorphism from the adjunct of the identity **without** ever stating compatibility with the units, and it does not prove the comparison isomorphism itself unique. Those last two clauses are precisely the content of Riehl's exercise.
4. Riehl's size caveat (`E^C`, `E^D` possibly not locally small, so one passes to a larger universe) has no in-tree analogue: the library's hom-setoids are universe-polymorphic and the point never arises.

## Work to be done

Suggested module: `Theory/Kan/Representation.v` (new), with a small addition to `Theory/Universal/Arrow.v`.

1. Build the candidate categories for a fixed `X : A ⟶ C` along `F : A ⟶ B` as the comma categories `Induced ↓ =(X)` and `=(X) ↓ Induced` over `Construction/Comma.v` — objects the pairs `(M, μ)`, morphisms the 2-cells commuting with the structure maps. Do not introduce a bespoke record.
2. Prove `LocalRightKan X` is exactly a `Terminal` object of the first and `LocalLeftKan X` exactly an `Initial` object of the second. `ump_ran` / `ump_lan` are terminality/initiality unwound, so both directions are short. Add the couniversal-arrow dual to `Theory/Universal/Arrow.v` while you are there — its absence is why no comma category in the tree currently carries a `Terminal` instance.
3. Form `[A,C](X, − ◯ F) : [B,C] ⟶ Sets` (the hom-functor of `Instance/Fun.v` postcomposed with `Induced`) and prove `LocalLeftKan X` is equivalent to a `Representable` structure on it; dually for `LocalRightKan` over `([B,C])^op`. Derive the statement from `lan_adjoint` in the case where the global extension happens to exist, so the tree exhibits one fact at two strengths rather than two unrelated facts.
4. Prove essential uniqueness: any two `LocalLeftKan` structures on the same `X` are related by a natural isomorphism `L ≅ L'` satisfying `(iso ⊲ F) ∙ η ≈ η'`, and that isomorphism is the **unique** natural transformation with that property; dually for `LocalRightKan`. Derive it from step 2 (initial and terminal objects are unique up to unique isomorphism), not by hand.
5. Record in the header that the unit/counit names already live on `lan_transform` / `ran_transform`, and that Riehl's local-smallness caveat is vacuous here because the hom-setoids are universe-polymorphic.

In-tree donors: `Theory/Kan/Extension.v`, `Construction/Comma.v`, `Functor/Representable.v`, `Functor/Diagonal.v` (the `=( − )` notation), `Instance/Fun.v`, `Theory/Universal/Arrow.v`, `Structure/Initial.v` / `Structure/Terminal.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.1 (the unit/counit paragraph, printed pp. 222–223; Exercises 6.1.ii and 6.1.v, printed p. 224), paraphrased; `≈` used for every morphism equality, never `=`
- [ ] The candidate categories are built over `Construction/Comma.v` and not as new records
- [ ] `LocalRightKan X` proved equivalent to a `Terminal` structure on the candidate category, and `LocalLeftKan X` to an `Initial` one, in both directions
- [ ] The couniversal-arrow dual of `Theory/Universal/Arrow.v`'s `UniversalArrow` is added
- [ ] `[A,C](X, − ◯ F)` is formed and `LocalLeftKan X ↔ Representable` proved, with the global `lan_adjoint` case derived from it (or vice versa) rather than duplicated
- [ ] Essential uniqueness proved with **both** clauses Riehl asks for: compatibility with the units, and uniqueness of the comparison isomorphism
- [ ] The header records that `lan_transform`/`ran_transform` already carry the unit/counit names, and that the local-smallness caveat does not arise
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (the Kan-extension entry gains a representation/uniqueness API)

## Verification

```sh
nix develop --command coqc -R . Category Theory/Kan/Representation.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Kan.Representation. Print Assumptions lan_representable. Print Assumptions ran_terminal. Print Assumptions lan_unique." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the statement matches Riehl §6.1 up to paraphrase; uniqueness is proved for the **local** (single-diagram) extension and not merely re-exported from `left_adjoint_iso`; the unit-compatibility clause is present; the representing functor is the honest `[A,C](X, − ◯ F)` and not a restatement of the adjunction.

## Dependencies

None in catalog. Related: #590 supplies the global adjoint form of the same bijection, and this issue's local form should be stated so that #590's assembly consumes it.

<!-- catalog: {"ids":["riehl:6.1:def-unit-counit","riehl:6.1:exii","riehl:6.1:exv"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 6.1/6.2: Kan extensions along the inclusion of the parallel pair into the free fork"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.1:example3, riehl:6.2:exi]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.1 Example 6.1.3, printed pp. 220–221 (PDF pp. 240–241) — new in the second edition — and §6.2 Exercise 6.2.i, printed p. 232 (PDF p. 252). Items: `riehl:6.1:example3`, `riehl:6.2:exi`.

Paraphrase: let the domain be the walking parallel pair and the codomain the free category on a fork (a parallel pair together with an arrow under it), with the fully faithful inclusion between them. A diagram on the parallel pair is a pair of parallel arrows in the target. When that pair has a coequalizer, the coequalizer fork is the left Kan extension along the inclusion: the extension is a strict extension so the unit may be taken to be the identity, and the factorization property is exactly the coequalizer's universal property. Dually, when the target has a terminal object, the unique fork to it is the right Kan extension, its universal property being terminality. The exercise asks to confirm that both extensions are *pointwise*, by checking that the (co)limit formulae recover this description.

## Background

The smallest interesting Kan extension: extending a parallel pair along the inclusion into the free fork manufactures the coequalizer, so a familiar colimit appears as an extension problem. See [nLab: Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and [nLab: coequalizer](https://ncatlab.org/nlab/show/coequalizer).

## Current state in the library

The domain shape exists; the codomain shape does not, and no Kan extension is ever computed in a concrete category.

- `Instance/Parallel.v:80` — `Program Definition Parallel : Category` is the walking parallel pair (registered `_CoqProject:221`), and `Structure/Coequalizer.v:188` `colimit_coequalizes` / `:226` `coequalizer_is_coequalizer` already relate `Parallel`-shaped colimits to coequalizers.
- There is **no free fork category** (a parallel pair together with a cone under it): `rg -i 'free fork|walking fork|fork categ'` returns 0 hits, and the shape categories in tree are exactly `One`, `Two`, `Zero`, `Parallel`, `Roof`, `Discrete`, `Omega`, `Shapes`. "Fork" in tree means either the cartesian pairing `⟨f,g⟩` (`fmap_fork`, `fork_comp`) or the elementary (co)equalizer fork APIs (`Structure/Equalizer/Fork.v:52` `IsEqualizer`, `:176` `fork_cone`, `:187` `limit_equalizes`; `Structure/Coequalizer.v:52` `IsCoequalizer`) — neither is an index category with a cone object.
- No statement anywhere connects a coequalizer or a terminal object to a Kan extension (`coequalizer` ∩ `Kan` → 0 hits), and the only consumer of the Kan classes in the whole tree is `Structure/Limit/Kan/Extension.v`'s `Kan_Limit`, which is the right Kan extension along `Erase J : J ⟶ 1` — a different functor to extend along.
- The exercise's own vocabulary is unavailable: pointwiseness is not defined in tree, and `Theory/Kan/Extension.v:148` in fact calls `LocalRightKan` the "**pointwise-free**" local extension, while `:74–79` concedes that the comma-category (co)limit formulas are "a bridge not yet formalized".

## Work to be done

Suggested modules: `Instance/Fork.v` (the shape) and `Instance/Fork/Kan.v` (the computation).

1. Build the free category on a fork: three objects `a`, `b`, `c`; generating arrows `f, g : a ⟶ b` and `h : b ⟶ c`; morphisms the identities, `f`, `g`, `h`, `h ∘ f`, `h ∘ g`, with composition and the category laws proved. Define `K : Parallel ⟶ Fork` picking out `f, g` and prove it fully faithful.
2. Given `E` and a diagram `F : Parallel ⟶ E` whose pair has a coequalizer, construct a `LocalLeftKan` of `F` along `K` whose value at `c` is the coequalizer object, with the unit taken to be the identity (a *strict* extension — state it as such, since Riehl uses this example to make that point). Derive the `ump_lan` obligation from the coequalizer universal property of `Structure/Coequalizer.v` rather than re-proving it.
3. Dually, given a terminal object in `E`, construct a `LocalRightKan` of `F` along `K` whose value at `c` is that terminal object, deriving `ump_ran` from terminality.
4. Discharge the exercise: verify both extensions are pointwise by computing the comma categories `K ↓ c` and `c ↓ K` and showing the (co)limit formula reproduces the construction of steps 2 and 3 — `K ↓ c` is the whole of `Parallel` extended by the identity at `c`, so the colimit over it is exactly the coequalizer, and `c ↓ K` is empty above `c`, so the limit is the terminal object.
5. Record in the header that this is the tree's first worked Kan-extension computation and the first inhabitant of `LocalLeftKan`/`LocalRightKan` at a non-trivial functor.

In-tree donors: `Instance/Parallel.v`, `Structure/Coequalizer.v`, `Structure/Equalizer/Fork.v`, `Structure/Terminal.v`, `Theory/Kan/Extension.v`, `Construction/Comma.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.1 Example 6.1.3 (printed pp. 220–221) and §6.2 Exercise 6.2.i (printed p. 232), paraphrased; `≈` on morphisms, never `=`
- [ ] The free fork category is constructed with its laws proved, and `K : Parallel ⟶ Fork` proved fully faithful
- [ ] `LocalLeftKan` inhabited with the coequalizer as its value and the **identity** unit, and the strictness of the extension stated explicitly
- [ ] `LocalRightKan` inhabited with the terminal object as its value
- [ ] Pointwiseness verified through the comma-category (co)limit formula, not by an independent hand argument
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] docs/INHABITATION.md updated: the Kan-extension classes acquire a concrete non-terminal witness

## Verification

```sh
nix develop --command coqc -R . Category Instance/Fork.v Instance/Fork/Kan.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Fork.Kan. Print Assumptions fork_lan_coequalizer. Print Assumptions fork_ran_terminal." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the fork category really is free on a fork (no extra composites); the unit is the identity and this is asserted, not assumed; the pointwiseness check goes through the comma formula.

## Dependencies

Depends on: #589 (the pointwise (co)limit formula for Kan extensions — the tool the exercise requires)
Depends on: #599 (pointwise Kan extensions — the predicate the exercise's conclusion is stated in)
Depends on: #591 (fully faithful `K` gives an invertible unit — the general reason the unit here may be taken to be the identity)

<!-- catalog: {"ids":["riehl:6.1:example3","riehl:6.2:exi"],"deps":["#589","#599","#591"]} -->

---8<---

```yaml
title: "Riehl 6.1/6.2: Extension along a fully faithful functor — the walking-triangle example and a non-pointwise counterexample"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.1:exiv, riehl:6.2:example15]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.1 Exercise 6.1.iv, printed p. 224 (PDF p. 244), and §6.2 Example 6.2.15, printed p. 231 (PDF p. 251) — the latter new in the second edition. Items: `riehl:6.1:exiv`, `riehl:6.2:example15`.

Paraphrase: (a) for the functor from the walking arrow into the walking commutative triangle that picks out the diagonal composite, both Kan extensions of an arbitrary arrow-shaped diagram exist and can be written down explicitly; both genuinely extend the original diagram, because the functor is fully faithful, yet the two extensions are not in general isomorphic to one another. (b) A counterexample showing the pointwise hypothesis in the "fully faithful extensions really extend" corollary is essential: for the fully faithful inclusion of a two-object discrete category into the walking span, and a five-object target with four non-identity arrows, there is exactly one candidate pair, it does satisfy the left Kan universal property, and yet its unit components are not invertible — because it is not pointwise, the target having no initial object.

## Background

Extension along a fully faithful functor is the case where one expects a Kan extension to be an honest extension. It is, provided the extension is pointwise; these two examples delimit the statement from both sides. See [nLab: Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and [nLab: pointwise Kan extension](https://ncatlab.org/nlab/show/pointwise+Kan+extension).

## Current state in the library

Both shape categories are (nearly) available; nothing about them is connected to Kan extensions.

- The walking commutative triangle exists as `Theory/Metacategory.v:413` — `Definition Three : Category := FromArrows ThreeArrows`, with the arrow table at `:396` — and the walking arrow as `Instance/Two.v:134` `Program Definition _2 : Category`. **No functor `_2 ⟶ Three` is defined anywhere.**
- **Orientation warning established by the verification pass.** Under `Theory/Metacategory.v:143`'s own convention (`composite f g h := M.MapsTo (f,g) h pairs`, i.e. `f ∙ g = h`), the entries of `ThreeArrows` make the generating arrows run `3 : 1 ⟶ 0`, `4 : 2 ⟶ 1` and `5 = 3 ∙ 4 : 2 ⟶ 0`. It is the same walking commutative triangle Riehl uses, but with the arrows named in the *opposite* direction from what a naive reading of the table suggests; any `d¹ : _2 ⟶ Three` must be written against that orientation. Note also that `Theory/Metacategory.v:533`'s `FromThree` sits inside an open comment block and is therefore not available.
- `Instance/Roof.v:28` — `Inductive RoofObj := RNeg | RZero | RPos` — is the walking span, the shape the counterexample extends into. The five-object target category of the counterexample does not occur anywhere.
- No worked Kan-extension example or counterexample exists in the tree at all: the only consumers of the Kan classes are `Structure/Limit/Kan/Extension.v`'s `Kan_Limit` and the abandoned `left_adjoints_preserve` sketch (`Theory/Kan/Extension.v:386`, three `admit`s, `Abort.` at `:438`, honestly disclosed at `:376–384`).
- No theorem anywhere hypothesises anything about the functor one extends along (fully faithful or otherwise), and no statement asserts that a Kan-extension unit or counit is invertible. Since pointwiseness itself is undefined in tree, the very distinction the counterexample draws is currently inexpressible.

## Work to be done

Suggested module: `Instance/Kan/Examples.v` (new).

1. Define `d¹ : _2 ⟶ Three` picking out the diagonal composite, against the orientation actually used by `ThreeArrows` (or build the triangle directly in `Instance/` and disclose the choice in the header — the arrows-only presentation is workable but its orientation is a documented trap).
2. For an arbitrary `f : _2 ⟶ C`, construct both `LocalLeftKan f` and `LocalRightKan f` along `d¹` explicitly (no (co)completeness hypothesis is needed: the comma categories involved are trivial), prove the unit and counit invertible, and exhibit a concrete `C` in which the two extensions are **not** isomorphic — so a fully faithful `K` guarantees that an extension extends, but not that it is unique across handedness.
3. Define the five-object category of Example 6.2.15 (objects `L, M, R, L', R'`, non-identity arrows `L ⟶ L'`, `M ⟶ L'`, `M ⟶ R'`, `R ⟶ R'`, no further composites) and the fully faithful `K` from the two-object discrete category into `Roof`. Prove the described pair is the **unique** candidate and that it satisfies the `LocalLeftKan` universal property, and prove its unit components are not invertible.
4. Prove that this extension is **not** pointwise, by exhibiting the comma-category colimit that the pointwise formula would require and showing it does not exist (the target has no initial object). Cross-reference: this is exactly why #591's corollary carries the pointwise hypothesis.
5. Record in the header Riehl's Remark 6.1.2 in full: extensions along a fully faithful functor do extend when pointwise, and conversely a strict on-the-nose extension need not be a Kan extension at all — the second half's group-theoretic witness is carried by #987.

In-tree donors: `Instance/Two.v`, `Instance/Roof.v`, `Theory/Metacategory.v`, `Theory/Kan/Extension.v`, `Construction/Comma.v`, `Structure/Limit.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.1 Exercise 6.1.iv (printed p. 224) and §6.2 Example 6.2.15 (printed p. 231), paraphrased; `≈` on morphisms, never `=`
- [ ] `d¹ : _2 ⟶ Three` defined against the documented `ThreeArrows` orientation (or the triangle rebuilt, with the choice justified in the header)
- [ ] Both extensions along `d¹` constructed explicitly, units/counits proved invertible, and a target exhibited in which they are not isomorphic to each other
- [ ] The five-object counterexample category and the unique candidate pair constructed; the `LocalLeftKan` universal property **proved**, and the non-invertibility of its unit **proved**
- [ ] Non-pointwiseness proved by exhibiting the missing comma-category colimit
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Instance/Kan/Examples.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Kan.Examples. Print Assumptions d1_lan. Print Assumptions d1_ran. Print Assumptions nonpointwise_lan_unit_not_iso." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the counterexample's candidate pair is proved unique rather than asserted; non-invertibility is a proof, not a `Fail`; the pointwise obstruction is identified as the absent colimit.

## Dependencies

Depends on: #591 (fully faithful `K` and the invertible unit/counit — the statement these examples delimit)
Depends on: #599 (the pointwise predicate, without which "not pointwise" cannot be stated)
Depends on: #589 (the (co)limit formula used to exhibit the missing colimit)

<!-- catalog: {"ids":["riehl:6.1:exiv","riehl:6.2:example15"],"deps":["#591","#599","#589"]} -->

---8<---

```yaml
title: "Riehl 6.1/6.2: The augmented simplex category and the adjoint triples on simplicial sets — augmentation, truncation, skeleton and coskeleton"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.1:example8, riehl:6.2:example13]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.1 Example 6.1.8, printed pp. 223–224 (PDF pp. 243–244), and §6.2 Example 6.2.13, printed p. 230 (PDF p. 250). Items: `riehl:6.1:example8`, `riehl:6.2:example13`.

Paraphrase: the simplex category is the full subcategory of the augmented simplex category omitting the initial ordinal, so presheaves on the two are simplicial sets and augmented simplicial sets; restriction along the inclusion has both adjoints, the left one augmenting a simplicial set by its set of path components and the right one by the trivial augmentation at the one-point set. Likewise, restriction along the inclusion of the full subcategory on the first `n+1` ordinals is `n`-truncation; since sets are complete and cocomplete both Kan extensions exist, the composite comonad is the `n`-skeleton and the composite monad the `n`-coskeleton, and skeleton is left adjoint to coskeleton, as happens for any comonad and monad arising from one adjoint triple.

## Background

Truncation, skeleton and coskeleton are the standard example of an adjoint triple obtained by restriction along an inclusion of index categories, and they are Kan extensions by construction. See [nLab: simplicial set](https://ncatlab.org/nlab/show/simplicial+set), [nLab: augmented simplicial set](https://ncatlab.org/nlab/show/augmented+simplicial+set) and [nLab: simplicial skeleton](https://ncatlab.org/nlab/show/simplicial+skeleton).

## Current state in the library

Nothing. Every simplicial mention in the tree is background prose.

- `rg -i 'simplicial|simplex|Delta_|skeleton|coskeleton|truncat|augmented'` hits only comment blocks: `Theory/Kan/Extension.v:47,91`; `Instance/FinSet.v:87,89` (remarking that presheaves on `FinSet` are Grandis' augmented symmetric simplicial sets and that the simplex category embeds into `FinSet` — an aspiration, nothing built); `Structure/Coend.v:113`; `Construction/Enriched.v:72`; `Comonad/Core.v:103` and `Comonad/Coalgebra.v:100` (the simplicial bar resolution); `Instance/Two.v:81`; `Structure/Group.v:47`. `rg -nw 'Delta'` returns 0 hits and `coskeleton` returns 0 hits; `ls Instance/` shows no `Delta.v`, `Simplex.v` or `sSet.v`.
- `Instance/FinSet.v:116` builds `FinSet` with **arbitrary** functions, not monotone maps, so it does not contain the simplex category by accident.
- The abstract half is missing too: `rg -in 'comonad.*left adjoint.*monad|induced comonad.*monad'` returns 0 hits, so even the general statement that the comonad and the monad of one adjoint triple are adjoint has no in-tree form, although `Adjunction_Comonad` (`Comonad/Duality.v:170`) and `Adjunction_Induced_Monad` (`Monad/Comparison.v:123`) exist separately. That general statement is filed as #743.
- No `LeftKan`/`RightKan` instance exists anywhere in the tree, so no restriction functor has ever been given an adjoint.

## Work to be done

Suggested modules: `Instance/Delta/Augmented.v` and `Instance/Delta/Truncation.v`.

1. Over #225's simplex category, build the augmented simplex category (all finite ordinals including the initial one, order-preserving maps) and the full inclusion omitting exactly the initial object; prove it fully faithful.
2. Build, for each `n`, the full subcategory on the first `n+1` ordinals and its inclusion, and define `n`-truncation as restriction along it between the presheaf categories of #515.
3. Instantiate #590 at both inclusions: sets are complete and cocomplete and the index categories are small, so both adjoints exist and are pointwise. Give them names.
4. Identify the left adjoint along the augmentation inclusion with the path-components functor — computed by #589's colimit formula as the coequalizer of the two face maps out of the 1-simplices — and the right adjoint with the trivial augmentation at the one-point set.
5. Define `sk n` as the composite comonad and `cosk n` as the composite monad of the truncation triple, unfold both by #589's formulae, and derive `sk n ⊣ cosk n` from #743.

In-tree donors: `Instance/Fun.v` (presheaf categories), `Structure/Coequalizer.v`, `Theory/Kan/Extension.v`, `Comonad/Duality.v`, `Monad/Comparison.v`, `Construction/Subcategory.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.1 Example 6.1.8 (printed pp. 223–224) and §6.2 Example 6.2.13 (printed p. 230), paraphrased; `≈` on morphisms, never `=`
- [ ] The augmented simplex category and the truncation subcategories are constructed, with both inclusions proved fully faithful
- [ ] Both adjoint triples obtained by **instantiating** the general existence theorem, not by bespoke constructions
- [ ] The left adjoint along the augmentation inclusion identified with path components and the right adjoint with the trivial augmentation, both proved
- [ ] `sk n` and `cosk n` defined as the composite comonad/monad and `sk n ⊣ cosk n` proved
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms of docs/AXIOMS.md
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] docs/INHABITATION.md updated: the Kan-extension classes acquire a presheaf-level witness

## Verification

```sh
nix develop --command coqc -R . Category Instance/Delta/Augmented.v Instance/Delta/Truncation.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Delta.Truncation. Print Assumptions sk_cosk_adjunction." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the two adjoint triples are instances of the general Kan existence theorem; the path-components identification is proved via the colimit formula; `sk ⊣ cosk` comes from the adjoint-triple result and is not re-proved by hand.

## Dependencies

Depends on: #225 (the simplicial category Δ)
Depends on: #515 (simplicial sets and simplicial objects)
Depends on: #590 (existence of Kan extensions from (co)completeness and the global adjoint to precomposition)
Depends on: #589 (the pointwise (co)limit formula, used to compute π₀, `sk` and `cosk`)
Depends on: #743 (adjoint triples — the induced monad and comonad, and `T ⊣ G`)

<!-- catalog: {"ids":["riehl:6.1:example8","riehl:6.2:example13"],"deps":["#225","#515","#590","#589","#743"]} -->

---8<---

```yaml
title: "Riehl 6.2: The comma category K↓d as the indexing data for Kan extensions — projection, reindexing, and the category-of-elements identification"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.2:construction-comma-slice-projection]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.2 "A formula for Kan extensions", the unnumbered construction developed in prose, printed p. 225 (PDF p. 245). Item: `riehl:6.2:construction-comma-slice-projection`.

Paraphrase: for a functor `K : C ⟶ D` and an object `d`, the comma category whose objects are the morphisms `K c ⟶ d` and whose morphisms are the maps of `C` making the evident triangle commute is (isomorphic to) the category of elements of the presheaf `D(K−, d)`, and carries a canonical projection to `C`. A morphism `g : d ⟶ d'` induces a reindexing functor between the two comma categories by postcomposition, strictly over `C` — the projection from the target composed with the reindexing is the projection from the source. The dual comma category with its projection is used for the right-handed statements.

## Background

This comma category and its projection are the indexing data for every formula in the chapter: the left Kan extension at `d` is a colimit over it, the right one a limit over the dual. See [nLab: comma category](https://ncatlab.org/nlab/show/comma+category) and [nLab: category of elements](https://ncatlab.org/nlab/show/category+of+elements).

## Current state in the library

Two of the four clauses are already in force; two are absent.

- `Construction/Comma.v:127` — `Program Definition Comma : Category := {| obj := ∃ p : A ∏ B, S (fst p) ~{C}~> T (snd p); hom := fun x y => ∃ f : …, `2 y ∘ fmap[S] (fst f) ≈ fmap[T] (snd f) ∘ `2 x; … |}` — at `S := K` and `T := =(d)` **is** Riehl's comma category on the nose. The verification pass checked this from source: `=( c )` is notation for `Diagonal 1 c` (`Functor/Diagonal.v:55`) whose `fmap` is `fun _ _ _ => id[x]` (`:32–38`), so the hom-condition collapses to `f' ∘ K h ≈ f`; the redundant second component valued in the terminal category is forced to its unique object and morphism and is harmless.
- `Construction/Comma.v:196` — `Program Instance comma_proj1 : Comma ⟶ A` — is the projection, and `:204` `comma_proj2` the dual one. Both orientations are in **use**, not merely constructible: `Construction/Comma/Limit.v:68–84` works in `=(d) ↓ U` and `Adjunction/GAFT.v:247–251` instantiates it.
- **Missing (1): the category-of-elements identification.** There is no category-of-elements construction anywhere in the library. `Construction/Grothendieck.v:108–110` narrates in a comment that "restricting the fibres to sets, viewed as discrete categories, recovers the category of elements el(F), whose projection is a discrete opfibration"; the restriction is never carried out, and `Construction/Grothendieck.v` is built over `IndexedCat : B ⟶ Cat`, not over a `Sets`-valued presheaf.
- **Missing (2): the reindexing functor at general `K`.** Only `Construction/Slice/Pullback.v:50` `Bang_Functor` exists (`@Slice C a ⟶ @Slice C b` by postcomposition) — the `K = Id` case on slices — and it carries no projection-compatibility equation. `Construction/Comma/Isomorphism.v` transports along a natural isomorphism of the *defining functors*, not along a morphism of the target object. The equation the (co)limit formula needs in order to make `d ↦ Lan_K F(d)` functorial is nowhere stated.

## Work to be done

Suggested module: `Construction/Comma/Reindex.v` (new). **Module-path note:** the category of elements itself belongs to #345 (which already proposes `Construction/Elements.v`); this issue must *consume* that file and add the comparison, not create a second category-of-elements construction. If #345 has not landed, put the comparison in `Construction/Comma/Reindex.v` against whatever construction #345 settles on rather than forking one here.

1. Define `comma_reindex g : (K ↓ =(d)) ⟶ (K ↓ =(d'))` for `g : d ~> d'` by postcomposition; prove functoriality, prove the projection equation `comma_proj1 ◯ comma_reindex g ≈ comma_proj1`, and prove the two coherence laws `comma_reindex id ≈ Id` and `comma_reindex (g' ∘ g) ≈ comma_reindex g' ◯ comma_reindex g`. Do the dual for `=(d) ↓ K` by precomposition.
2. Show `Construction/Slice/Pullback.v:50`'s `Bang_Functor` is the `K = Id` instance, so the tree ends with one reindexing notion in two presentations rather than two.
3. Consuming #345's category of elements of a `Sets`-valued presheaf and its projection, prove the comparison `Elements (D(K−, d)) ≅ (K ↓ =(d))` **over** `C` — i.e. the isomorphism commutes with the two projections. Relate it to #716's Yoneda-slice identification, of which this is the general form. Do not re-define the category of elements.
4. Note in the header that this construction is the indexing data for the whole of §6.2 and is what #589's formula consumes to make the extension functorial.

In-tree donors: `Construction/Comma.v`, `Construction/Comma/Isomorphism.v`, `Construction/Slice.v`, `Construction/Slice/Pullback.v`, `Functor/Diagonal.v`, `Instance/Discrete.v`, `Construction/Grothendieck.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.2 (printed p. 225), paraphrased; `≈` on morphisms, never `=`
- [ ] `comma_reindex` defined at **general** `K` (not only for slices), with functoriality, the projection equation, and both coherence laws proved
- [ ] `Bang_Functor` exhibited as the `K = Id` instance rather than left as a parallel notion
- [ ] `Elements (D(K−,d)) ≅ (K ↓ =(d))` proved **over** `C`, consuming #345's category of elements — no second category-of-elements construction is introduced
- [ ] The existing `Comma`/`comma_proj1` are reused; no second comma category is introduced
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Construction/Comma/Reindex.v
nix develop --command bash -c 'echo "Require Import Category.Construction.Comma.Reindex. Print Assumptions comma_reindex_proj. Print Assumptions comma_elements_iso." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the reindexing is at general `K`; the projection equation is stated and proved, not assumed; the elements comparison is over `C`, not merely an abstract equivalence.

## Dependencies

Depends on: #345 (the category of elements of a set-valued functor)
Depends on: #716 (the category of elements is equivalent to the Yoneda slice — the `K = y` case of the comparison)

- Related (NOT blocking): **#809** (Seven Sketches 3.5.3) also proposes `Construction/Elements.v`,
  and its Work item 1 defines the category of elements there as a prerequisite for its own pullback
  result. This issue already depends on **#345**, the canonical builder of that construction; #809
  supplies nothing further that this issue needs. Recorded as a same-file peer in
  `doc/plan/books/graph/serialize-groups.json`; no dependency edge is asserted.

<!-- catalog: {"ids":["riehl:6.2:construction-comma-slice-projection"],"deps":["#345","#716"]} -->

---8<---

```yaml
title: "Riehl 6.2: The real exponential as a Kan extension along the rationals in the reals"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:6.2:example8, riehl:6.2:exiii]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.2 Example 6.2.8, printed p. 228 (PDF p. 248), and Exercise 6.2.iii, printed p. 232 (PDF p. 252). Items: `riehl:6.2:example8`, `riehl:6.2:exiii`.

Paraphrase: regard the rationals and the positive reals as posets, hence as categories, and the exponential-base-two map as a functor between them. The positive reals have suprema and infima of bounded subsets, so the (co)limit formulae apply to the inclusion of the rationals: the left Kan extension at a real is the supremum of the values at rationals below it, which is the classical definition of a real power, and the right Kan extension is the infimum of the values at rationals above it, which agrees. The exercise asks for conditions on a monotone map under which its two Kan extensions along that inclusion both exist and coincide.

## Background

The chapter's opening motivation: a familiar analytic definition by suprema is a Kan extension in a thin category, and left and right Kan extensions along a dense order inclusion coincide exactly for the continuous maps. See [nLab: Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and Wikipedia on the [exponential function](https://en.wikipedia.org/wiki/Exponential_function).

## Current state in the library

The generic order machinery exists; no ordered field does, and no Kan extension is computed in any concrete category.

- **Correction recorded by the verification pass**, which sharpens (and does not weaken) the classification: the coverage note that `Instance/Poset.v` and `Instance/Proset.v` give the *categories* of posets and prosets is wrong. `Instance/Proset.v:33` — `Program Definition Proset {A} {R} (P : PreOrder R) : Category` — and `Instance/Poset.v:116` — `Definition Poset … : Category := Proset P`, with `LessThanEqualTo_Category` over the naturals at `:120` as the worked instance — build a single preorder or poset **as** a thin category. That is precisely the encoding this example needs.
- What is missing is everything else: there is no ℚ and no ℝ in the tree (`rg -iE 'rational|Qle|Rle|Reals'` finds nothing relevant; every "real" hit is English prose), no order embedding of one in the other, no order-theoretic supremum or infimum (`rg -i 'supremum|infimum'` → 0 relevant hits; `Instance/FinSet/Closed.v:178`'s `2^2` is the finite exponential object), and no statement anywhere about when a left and a right Kan extension along a common functor coincide.

## Work to be done

Suggested modules: `Instance/Poset/Reals.v` and `Instance/Poset/Exponential.v` (new).

1. Present ℚ and the positive reals as thin categories over `Instance/Proset.v`. State in the header which stdlib development is used (`QArith`, and `Reals` — which is classical, so this is an `Instance/`-layer artifact and docs/AXIOMS.md must be extended) or, if a constructive route is preferred, ℝ as Dedekind cuts of ℚ; disclose the choice and its axiom cost either way.
2. Define the order inclusion of ℚ in ℝ as a functor, and characterise bounded suprema and infima in the thin category as colimits and limits — in a thin category a (co)cone has at most one leg per object, so the (co)limit formula collapses to a supremum or infimum, and this collapse should be a stated lemma rather than a proof-local step.
3. Define the base-two exponential on ℚ, apply #589's formulae to the inclusion, and prove the left Kan extension at a real is the supremum of the values at rationals below and the right one the infimum of the values at rationals above, and that the two agree — hence the real exponential is *both* Kan extensions of its restriction to the rationals.
4. Discharge the exercise in general: give and prove a condition on a monotone `f : ℚ ⟶ ℝ` equivalent to the existence and agreement of both extensions (the supremum of the values below `x` equals the infimum of the values above it at every real `x` — i.e. `f` extends continuously), and record the boundedness hypothesis needed for existence separately from the agreement hypothesis.

In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Theory/Kan/Extension.v`, `Structure/Limit.v`, `Construction/Comma.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.2 Example 6.2.8 (printed p. 228) and Exercise 6.2.iii (printed p. 232), paraphrased; `≈` on morphisms, never `=`
- [ ] ℚ and the positive reals presented as thin categories **over** `Instance/Proset.v`, not as new bespoke categories
- [ ] The "in a thin category a (co)limit is a supremum/infimum" collapse proved as a reusable lemma
- [ ] Both Kan extensions of the exponential computed and proved to agree
- [ ] The exercise answered with a **proved** equivalence, existence and agreement conditions stated separately
- [ ] The axiom cost of the chosen real-number development disclosed in the header and enumerated in docs/AXIOMS.md
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the disclosed stdlib axioms of the `Instance/` layer
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Instance/Poset/Reals.v Instance/Poset/Exponential.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Poset.Exponential. Print Assumptions exp_is_lan. Print Assumptions exp_is_ran. Print Assumptions lan_ran_agree_iff." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the two extensions are computed by the general formula rather than defined to be the sup and inf; the agreement criterion is an equivalence, not a sufficient condition only.

## Dependencies

Depends on: #589 (the pointwise (co)limit formula for Kan extensions)
Depends on: #599 (pointwise Kan extensions — the formula's hypothesis)

<!-- catalog: {"ids":["riehl:6.2:example8","riehl:6.2:exiii"],"deps":["#589","#599"]} -->

---8<---

```yaml
title: "Riehl 6.2: Explicit induction and coinduction formulae for a subgroup inclusion"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.2:example9]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.2 Example 6.2.9, printed pp. 228–230 (PDF pp. 248–250). Item: `riehl:6.2:example9`.

Paraphrase: for a subgroup of a group and a complete and cocomplete target, restriction between the two functor categories has both adjoints, and the (co)limit formula makes them explicit. The comma category indexing the induction colimit has the group elements as objects and the subgroup elements acting on the right as morphisms; the colimit is therefore the coequalizer of two maps between coproducts indexed by the group-times-subgroup and by the group, and it is isomorphic to a coproduct indexed by the left cosets, with the residual action characterised as the unique quotient of left multiplication along the comparison epimorphism. Dually coinduction is an equalizer between products and is isomorphic to a product indexed by the right cosets. When finite products and finite coproducts agree in the target and the subgroup has finite index, the two formulae give the same object, so induction from a finite-index subgroup is simultaneously left *and* right adjoint to restriction.

## Background

The categorical form of Frobenius reciprocity, with the classical induced-module formula recovered from the colimit formula for Kan extensions. See [nLab: induced representation](https://ncatlab.org/nlab/show/induced+representation) and [nLab: Frobenius reciprocity](https://ncatlab.org/nlab/show/Frobenius+reciprocity).

## Current state in the library

The general adjoint triple for a group homomorphism is the subject of #987; nothing about the explicit formulae exists.

- No delooping of a group as a one-object category exists (`Theory/Bicategory/OneObject.v` deloops a *monoidal category* into a one-object *bicategory*, which is not this), so the functor categories cannot yet be named; `Structure/Group.v:109`'s `GroupObject` is a group internal to a cartesian category, with no action, coset or orbit machinery.
- "Coinduction" in the tree means the final-coalgebra proof principle (`Instance/Sets/Streams.v:21`, `Construction/FAlg.v:88`), unrelated. `rg -i 'induced representation|induction functor|ind\^|res\^'` finds nothing else.
- The pieces the formulae would consume do exist: `Structure/Limit/Product.v`'s `iprod`/`iprod_proj`/`iprod_ump` give set-indexed products as discrete-diagram limits, `Structure/Coequalizer.v` and `Structure/Equalizer/Fork.v` give the elementary (co)fork APIs, and `Structure/Biproduct.v` / `Structure/Semiadditive.v` are the in-tree vocabulary for "finite products and finite coproducts agree". None is connected to a Kan extension.
- No `LeftKan`/`RightKan` instance exists in the tree at all, so no restriction functor has an adjoint today.

## Work to be done

Suggested module: `Instance/Delooping/Induction.v` (a satellite of #987's files).

1. Over #987's delooping and restriction functor for a subgroup inclusion, and a complete and cocomplete target, obtain both adjoints from #590 and unfold them with #589's formulae.
2. Identify the indexing comma category for induction explicitly: objects the group elements, morphisms from one to another the subgroup elements with the stated equation. Prove the colimit over it is the coequalizer of the two evident maps between the coproduct indexed by group-times-subgroup and the coproduct indexed by the group.
3. Prove the coset formula: choosing left coset representatives gives an epimorphism from the group-indexed coproduct onto the coset-indexed one, exhibits induction as isomorphic to the coset-indexed coproduct, and characterises the residual action as the **unique** action making that epimorphism equivariant.
4. Do the dual for coinduction: an equalizer between the group-indexed product and the subgroup-times-group-indexed product, isomorphic to the right-coset-indexed product, with the action obtained by restricting the right action along the comparison monomorphism.
5. Prove the finite-index self-duality: in a target where finite products and finite coproducts agree (state this via `Structure/Biproduct.v`, not via an ad hoc hypothesis), induction and coinduction from a finite-index subgroup are isomorphic and the actions match, so induction is simultaneously a left and a right adjoint to restriction.

In-tree donors: `Structure/Limit/Product.v`, `Structure/Coequalizer.v`, `Structure/Equalizer/Fork.v`, `Structure/Biproduct.v`, `Structure/Semiadditive.v`, `Theory/Kan/Extension.v`, `Construction/Comma.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.2 Example 6.2.9 (printed pp. 228–230), paraphrased; `≈` on morphisms, never `=`
- [ ] The indexing comma category identified explicitly and the (co)equalizer presentations **proved** from the (co)limit formula, not posited
- [ ] The coset formulae proved for both induction and coinduction, with the residual action characterised by its uniqueness
- [ ] The finite-index case proved, with "finite products agree with finite coproducts" expressed through the existing biproduct vocabulary
- [ ] The conclusion that induction from a finite-index subgroup is both a left and a right adjoint to restriction stated as a theorem
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Instance/Delooping/Induction.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Delooping.Induction. Print Assumptions ind_coequalizer. Print Assumptions ind_cosets. Print Assumptions ind_iso_coind_finite_index." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the formulae are derived from the comma-category (co)limit formula, not defined; the coset isomorphism is proved equivariant; the finite-index statement really concludes a two-sided adjointness.

## Dependencies

Depends on: #987 (induction, restriction and coinduction along a group homomorphism — the adjoint triple this issue computes)
Depends on: #589 (the pointwise (co)limit formula)
Depends on: #590 (existence of the extensions from (co)completeness)
Depends on: #220 (delooping monoids and groups into one-object categories)

<!-- catalog: {"ids":["riehl:6.2:example9"],"deps":["#987","#589","#590","#220"]} -->

---8<---

```yaml
title: "Riehl 6.2: The fixed-point functor as a right Kan extension along the orbit-category embedding"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.2:example12]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.2 Example 6.2.12, printed p. 230 (PDF p. 250). Item: `riehl:6.2:example12`.

Paraphrase: the endomorphism monoid of the free orbit is the opposite of the group, which embeds the opposite delooping into the orbit category. For a left group-set, the limit formula computes the right Kan extension along that embedding as the fixed-point functor: the comma category indexing the limit at an orbit is isomorphic to the action groupoid of that orbit, which is equivalent to the automorphism group of any of its objects, so the limit reduces to the limit of the restricted action, namely the fixed points of the corresponding subgroup, and an equivariant map of orbits acts by direct image. Specialising to the Galois group of a finite Galois extension, the right Kan extension of the extension field along the embedding yields the isomorphism of categories that categorifies the fundamental theorem of Galois theory; a footnote notes that the category of intermediate fields has very few limits, but does possess exactly the ones the formula requires.

## Background

An instance where the pointwise formula is genuinely load-bearing: the target has almost no limits, yet exactly the ones the extension needs, and the resulting functor is the classical fixed-point construction. See [nLab: orbit category](https://ncatlab.org/nlab/show/orbit+category) and Wikipedia on the [fundamental theorem of Galois theory](https://en.wikipedia.org/wiki/Fundamental_theorem_of_Galois_theory).

## Current state in the library

Absent, together with every one of its ingredients.

- There is no orbit category, no group-set, no action groupoid, and no category of fields; `Structure/Group.v` provides only the internal `GroupObject` class, with no action or orbit machinery. The orbit category and the Galois isomorphism are filed as #911; limits and colimits of group-sets, including fixed points and orbits, as #954.
- Every `Galois` hit in the tree is about Galois *connections* between posets (`Instance/Poset.v:37–100`, `Theory/Adjunction.v:78–79`, `Adjunction/GAFT.v:136`, `Structure/Factorization.v:69`, `Structure/Limit.v:53`), and `Instance/Poset.v:58` cites the fundamental theorem purely as etymology; nothing asserts anything about field extensions.
- No comma-category limit formula for Kan extensions exists (`Theory/Kan/Extension.v:74–79` calls it "a bridge not yet formalized"), and the only Kan statement outside that file is `Structure/Limit/Kan/Extension.v:46` `Kan_Limit`, along the terminal functor.

## Work to be done

Suggested module: `Instance/Orbit/Kan.v` (new).

1. Over #911's orbit category and #220's delooping, construct the embedding of the opposite delooping into the orbit category (the free orbit's endomorphism monoid is the opposite group) and prove it fully faithful.
2. For a left group-set, apply #589's limit formula along that embedding, and prove the indexing comma category at an orbit is isomorphic to the action groupoid of that orbit; prove that groupoid is equivalent to the delooping of the corresponding subgroup (this is #923's orbit–stabilizer content), so the limit reduces to the limit of the restricted action.
3. Identify that limit with the fixed-point set of the subgroup — #954 supplies the fixed-point-as-limit statement for group-sets — and prove the resulting assignment is a functor on the opposite orbit category carrying an equivariant map of orbits to the corresponding direct-image function.
4. Specialise to Galois theory: with the Galois group of a finite Galois extension and the extension field viewed as a functor on the delooping, prove the right Kan extension along the embedding is the isomorphism of categories filed as #911, and record explicitly which limits the category of intermediate fields must possess for the formula to apply — the point of Riehl's footnote, and the reason the representable (pointwise) criterion of #599 rather than completeness is the right hypothesis here.

In-tree donors: `Theory/Kan/Extension.v`, `Construction/Comma.v`, `Construction/Groupoid.v`, `Structure/Limit.v`, `Instance/Fun.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.2 Example 6.2.12 (printed p. 230), paraphrased; `≈` on morphisms, never `=`
- [ ] The embedding of the opposite delooping into the orbit category constructed and proved fully faithful
- [ ] The comma category at each orbit proved isomorphic to the action groupoid, and that groupoid proved equivalent to the subgroup's delooping
- [ ] The right Kan extension proved to be the fixed-point functor, with the action on morphisms identified as the direct image
- [ ] The Galois specialisation proved, and the limits actually required of the intermediate-field category enumerated in the header (Riehl's footnote)
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Instance/Orbit/Kan.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Orbit.Kan. Print Assumptions ran_is_fixed_points. Print Assumptions galois_ran." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the fixed-point identification comes from the limit formula rather than being defined; the Galois clause is derived, not restated; the required-limits footnote is honoured in the header.

## Dependencies

Depends on: #911 (the orbit category and the fundamental theorem of Galois theory as an isomorphism of categories)
Depends on: #954 (limits and colimits of group-sets — fixed points and orbits)
Depends on: #923 (the action groupoid and the categorified orbit–stabilizer theorem)
Depends on: #589 (the pointwise (co)limit formula)
Depends on: #599 (pointwise Kan extensions — the criterion appropriate to a target with few limits)
Depends on: #220 (delooping monoids and groups into one-object categories)

<!-- catalog: {"ids":["riehl:6.2:example12"],"deps":["#911","#954","#923","#589","#599","#220"]} -->

---8<---

```yaml
title: "Riehl 6.3: Preservation of induced and coinduced objects by underlying-set functors"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.3:example3, riehl:6.3:example4]
deps_item_ids: [riehl:6.2:example9]
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.3 Examples 6.3.3 and 6.3.4, printed p. 234 (PDF p. 254). Items: `riehl:6.3:example3`, `riehl:6.3:example4`.

Paraphrase: the underlying-set functor on spaces has both a left and a right adjoint, so it preserves both the left and the right Kan extension computing induction and coinduction — the underlying set of an induced (resp. coinduced) group-space is the induced (resp. coinduced) group-set. The underlying-set functor on vector spaces is only a right adjoint: it preserves limits, hence the coinduced representation agrees with the coinduced group-set built from the underlying set, but it does not preserve colimits — the underlying set of a direct sum is not the coproduct of the underlying sets — so the underlying set of an *induced* representation is **not** the induced group-set.

## Background

The two examples calibrate the preservation lemma: having an adjoint on the relevant side is exactly what makes a forgetful functor commute with an induction or coinduction construction, and the failure on the other side is a genuine counterexample. See [nLab: Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and [nLab: induced representation](https://ncatlab.org/nlab/show/induced+representation).

## Current state in the library

Both concrete categories are missing, and the only preservation vocabulary in the tree is the weaker corollary Riehl explicitly says is not enough here.

- There is no category of topological spaces: `ls Instance/*.v` is exactly `Adj, Adjoints, AST, Cat, CMon, Comp, Cones, Coq, Discrete, Ens, Fact, FinSet, Fun, Lambda, Omega, One, Parallel, Poset, Props, Proset, Rel, Roof, Sets, Shapes, StrictCat, Two, Zero, ZX`, and `rg -i 'topological space'` returns nothing outside background prose. `Top` and its adjoint triple are filed as #259 and #456.
- There is no category of vector spaces: `rg -i 'Vect|vector space'` returns only header prose (`Structure/Abelian.v`, `Structure/Group.v`, the monoidal headers) plus `Coq.Vectors.Vector` in `Theory/Sheaf.v`; `Instance/Shapes.v`'s `Vectors` is a category of length-indexed tries and is unrelated. The additive spine (`Structure/Biproduct.v`, `Structure/Additive.v`, `Instance/CMon.v`) has biproducts but no field and no forgetful functor to sets.
- What exists is `Adjunction/Continuity.v:202` `right_adjoint_preserves_limits` and `:223` `left_adjoint_preserves_colimits` — the RAPL/LAPC statements. Riehl's §6.3 is explicit that this corollary is *insufficient* for the preservation claim, because it covers only the Kan extensions that happen to be constructed as (co)limits; the genuine statement is that an adjoint preserves *all* Kan extensions on the relevant side, and that is #598's obligation (whose in-tree stub `left_adjoints_preserve`, `Theory/Kan/Extension.v:386–438`, is abandoned with three `admit`s and an `Abort.`, honestly disclosed at `:376–384`).

## Work to be done

Suggested module: `Instance/Delooping/Preservation.v` (new).

1. Over #456's adjoint triple for the underlying-set functor on spaces, and #598's theorem that an adjoint preserves Kan extensions on the corresponding side, prove that the underlying set of an induced group-space is the induced group-set and likewise for coinduction — stating the conclusion at the level of the extensions themselves (the whiskered unit exhibits the extension), not merely as an isomorphism of objects.
2. Over #935's vector spaces: prove the underlying-set functor is a right adjoint, hence preserves the coinduced representation; then exhibit the counterexample for the left-hand side by computing the underlying set of a direct sum and the coproduct of the underlying sets and proving they differ, so that the induced representation's underlying set is **not** the induced group-set.
3. Record in the header the distinction Riehl draws and why it matters here: RAPL/LAPC would only give preservation for extensions that are (co)limits, whereas the statement being proved is preservation of the extension itself.

In-tree donors: `Adjunction/Continuity.v`, `Theory/Kan/Extension.v`, `Structure/Biproduct.v`, `Instance/Sets.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.3 Examples 6.3.3 and 6.3.4 (printed p. 234), paraphrased; `≈` on morphisms, never `=`
- [ ] Both spaces-side preservation statements proved through the "adjoints preserve Kan extensions" theorem, not through RAPL/LAPC, and the difference recorded in the header
- [ ] The vector-space coinduction preservation proved
- [ ] The vector-space induction **counterexample** proved (not merely asserted), by computing both sides
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Instance/Delooping/Preservation.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Delooping.Preservation. Print Assumptions top_forget_preserves_ind. Print Assumptions vect_forget_not_preserves_ind." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the preservation statements track the whiskered unit/counit, not just the underlying objects; the vector-space failure is a theorem.

## Dependencies

Depends on: riehl:6.2:example9 (the explicit induction and coinduction formulae these examples evaluate)
Depends on: #598 (preservation of Kan extensions; adjoints preserve them)
Depends on: #456 (the underlying-set functor of Top and its adjoint triple)
Depends on: #935 (the category of vector spaces)
Depends on: #987 (induction, restriction and coinduction along a group homomorphism)

<!-- catalog: {"ids":["riehl:6.3:example3","riehl:6.3:example4"],"deps":["riehl:6.2:example9","#598","#456","#935","#987"]} -->

---8<---

```yaml
title: "Riehl 6.3: (Co)completeness as an adjoint to restriction along the cone-shape inclusion"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.3:prop9, riehl:6.3:exii]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.3 Proposition 6.3.9 and Exercise 6.3.ii, printed p. 236 (PDF p. 256). Items: `riehl:6.3:prop9`, `riehl:6.3:exii`.

Paraphrase: a category admits all colimits of diagrams of a given small shape if and only if restriction along the inclusion of that shape into the shape obtained by freely adjoining a terminal object has a left adjoint, and in that case the left adjoint is given by pointwise left Kan extension — it carries a diagram to its colimit cone. Dually for limits and the freely adjoined initial object. The proof: the inclusion is fully faithful, so the extension is the original diagram on the old objects, and the comma category at the new cone point is isomorphic to the shape itself, so the formula identifies the value there with the colimit. The exercise asks which universal property of the colimit cone this expresses — one strictly stronger than the usual one.

## Background

Restriction along the inclusion of a shape into its cone shape is the "forget the cone" functor, and its adjoint is the colimit-with-its-cocone. It packages (co)completeness as an adjointness, one level finer than the usual diagonal-functor formulation. See [nLab: Kan extension](https://ncatlab.org/nlab/show/Kan+extension) and [nLab: join of categories](https://ncatlab.org/nlab/show/join+of+categories).

## Current state in the library

Neither the shape nor the characterisation exists.

- The cone and cocone shape categories do not exist; they are filed as #961 (as pushouts in the category of categories). Without them neither the restriction functor between the two functor categories nor its adjoint can be written down.
- `Complete` and `Cocomplete` (`Structure/Complete.v:115`, `:119`) are defined purely as "every diagram has a limit/colimit" and are never characterised by an adjoint. `Functor/Diagonal.v:28` mentions `colim ⊣ Δ ⊣ lim` **only in a header comment**; the file's actual content is `Diagonal`, `Diagonal_Product`, the `Δ` notations, `Diagonal_Product_Two` and `Transform_Const`, with no adjunction. The only diagonal adjunction proved in the tree is the **binary** `Adjunction/Diagonal/Product.v:36`, i.e. the two-object discrete shape. `Structure/Cone/Const.v:24`'s `Δ ⊣ lim` is likewise prose.
- The only colimit universal property in the tree is the ordinary initial-cocone one (`Structure/Limit.v`'s `Limit`/`IsALimit`/`ump_limits`, `Structure/Cone.v`'s `ACone`); there is no strengthened variant, and no `C^{J^▷} ⟶ C^J` restriction functor.

## Work to be done

Suggested module: `Structure/Limit/ConeShape.v` (new).

1. Over #961's cone and cocone shapes, define the fully faithful inclusion of the shape into its cone shape and the restriction functor between the two functor categories (this is `Induced` at that inclusion, so reuse `Theory/Kan/Extension.v:127` rather than defining a second restriction).
2. Prove: the target admits all colimits of that shape **iff** the restriction functor has a left adjoint, and in that case the left adjoint is the pointwise left Kan extension. Follow Riehl's argument — full faithfulness gives, by #591, that the extension agrees with the original diagram on the old objects, and the comma category at the freely adjoined cone point is isomorphic to the shape, so #589's formula identifies the value there with the colimit. Dually for limits along the cocone shape.
3. Discharge Exercise 6.3.ii: state and prove the strictly stronger universal property this expresses. Ordinary colimit universality quantifies over cocones under a **fixed** diagram; adjointness quantifies over all diagrams and all natural transformations between them, so a natural transformation from the diagram to any other diagram, together with a cocone under the latter, induces a unique map out of the colimit — colimit is a left adjoint, not merely objectwise initial.
4. Record the closing observation of §6.3 in the header: pointwise Kan extensions most often arise when the target is (co)complete, but §6.4's derived functors are a case where they arise otherwise.

In-tree donors: `Theory/Kan/Extension.v`, `Structure/Limit.v`, `Structure/Cone.v`, `Structure/Cone/Const.v`, `Structure/Complete.v`, `Instance/Fun.v`, `Construction/Comma.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.3 Proposition 6.3.9 and Exercise 6.3.ii (printed p. 236), paraphrased; `≈` on morphisms, never `=`
- [ ] The restriction functor is `Induced` at the cone-shape inclusion, not a new definition
- [ ] The biconditional proved in **both** directions, for colimits and (dually) for limits
- [ ] The left adjoint identified with the pointwise left Kan extension, and its value at the cone point identified with the colimit
- [ ] Exercise 6.3.ii's stronger universal property stated as its own named theorem and proved
- [ ] The relation to `Structure/Complete.v`'s `Complete`/`Cocomplete` recorded, so the tree has one (co)completeness notion with two characterisations
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (a new characterisation of (co)completeness is flagship-level)

## Verification

```sh
nix develop --command coqc -R . Category Structure/Limit/ConeShape.v
nix develop --command bash -c 'echo "Require Import Category.Structure.Limit.ConeShape. Print Assumptions cocomplete_iff_cone_restriction_left_adjoint. Print Assumptions colimit_cocone_strong_ump." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: both directions of the biconditional are proved; the stronger universal property is genuinely stronger (it quantifies over maps of diagrams) and is stated separately.

## Dependencies

Depends on: #961 (cone-shape index categories)
Depends on: #591 (fully faithful `K` and the invertible unit — used on the old objects)
Depends on: #589 (the pointwise (co)limit formula — used at the cone point)
Depends on: #599 (pointwise Kan extensions)

<!-- catalog: {"ids":["riehl:6.3:prop9","riehl:6.3:exii"],"deps":["#961","#591","#589","#599"]} -->

---8<---

```yaml
title: "Riehl 6.4: Homotopical categories — weak equivalences, the 2-of-6 property, and homotopical functors"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.4:def1, riehl:6.4:lem2, riehl:6.4:def3, riehl:6.4:example4, riehl:6.4:exi]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.4 "Derived functors as Kan extensions": Definition 6.4.1, Lemma 6.4.2, Definition 6.4.3 and Example 6.4.4, printed p. 237 (PDF p. 257); Exercise 6.4.i, printed p. 242 (PDF p. 262). Items: `riehl:6.4:def1`, `riehl:6.4:lem2`, `riehl:6.4:def3`, `riehl:6.4:example4`, `riehl:6.4:exi`.

Paraphrase: a class of morphisms is a class of **weak equivalences** when it contains every identity and satisfies the 2-of-6 property — for a composable triple whose two adjacent binary composites lie in the class, all four of the three arrows and their triple composite lie in the class. Three consequences: any class containing the identities and satisfying 2-of-6 contains all isomorphisms; the isomorphisms themselves satisfy 2-of-6; and for any functor, the class of morphisms it sends to isomorphisms satisfies 2-of-6. A **homotopical category** is a category with such a class, and a functor between homotopical categories is **homotopical** when it carries weak equivalences to weak equivalences. In the absence of a specified class, a category is given the minimal homotopical structure, which by the first two consequences is exactly its class of isomorphisms.

## Background

Homotopical categories are the minimal setting for derived functors: no model structure, no factorisation, just a class of maps to be inverted, closed under the 2-of-6 cancellation property. See [nLab: homotopical category](https://ncatlab.org/nlab/show/homotopical+category) and [nLab: two-out-of-six property](https://ncatlab.org/nlab/show/two-out-of-six).

## Current state in the library

Wholly absent, but the carrier the definition constrains already exists.

- `rg -i '2-of-6|two-out-of-six|2-of-3|two-out-of-three'` over the whole tree returns **0 hits**: neither 2-of-6 nor the weaker 2-of-3 is stated anywhere.
- `rg -ci 'weak equivalence'` returns 4 files, all prose: `Structure/Factorization.v:104` (a Quillen citation), `Theory/Kan/Extension.v:94` (the pointer to this very section of Riehl), `Construction/Localization.v:57,77` (motivation for localizing), and `Test/Issue138.v:15,40` (which uses "weak equivalence" for the identification of functors up to natural isomorphism in the category of categories — unrelated). `rg -i 'homotopical'` returns 4 hits, all background essays (`Structure/Factorization.v:104`, `Construction/Localization.v:107`, `Construction/Arrow.v:65`, `Theory/Kan/Extension.v:52`).
- The carrier exists: `Theory/Morphisms/Classes.v:28` — `MorphismClass C := ∀ x y : C, (x ~> y) → Type` — with `IsoClass` at `:39` (`fun _ _ f => IsIsomorphism f`) and six inclusion lemmas. But the file proves **no closure or cancellation axiom on any class**, and all three consumers take the class unaxiomatized: `Structure/Factorization.v`'s `OFS` (`:144`, whose only closure field is `ofs_e_respects` at `:145`), `Structure/Regular/Factorization.v`, and `Construction/Localization.v`.
- The tools the lemma needs are missing in two places. There is **no 2-of-3-shaped cancellation lemma for isomorphisms** ("if `g ∘ f` and `g` are isomorphisms then so is `f`"): `Theory/Isomorphism.v` offers `iso_id`, `iso_sym`, `iso_compose` (`:166`), `iso_equivalence` (`:187`), `comp_inverse_unique`, and the iso-implies-monic-and-epic lemmas, none of which cancels. And the class of morphisms **inverted by** a functor is never formed as a `MorphismClass`; the nearest thing is the section hypothesis `Construction/Localization/Universal.v:144` — `Context (GW : ∀ a b (w : a ~> b), W a b w → IsIsomorphism (fmap[G] w))` — which constrains a *given* class rather than forming the inverted one. `Structure/Limit/Preservation.v:243` `Class ReflectsIsos` (field `reflects_iso : IsIsomorphism (fmap[F] f) → IsIsomorphism f`) is the converse direction.
- No structure in the tree bundles a category with a distinguished class of morphisms as a single object of study, and there is no "functor preserves a `MorphismClass`" predicate — the preservation vocabulary of `Structure/Limit/Preservation.v` is limits, colimits and `ReflectsIsos`. **Distinction to preserve when formalizing:** *inverting* a class (what the in-tree localization hypotheses say) and *preserving* a class (Riehl's homotopical functor) are different conditions, and both are needed later in the section.

## Work to be done

Suggested module: `Theory/Homotopical.v` (new).

1. Define `WeakEquivalences` over `Theory/Morphisms/Classes.v`'s existing `MorphismClass` — do **not** introduce a second carrier — with the identity-containment field and the 2-of-6 field stated for a composable triple, concluding membership for all three arrows and the triple composite.
2. Prove Lemma 6.4.2 (Exercise 6.4.i): (i) identities plus 2-of-6 imply every isomorphism belongs to the class; (ii) the isomorphisms satisfy 2-of-6 — this needs the missing cancellation lemma, so add "if `g ∘ f` and `g` are isomorphisms then `f` is" (and its mirror) to `Theory/Isomorphism.v` alongside `iso_compose`; (iii) for any functor, the class of morphisms it sends to isomorphisms satisfies 2-of-6 — and package that class as a first-class `MorphismClass` (`inverted_by F`), which the tree currently lacks and which the later sections need.
3. Define `HomotopicalCategory` bundling a category with such a class, and `HomotopicalFunctor` as a functor carrying weak equivalences to weak equivalences. State in the header the difference between this and "inverts the class", and cross-reference `Construction/Localization/Universal.v`'s hypothesis, which is the latter.
4. Prove Example 6.4.4: the minimal homotopical structure on a category is `IsoClass` — built on `Theory/Morphisms/Classes.v:39`'s existing definition, not a fresh one — and prove its minimality among admissible classes, which is exactly clauses (i) and (ii).

In-tree donors: `Theory/Morphisms/Classes.v`, `Theory/Isomorphism.v`, `Theory/Morphisms.v`, `Structure/Limit/Preservation.v`, `Construction/Localization.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.4 Definitions 6.4.1 and 6.4.3, Lemma 6.4.2, Example 6.4.4 (printed p. 237) and Exercise 6.4.i (printed p. 242), paraphrased; `≈` on morphisms, never `=`
- [ ] `WeakEquivalences` built over the existing `MorphismClass`; no second carrier introduced
- [ ] All three clauses of Lemma 6.4.2 proved
- [ ] The missing isomorphism cancellation lemma added to `Theory/Isomorphism.v` (both sides)
- [ ] The class of morphisms inverted by a functor packaged as a `MorphismClass` and proved to satisfy 2-of-6
- [ ] `HomotopicalCategory` and `HomotopicalFunctor` defined, with the preserve-versus-invert distinction stated in the header and cross-referenced to `Construction/Localization/Universal.v`
- [ ] The minimal structure proved to be `IsoClass`, reusing the existing definition, with minimality proved
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` (zero-axiom core theory per docs/AXIOMS.md scoping)
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (this opens a new development area)

## Verification

```sh
nix develop --command coqc -R . Category Theory/Homotopical.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Homotopical. Print Assumptions we_contains_isos. Print Assumptions iso_class_2of6. Print Assumptions inverted_by_2of6." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: 2-of-6 is stated in full (all four conclusions), not weakened to 2-of-3; the minimal-structure claim is a minimality proof, not a definitional alias.

## Dependencies

None.

<!-- catalog: {"ids":["riehl:6.4:def1","riehl:6.4:lem2","riehl:6.4:def3","riehl:6.4:example4","riehl:6.4:exi"],"deps":[]} -->

---8<---

```yaml
title: "Riehl 6.4: The homotopy category and the localization functor — universal property and the Gabriel–Zisman construction"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.4:def5, riehl:6.4:construction-gabriel-zisman-hoc, riehl:6.4:remark6, riehl:6.4:exii]
deps_item_ids: [riehl:6.4:def3]
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.4: Definition 6.4.5, printed p. 237 (PDF pp. 257–258); the Gabriel–Zisman construction in unnumbered running prose, printed p. 238 (PDF p. 258); Remark 6.4.6, printed p. 238 (PDF p. 258); Exercise 6.4.ii, printed p. 242 (PDF p. 262). Items: `riehl:6.4:def5`, `riehl:6.4:construction-gabriel-zisman-hoc`, `riehl:6.4:remark6`, `riehl:6.4:exii`.

Paraphrase: every homotopical category has a homotopy category characterised by a universal property — it is initial among categories equipped with a homotopical functor from it, i.e. among categories receiving a functor that inverts the weak equivalences — and the universal functor is called the localization functor. An explicit model is due to Gabriel and Zisman: same objects, morphisms the equivalence classes of finite zig-zags in which only weak equivalences point backwards, modulo composing adjacent same-direction arrows, deleting an adjacent out-and-back pair labelled by one and the same weak equivalence, and deleting identities in either direction; the localization functor is the identity on objects and sends a morphism to its unary forward zig-zag. The universal property has a second, two-dimensional aspect: precomposition with the localization is also a bijection on natural transformations, equivalently it identifies the functor category out of the homotopy category with the full subcategory of the functor category out of the original spanned by the homotopical functors.

## Background

Localization inverts a class of morphisms freely; the Gabriel–Zisman zig-zag calculus is the general construction, and its two-dimensional universal property is what makes derived functors computable. See [nLab: localization](https://ncatlab.org/nlab/show/localization), [nLab: calculus of fractions](https://ncatlab.org/nlab/show/calculus+of+fractions) and Wikipedia on [localization of a category](https://en.wikipedia.org/wiki/Localization_of_a_category).

## Current state in the library

A localization exists, but only in a reflective form with three genuine weakenings, and the two-dimensional aspect is entirely absent.

- `Construction/Localization/Universal.v:188` — `Theorem localization_universal : { G' : Su ⟶ E & (G ≈ G' ◯ Refl) * (∀ H : Su ⟶ E, G ≈ H ◯ Refl → H ≈ G') }` — under `Context (R : Reflective (C_W W))` (`:76`), `(G : C ⟶ E)` (`:141`), `(GW : ∀ a b (w : a ~> b), W a b w → IsIsomorphism (fmap[G] w))` (`:144`) and `Hunit` (`:148–150`). `Construction/Localization.v:241` — `Theorem reflector_inverts_W {a b : C} (w : a ~> b) (Hw : W a b w) : IsIsomorphism (fmap[Refl] w)`. Both files are registered in `_CoqProject` (lines 56–57) and compile.
- The three weakenings, each verified: **(1) existence is assumed, not proved** — the homotopy category is taken to be the full subcategory of `W`-local objects and its existence is the hypothesis `Reflective (C_W W)`, whereas Riehl asserts a homotopy category for *every* homotopical category; **(2)** the extra saturation hypothesis `Hunit` requires the reflection units to lie in `W` (the file's own "honest saturation condition"); **(3) uniqueness is only up to natural isomorphism** — `H ≈ G'` in the functor setoid, and `Instance/Fun.v:255` `Theorem Functor_Setoid_Nat_Iso` confirms `≈` is natural isomorphism — whereas Riehl's initiality is a **bijection** between functors out of the homotopy category and homotopical functors out of the original.
- The general construction is explicitly out of scope in the tree today: `Construction/Localization/Universal.v:35–38` states that "the zig-zag calculus of fractions — the syntactic construction of `C[W⁻¹]` out of formal composites of `W`-arrows and their formal inverses — is out of this file's scope (ledger entry 15)". Every `zig-zag` hit in the tree is either the adjunction triangle identities or `Theory/DoubleCategory/Companion.v`'s vertical zigzag.
- Nothing in the tree names a homotopy category, or a localization functor attached to a class of weak equivalences, or proves initiality among categories under the original.
- Remark 6.4.6 is not even approached. `Induced` (`Theory/Kan/Extension.v:127`) is the only precomposition functor in the tree, and the **only** facts proved about it are that its adjoints are the Kan extensions (`:145`, `:225`); nothing asserts fullness, faithfulness, or a bijection on natural transformations for precomposition along any functor, let alone a localization. `localization_universal` is strictly one-dimensional.
- For the free-category ingredient of the syntactic construction, note that `Construction/Free.v:118`'s `Free` is the free category on the underlying quiver **of an existing category**; the free category on an arbitrary quiver is `FreeOnQuiver` in `Construction/Free/Quiver.v` (Section `Free`, `:426` ff.), with `FreeCatFunctor` at `:546` and `FreeForgetfulAdjunction` at `:550`. Cite the latter.

## Work to be done

Suggested module: `Construction/Localization/Fractions.v` (new), with a header update to `Construction/Localization/Universal.v`.

1. Build the homotopy category by the Gabriel–Zisman presentation: same objects; morphisms the finite zig-zags with only weak equivalences pointing backwards, quotiented by the three relations (compose adjacent same-direction arrows; delete an adjacent out-and-back pair labelled by one and the same weak equivalence; delete identities in either direction). Use `Construction/Free/Quiver.v` for the free category on the zig-zag quiver and `Construction/Quotient.v` for the hom-congruence quotient, so the construction is two existing universal properties composed.
2. Define the localization functor (identity on objects, a morphism to its unary forward zig-zag), prove it is homotopical, and prove Definition 6.4.5's universal property as a genuine **bijection** between functors out of the homotopy category and homotopical functors out of the original — not merely existence-and-uniqueness up to `≈`.
3. Prove Remark 6.4.6 / Exercise 6.4.ii: precomposition with the localization is also a bijection on natural transformations, equivalently the functor category out of the homotopy category is the full subcategory of the functor category out of the original spanned by the homotopical functors. State it in the form the later derived-functor propositions consume (fullness and faithfulness of `Induced` at the localization, restricted to that subcategory).
4. Reconcile with the existing reflective localization: exhibit the comparison functor from the Gabriel–Zisman model to `Construction/Localization.v`'s `C_W W` under the `Reflective` plus `Hunit` hypotheses, and state which hypotheses become redundant. Update `Construction/Localization/Universal.v`'s header, which currently defers this to ledger entry 15.
5. Record the set-theoretic caveat Riehl flags: in the interesting cases the source is not small and the homotopy category is a priori not locally small; say how the universe-polymorphic hom-setoids handle it.

In-tree donors: `Construction/Free/Quiver.v`, `Construction/Quotient.v`, `Construction/Localization.v`, `Construction/Localization/Universal.v`, `Theory/Kan/Extension.v` (`Induced`), `Instance/Fun.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.4 Definition 6.4.5 and Remark 6.4.6 (printed pp. 237–238), the Gabriel–Zisman construction (printed p. 238) and Exercise 6.4.ii (printed p. 242), paraphrased; `≈` on morphisms, never `=`
- [ ] The zig-zag category constructed via the free-category and quotient universal properties rather than by hand
- [ ] The one-dimensional universal property proved as a **bijection** (Riehl's initiality), not as uniqueness up to natural isomorphism
- [ ] The two-dimensional universal property proved, in the form the derived-functor results consume
- [ ] The comparison with `Construction/Localization.v`'s reflective localization stated and proved, and that file's header updated so ledger entry 15's deferral is discharged
- [ ] The size caveat recorded in the header
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (the general localization is flagship-level)

## Verification

```sh
nix develop --command coqc -R . Category Construction/Localization/Fractions.v
nix develop --command bash -c 'echo "Require Import Category.Construction.Localization.Fractions. Print Assumptions ho_universal. Print Assumptions ho_universal_2dim." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the universal property really is a bijection; the two-dimensional statement is about natural transformations, not just functors; the reflective localization is reconciled rather than duplicated.

## Dependencies

Depends on: riehl:6.4:def3 (homotopical categories and homotopical functors)
Related: #972 (the category of fractions for the groupoid core — the special case in which every morphism is inverted)

<!-- catalog: {"ids":["riehl:6.4:def5","riehl:6.4:construction-gabriel-zisman-hoc","riehl:6.4:remark6","riehl:6.4:exii"],"deps":["riehl:6.4:def3"]} -->

---8<---

```yaml
title: "Riehl 6.4: Concrete homotopical structures — chain complexes and topological spaces"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.4:example7, riehl:6.4:example8]
deps_item_ids: [riehl:6.4:def3]
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.4 Examples 6.4.7 and 6.4.8, printed p. 238 (PDF p. 258). Items: `riehl:6.4:example7`, `riehl:6.4:example8`.

Paraphrase: chain complexes of modules carry two homotopical structures of interest — first with the chain homotopy equivalences as weak equivalences, then with the larger class of quasi-isomorphisms, the chain maps inducing isomorphisms on homology. Spaces likewise carry two — the homotopy equivalences, and the larger class of weak homotopy equivalences, the maps inducing isomorphisms on all homotopy groups; the homotopy category of spaces is the one associated with the second, and it is equivalent to the category of CW complexes and homotopy classes of maps.

## Background

The two motivating families of homotopical categories, and the reason the derived-functor machinery of the section is worth building. See [nLab: quasi-isomorphism](https://ncatlab.org/nlab/show/quasi-isomorphism) and [nLab: weak homotopy equivalence](https://ncatlab.org/nlab/show/weak+homotopy+equivalence).

## Current state in the library

Neither ambient category exists.

- There is no category of chain complexes: `rg -i 'chain complex|Ch_R|differential graded|\bdg-'` returns prose only (`Structure/Abelian.v:70`, `Construction/Enriched.v:47,71`, `Construction/Localization.v:58,80,99`), and there is no homology functor — every `homology`/`cohomolog` hit is historical prose — so "quasi-isomorphism" has no carrier at all (its three occurrences are all inside the `Construction/Localization.v` background essay, at `:58`, `:80`, `:99`). Chain complexes and homology objects are filed as #557.
- There is no category of spaces: `rg -i 'topolog'` returns only bibliography and essay prose; `CW`, `Htpy` and `Whitehead` return 0 hits; homotopy groups appear only in prose (`Structure/Group.v:76`, `Theory/Kan/Extension.v:53`). `Top` is filed as #259 and the homotopy-classes category as #260.
- The one hit that might look like counter-evidence is not: `Instance/StrictCat.v:33–40` is a **comment** contrasting the functor setoid of the category of categories with the strict-equality one ("making it the homotopy category Ho(Cat)") — about categories, not spaces, and asserting nothing formal.

## Work to be done

Suggested modules: `Instance/Chain/Homotopical.v` and `Instance/Top/Homotopical.v` (new).

1. Over #557's chain complexes: define chain homotopy and chain homotopy equivalence, prove the equivalences contain the identities and satisfy 2-of-6, and register the first homotopical structure. Then define quasi-isomorphisms as the class **inverted by** the homology functor and register the second — with the general lemma that an inverted class satisfies 2-of-6, the 2-of-6 obligation is free, so this should be an instantiation rather than a proof.
2. Over #259 and #260: define homotopy equivalences of spaces (the isomorphisms of the homotopy-classes category) and register the first structure; define weak homotopy equivalences as the class inverted by the homotopy-group functors and register the second; define the homotopy category of spaces as the localization at the second class.
3. Record Riehl's identification of that homotopy category with the category of CW complexes and homotopy classes of maps as a **disclosed stretch goal**, not part of this issue's Definition of Done — it requires genuine algebraic topology (CW approximation), exactly as #260 disclosed its own non-monic example.

In-tree donors: `Theory/Morphisms/Classes.v`, `Structure/Abelian.v`, `Instance/CMon.v`, `Construction/Quotient.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.4 Examples 6.4.7 and 6.4.8 (printed p. 238), paraphrased; `≈` on morphisms, never `=`
- [ ] Both chain-complex structures registered as homotopical categories, the quasi-isomorphism one by instantiating the inverted-class lemma
- [ ] Both space-level structures registered, and the homotopy category of spaces defined as the localization at the weak homotopy equivalences
- [ ] The CW-approximation identification explicitly disclosed in the header as out of scope, with the reason
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] docs/INHABITATION.md updated: the homotopical-category class acquires its first concrete witnesses

## Verification

```sh
nix develop --command coqc -R . Category Instance/Chain/Homotopical.v Instance/Top/Homotopical.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Chain.Homotopical. Print Assumptions chain_quasi_iso_homotopical." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the two classes in each example are genuinely nested; the quasi-isomorphism 2-of-6 proof is an instantiation of the general lemma; the CW claim is disclosed, not silently dropped.

## Dependencies

Depends on: riehl:6.4:def3 (homotopical categories and homotopical functors)
Depends on: #557 (chain complexes and homology objects)
Depends on: #259 (Top, the category of topological spaces)
Depends on: #260 (homotopy categories and pointed spaces)

<!-- catalog: {"ids":["riehl:6.4:example7","riehl:6.4:example8"],"deps":["riehl:6.4:def3","#557","#259","#260"]} -->

---8<---

```yaml
title: "Riehl 6.4: Total and point-set derived functors as Kan extensions along localization"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.4:def9, riehl:6.4:def10]
deps_item_ids: [riehl:6.4:def5, riehl:6.4:def3]
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.4 Definition 6.4.9, printed pp. 238–239 (PDF pp. 258–259), and Definition 6.4.10, printed p. 239 (PDF p. 259). Items: `riehl:6.4:def9`, `riehl:6.4:def10`.

Paraphrase: for a functor between homotopical categories with their localizations, the **right** Kan extension of the localized functor along the source localization — when it exists — is the total **left** derived functor, and dually the left Kan extension is the total right derived functor. Riehl flags the deliberate clash of handedness: a right Kan extension yields a left derived functor because left derived functors approximate the original from the left. Via the universal property of the localization these are equivalently presented as homotopical functors into the target homotopy category. A **point-set** left derived functor is a homotopical functor into the target itself, with a natural transformation to the original, whose composite with the target localization is a total left derived functor; dually on the right. Point-set derived functors are thus lifts of total derived functors along the target localization.

## Background

The definition that makes the chapter's title literal: derived functors are Kan extensions, taken along the localization at the weak equivalences. See [nLab: derived functor](https://ncatlab.org/nlab/show/derived+functor) and Wikipedia on [derived functor](https://en.wikipedia.org/wiki/Derived_functor).

## Current state in the library

Absent — and the library itself cites this very definition as motivation rather than as content.

- `Theory/Kan/Extension.v:94` reads: "total derived functors are Kan extensions along localization at the weak equivalences (Riehl, *Category Theory in Context*, §6.4)". It is a comment.
- `rg -i 'derived functor'` returns 5 hits, all prose: `Structure/Abelian.v:70,78,101,103` (Cartan–Eilenberg and Tohoku history) and the comment just quoted. The only `Derived` identifier in the tree is `Theory/Category/Raw.v:110` `DerivedEquivalence`, a hom-setoid construction for raw categories, entirely unrelated. `rg -i 'point.set|pointset'` returns 0 hits.
- **Sharpening from the verification pass:** Definition 6.4.9 is already *expressible* in the existing vocabulary — as a `LocalRightKan` of the localized functor along the source localization, over `Theory/Kan/Extension.v:154`, whose `ran_transform` and `ump_ran` are exactly the 2-cell and universal property Riehl uses — but it is nowhere written, named, or given an API. Expressible is not formalized, and the point of this issue is the naming, the API and the handedness discipline as much as the mathematics.
- The point-set refinement has nothing to refine: no derived functor of any kind exists, the required notion of a homotopical functor is itself absent, and the in-tree localization has no notion of lifting a functor along it. `resolution` in the tree means Kleisli and Eilenberg–Moore monad resolutions only; there is no cofibrant or fibrant replacement.

## Work to be done

Suggested module: `Theory/Homotopical/Derived.v` (new).

1. Define the total left derived functor of a functor between homotopical categories as a `LocalRightKan` of the localized functor along the source localization, together with its 2-cell; dually the total right derived functor as a `LocalLeftKan`. Put Riehl's handedness note in the header, prominently, so the naming does not read as a transcription error.
2. Give the equivalent presentation as homotopical functors into the target homotopy category, using the two-dimensional universal property of the localization.
3. Define point-set derived functors: a homotopical functor into the target together with a natural transformation to (resp. from) the original, whose composite with the target localization, together with the composed 2-cell, is a total derived functor. Prove explicitly that a point-set derived functor determines a total one, so the "lift along the localization" reading is a theorem and not just a slogan.
4. Prove the essential uniqueness of total derived functors as an immediate consequence of the essential uniqueness of Kan extensions, and state it in the header as the reason the definitions are well posed.

In-tree donors: `Theory/Kan/Extension.v`, `Theory/Natural/Transformation.v`, `Instance/Fun.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.4 Definitions 6.4.9 and 6.4.10 (printed pp. 238–239), paraphrased; `≈` on morphisms, never `=`
- [ ] Total derived functors defined over the existing `LocalRightKan`/`LocalLeftKan` classes rather than by a new universal property
- [ ] The handedness convention (a right Kan extension yields a **left** derived functor) documented in the header
- [ ] The homotopical-functor presentation derived from the two-dimensional universal property of the localization
- [ ] Point-set derived functors defined, and "a point-set derived functor determines a total derived functor" proved
- [ ] Essential uniqueness of total derived functors recorded as a corollary
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] The motivational comment at `Theory/Kan/Extension.v:94` updated to point at the new file instead of forward-citing the book

## Verification

```sh
nix develop --command coqc -R . Category Theory/Homotopical/Derived.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Homotopical.Derived. Print Assumptions total_left_derived_unique. Print Assumptions pointset_gives_total." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the definitions are the Kan-extension ones and reuse the existing classes; the handedness is Riehl's; the point-set/total relationship is proved.

## Dependencies

Depends on: riehl:6.4:def5 (the homotopy category and the localization functor, including its two-dimensional universal property)
Depends on: riehl:6.4:def3 (homotopical categories and homotopical functors)

<!-- catalog: {"ids":["riehl:6.4:def9","riehl:6.4:def10"],"deps":["riehl:6.4:def5","riehl:6.4:def3"]} -->

---8<---

```yaml
title: "Riehl 6.4: Deformations and the construction of derived functors"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.4:def11, riehl:6.4:def-deformable, riehl:6.4:exiii, riehl:6.4:prop12]
deps_item_ids: [riehl:6.4:def9, riehl:6.4:def5, riehl:6.4:def1]
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.4 Definition 6.4.11, printed p. 239 (PDF pp. 259–260); Proposition 6.4.12, printed p. 240 (PDF p. 260); the boldfaced "deformable" in running prose, printed p. 241 (PDF p. 261); Exercise 6.4.iii, printed p. 242 (PDF p. 262). Items: `riehl:6.4:def11`, `riehl:6.4:def-deformable`, `riehl:6.4:exiii`, `riehl:6.4:prop12`.

Paraphrase: a **left deformation** on a homotopical category is an endofunctor together with a natural weak equivalence from it to the identity; a left deformation **for** a functor is one whose image lies in a full subcategory on which the functor preserves weak equivalences. Dually for right deformations. A functor is **deformable** when it admits a deformation of the appropriate handedness. Any endofunctor equipped with a natural weak equivalence to the identity is itself a homotopical functor. And if a functor admits a left deformation, then the composite of the functor with the deformation, together with the whiskered natural transformation, is a point-set left derived functor of it — in particular the resulting universal property does not depend on which deformation was used. Attributed to Dwyer, Kan, Hirschhorn and Smith.

## Background

Deformations are the axiomatic residue of cofibrant and fibrant replacement: enough structure to compute derived functors, with no model category in sight. See [nLab: homotopical category](https://ncatlab.org/nlab/show/homotopical+category) and [nLab: derived functor](https://ncatlab.org/nlab/show/derived+functor).

## Current state in the library

Absent, and the data shape is not even present in the correct variance.

- `rg -i 'deformable'` returns **0 hits** tree-wide. `rg -i 'deformation'` returns exactly one, unrelated: `Theory/Algebra/Frobenius.v:82`, "the same surface up to deformation". (A correction recorded by the verification pass: the coverage note reported two hits, counting `Structure/Monoidal.v:101`, which actually reads "deforming the picture" and does not match the pattern.)
- No Quillen model structure, no cofibrant or fibrant replacement: `rg -i 'cofibrant|fibrant|model.categor|Quillen'` returns comments only (`Construction/Arrow.v:65`, `Structure/Factorization.v:102,104`), and `resolution` in the tree means monad resolutions.
- The ambient notion does not exist either — there is no homotopical category and no class of weak equivalences — so the predicate is not merely unstated but currently unstatable.
- The nearest structural relative is in the **wrong variance**: `Instance/Fun.v:230` — `Class Pointed {C : Category} (F : C ⟶ C) := { point : Id ⟹ F }`, with `WellPointed` at `:240` — is a *pointed* endofunctor. A left deformation is a *copointed* endofunctor (a natural transformation from the endofunctor to the identity) whose component is a weak equivalence at every object; the copointed dual is not in the tree.

## Work to be done

Suggested module: `Theory/Homotopical/Deformation.v` (new).

1. Add the copointed dual of `Instance/Fun.v`'s `Pointed` (an endofunctor with a natural transformation to the identity) so the deformation definition is built on library vocabulary rather than a bespoke record, and say in the header why the existing `Pointed` is the wrong variance.
2. Define a left deformation on a homotopical category as such a copointed endofunctor whose component is a weak equivalence at every object; define a left deformation **for** a functor by adjoining a full subcategory containing the image of the endofunctor on which the functor preserves weak equivalences; define left deformability. Do the duals.
3. Prove Exercise 6.4.iii: an endofunctor with a natural weak equivalence to the identity is a homotopical functor — the naturality square plus 2-of-6 on the three composites.
4. Prove Proposition 6.4.12: given a left deformation for a functor, the composite of the functor with the deformation, with the whiskered transformation, is a point-set left derived functor. Follow Riehl's proof — use the two-dimensional universal property of the localization to identify the functor category out of the homotopy category with the full subcategory on homotopical functors, factor an arbitrary 2-cell through the whiskered transformation by inverting the deformation component, and get uniqueness from naturality together with the fact that the deformation is a weak equivalence between objects in the endofunctor's image.
5. Record the corollary Riehl draws: the universal property obtained is independent of the deformation chosen, so any two deformations give isomorphic derived functors.

In-tree donors: `Instance/Fun.v`, `Theory/Natural/Transformation.v`, `Theory/Kan/Extension.v`, `Construction/Subcategory.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.4 Definition 6.4.11, Proposition 6.4.12, the "deformable" paragraph (printed pp. 239–241) and Exercise 6.4.iii (printed p. 242), paraphrased; `≈` on morphisms, never `=`
- [ ] The copointed dual of `Instance/Fun.v`'s `Pointed` added, with the variance issue explained in the header
- [ ] Left and right deformations, deformations **for** a functor (with the full-subcategory clause), and deformability all defined
- [ ] Exercise 6.4.iii proved
- [ ] Proposition 6.4.12 proved via the two-dimensional universal property of the localization, including the uniqueness half
- [ ] The independence-of-deformation corollary stated and proved
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Theory/Homotopical/Deformation.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Homotopical.Deformation. Print Assumptions deformation_is_homotopical. Print Assumptions deformation_gives_pointset_derived." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the deformation-for-a-functor definition carries the full-subcategory clause (not just "preserves weak equivalences"); the uniqueness half of Proposition 6.4.12 is proved.

## Dependencies

Depends on: riehl:6.4:def9 (total and point-set derived functors)
Depends on: riehl:6.4:def5 (the homotopy category and its two-dimensional universal property)
Depends on: riehl:6.4:def1 (weak equivalences and the 2-of-6 property)

<!-- catalog: {"ids":["riehl:6.4:def11","riehl:6.4:def-deformable","riehl:6.4:exiii","riehl:6.4:prop12"],"deps":["riehl:6.4:def9","riehl:6.4:def5","riehl:6.4:def1"]} -->

---8<---

```yaml
title: "Riehl 6.4: Derived functors of deformable functors are absolute, and the derived adjunction"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.4:prop13, riehl:6.4:prop14, riehl:6.4:exiv, riehl:6.4:remark15]
deps_item_ids: [riehl:6.4:prop12, riehl:6.4:def9]
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.4 Propositions 6.4.13 and 6.4.14 and Remark 6.4.15, printed p. 241 (PDF p. 261); Exercise 6.4.iv, printed p. 242 (PDF p. 262). Items: `riehl:6.4:prop13`, `riehl:6.4:prop14`, `riehl:6.4:exiv`, `riehl:6.4:remark15`.

Paraphrase: the total left derived functor of a left deformable functor is an **absolute** right Kan extension, hence in particular a pointwise one — because for any functor out of the target homotopy category the deformation is still a deformation for the composite, since that functor preserves isomorphisms. Consequently, if an adjunction between homotopical categories has total derived functors on both sides that are absolute Kan extensions, the derived functors themselves form an adjunction between the homotopy categories; the bare universal property of being a derived functor would not suffice, and absoluteness is what makes the argument go through. This is the main theorem of a paper of Maltsiniotis. Moreover the derived adjunction is the unique one compatible with the two localizations, in the sense that the square built from the original adjunction bijection, the two localization maps and the derived comparison cells commutes; a footnote notes this is not a strict morphism of adjunctions, because the localizations do not commute with the adjoints.

## Background

Absoluteness — preservation by *every* functor out of the codomain — is the strengthening of pointwiseness that lets derived functors inherit an adjunction. See [nLab: absolute Kan extension](https://ncatlab.org/nlab/show/absolute+Kan+extension) and [nLab: derived functor](https://ncatlab.org/nlab/show/derived+functor).

## Current state in the library

Both the hypothesis and the conclusion are absent.

- `rg -iE 'absolute (kan|right kan|left kan|extension)'` returns **0 hits**. Every `absolute` occurrence concerns absolute *colimits*: `Structure/Coequalizer/Split.v:9,32,98` with `functor_preserves_split` at `:104`, `Monad/Monadicity/BeckObjects.v:53,200`, `Construction/Karoubi.v:67–70`, `Comonad/Coalgebra.v:102`, `Instance/Coq/Comonad/Store.v:71`, `Construction/Slice.v:69`. The absolute-Kan definition is #604's obligation.
- `rg -i Maltsiniotis` returns 0 hits, and no derived functors of any kind exist, so the conclusion cannot be stated.
- The strongest near miss is off-target: `Theory/Equivalence/Adjunction.v:105` — `Definition Transported_Adjunction`, built as `Adjunction_Compose (Adjunction_Compose transported_adj_dom A) transported_adj_cod` with `transported_adj_dom : Kinv ⊣ K` (`:89`) and `transported_adj_cod : G ⊣ Ginv` (`:94`) — transports an adjunction along **equivalences** of both categories. A localization is not an equivalence, so it does not apply; `Adjunction/Compose.v`, `Adjunction/Continuity.v`, `Adjunction/GAFT.v` and `Adjunction/SAFT.v` produce no adjunction between localizations either.
- The foil of Riehl's footnote is likewise missing: `rg -i 'morphism of adjunction|map of adjunction|adjunction morphism'` returns 0 hits, so there is no notion of a strict morphism of adjunctions to contrast the derived adjunction with.

## Work to be done

Suggested modules: `Theory/Homotopical/Absolute.v` and `Theory/Homotopical/DerivedAdjunction.v` (new).

1. Over #604's absolute-Kan-extension definition, prove Proposition 6.4.13: the total left derived functor of a left deformable functor is an absolute right Kan extension. Follow Riehl — since any total left derived functor is isomorphic to the one built from a deformation (essential uniqueness of Kan extensions), and since for any functor out of the target homotopy category the same deformation is still a deformation for the composite (that functor preserves isomorphisms), the deformation proposition applies again and produces a right Kan extension. Record the corollary that such derived functors are in particular pointwise.
2. Prove Proposition 6.4.14 / Exercise 6.4.iv: for an adjunction between homotopical categories whose total left and right derived functors are both absolute Kan extensions, the derived functors form an adjunction between the homotopy categories. Put Riehl's warning in the header: the mere universal property of being a derived functor is **not** enough; absoluteness is load-bearing.
3. Prove Remark 6.4.15: the derived adjunction is the unique adjunction compatible with the two localizations, in the sense that for all objects the square built from the original adjunction bijection, the two localization maps on hom-sets, and the maps induced by the derived-functor comparison cells, commutes with the derived adjunction bijection. Record the footnote in the header — this is not a strict morphism of adjunctions, because the localizations do not commute with the adjoints.

In-tree donors: `Theory/Kan/Extension.v`, `Theory/Adjunction.v`, `Adjunction/Compose.v`, `Theory/Equivalence/Adjunction.v`, `Instance/Fun.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.4 Propositions 6.4.13 and 6.4.14, Remark 6.4.15 (printed p. 241) and Exercise 6.4.iv (printed p. 242), paraphrased; `≈` on morphisms, never `=`
- [ ] Proposition 6.4.13 proved, with absoluteness stated through the shared absolute-Kan definition rather than a local one, and pointwiseness recorded as a corollary
- [ ] Proposition 6.4.14 proved as a genuine `Adjunction` between the homotopy categories, with the role of absoluteness stated in the header
- [ ] Remark 6.4.15's uniqueness/compatibility square proved, and the footnote's caveat recorded
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (the derived adjunction is flagship-level)

## Verification

```sh
nix develop --command coqc -R . Category Theory/Homotopical/Absolute.v Theory/Homotopical/DerivedAdjunction.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Homotopical.DerivedAdjunction. Print Assumptions derived_of_deformable_absolute. Print Assumptions derived_adjunction. Print Assumptions derived_adjunction_unique." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: absoluteness is quantified over **all** functors out of the codomain, not just representables; the derived adjunction is an `Adjunction` instance, not a hom-set bijection stated by hand; the uniqueness square is the one Riehl describes.

## Dependencies

Depends on: riehl:6.4:prop12 (deformations construct point-set derived functors)
Depends on: riehl:6.4:def9 (total and point-set derived functors)
Depends on: #604 (absolute Kan extensions — the definition this proposition concludes)

<!-- catalog: {"ids":["riehl:6.4:prop13","riehl:6.4:prop14","riehl:6.4:exiv","riehl:6.4:remark15"],"deps":["riehl:6.4:prop12","riehl:6.4:def9","#604"]} -->

---8<---

```yaml
title: "Riehl 6.5: A functor as a (co)limit over its (co)slices, and the Yoneda equalizer and co-Yoneda coequalizer formulas"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.5:eq3, riehl:6.5:prop4, riehl:6.5:eq5, riehl:6.5:prop6]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.5 "All concepts": the numbered display (6.5.3), printed p. 243 (PDF p. 263); Proposition 6.5.4, printed p. 244 (PDF p. 264); the numbered display (6.5.5), printed p. 244 (PDF p. 264); Proposition 6.5.6, printed p. 244 (PDF p. 264). Items: `riehl:6.5:eq3`, `riehl:6.5:prop4`, `riehl:6.5:eq5`, `riehl:6.5:prop6`. (In Riehl's numbering the displays draw on the same per-section counter as the environments, so (6.5.3) and (6.5.5) are numbered displays rather than named results.)

Paraphrase: since a functor is its own right Kan extension along the identity, and such an extension is automatically pointwise, the limit formula gives the value of the functor at an object as the limit of its composite with the projection from the coslice under that object. Applying the reduction of limits to products and equalizers turns this into an equalizer presentation: the value is the equalizer of a parallel pair from the product over morphisms out of the object to the product over composable pairs, one map projecting to the composite index and the other acting by the functor on the second map. Dually, a functor is its own pointwise left Kan extension along the identity, giving the value as a colimit over the slice and a coequalizer of a parallel pair between coproducts. For set-valued functors the limit formula directly reproves the Yoneda lemma, and the equalizer form generalizes it.

## Background

The "every functor is a canonical (co)limit over its own (co)slice" formulas, from which the Yoneda and co-Yoneda lemmas fall out as the set-valued case. See [nLab: co-Yoneda lemma](https://ncatlab.org/nlab/show/co-Yoneda+lemma) and [nLab: Yoneda lemma](https://ncatlab.org/nlab/show/Yoneda+lemma).

## Current state in the library

The set-valued case exists in end and coend form, and it is a genuine special case rather than a neighbouring notion; the general statement, the (co)slice diagram, the Kan reading and the explicit (co)equalizer are all missing.

- `Theory/Coend/Yoneda.v:297` — `Definition yoneda_reduction : Sets_End_obj YoE ≅[Sets] F c := yoneda_iso.` — with `YoE` defined at `:186` by `YoE (x,y) = SetoidMorphism (C(c,x)) (F y)`. The verification pass checked by hand that the wedge condition at `YoE` reduces, after the unit laws, to `fmap[F] f (s x k) ≈ s y (f ∘ k)`, which **is** the cone condition over the coslice diagram; the element-for-element identification is real, not hand-waved.
- `Instance/Sets/End.v:59` — `Definition end_family : Type := { s : ∀ x : C, F (x, x) & ∀ x y f, … }` — is literally a Σ-type carving an equalizer out of the product over all objects; instantiated at `YoE` it gives Riehl's hom-indexed product with the wedge law as her parallel pair.
- Dually `Theory/Coend/Yoneda.v:174` — `Definition coyoneda_reduction : coend_obj (SetsCoend YoI) ≅[Sets] F c := coyoneda_iso.` — with `YoI` at `:77` sending a pair to the product setoid of a hom-set and a value; `Instance/Sets/Coend.v:75`'s `coend_eq` has a `ce_glue` constructor identifying the reindexed pairs exactly as the slice category prescribes (verified by unfolding `bimap[YoI]` by hand), and `Instance/Sets/Coend.v:163` `SetsCoend : Coend F` proves the universal property.
- Missing: **(i)** a general codomain — only the `Sets` case exists, through the concrete funext-free end and coend. **(ii)** The (co)slice-indexed diagram is never formed: `Construction/Slice.v:123` `Slice`, `:169` `Coslice` and `:140`/`:181` their comma presentations exist, but nothing builds the composite with the functor and no `Limit`/`Colimit` instance is produced over it. **(iii)** The Kan-extension reading is unstated: `Lan` and `Ran` never leave `Theory/Kan/Extension.v` and are never applied to the identity, and pointwiseness is undefined in tree. **(iv)** The (co)equalizer diagram is never exhibited — no `IsEqualizer` (`Structure/Equalizer/Fork.v:52`), `IsCoequalizer` (`Structure/Coequalizer.v:52`) or `iprod` (`Structure/Limit/Product.v`) instance witnesses it, and the two indexed products (over hom-sets, over composable pairs) are never constructed as objects. **(v)** The engine theorem — limits as equalizers of products — is **not** in tree: `Structure/Complete.v` contains exactly two statements, `Complete` at `:115` and `Cocomplete` at `:119`, and cites the reduction only as header prose at `:51–56`. It is filed as #416. (A verifier note worth carrying: `Complete_HasEqualizers` lives in `Adjunction/GAFT.v`, not in `Structure/Complete.v`, so do not look for it there.)

## Work to be done

Suggested modules: `Theory/Kan/SelfExtension.v` and `Theory/Kan/YonedaEqualizer.v` (new).

1. Prove that a functor is its own Kan extension along the identity on both sides (#603 supplies the general statement) and that such an extension is automatically pointwise (#599's definition applies trivially, since restriction along the identity is the identity functor).
2. Form the coslice diagram — the composite of `Construction/Slice.v`'s coslice projection with the functor — and prove display (6.5.3): the value at an object is the limit of that diagram, for any codomain possessing the relevant limits. Dually form the slice diagram and prove display (6.5.5).
3. Apply #416 to (6.5.3) to obtain Proposition 6.5.4: the value is the equalizer of the explicit parallel pair between the hom-indexed product and the composable-pair-indexed product, with the two maps as Riehl describes. Construct both products with `Structure/Limit/Product.v`'s `iprod` and exhibit the equalizer through `Structure/Equalizer/Fork.v`'s `IsEqualizer`, so the diagram is a first-class object and not only an isomorphism of carriers. Dually prove Proposition 6.5.6 with coproducts and `Structure/Coequalizer.v`'s `IsCoequalizer`.
4. Connect the results to the existing `Sets` end and coend forms: prove the new equalizer object is isomorphic to `Sets_End_obj YoE` and the new coequalizer object to `coend_obj (SetsCoend YoI)`, so the tree ends with one theorem in two presentations rather than two unrelated theorems.
5. Record in the header that for set-valued functors the limit formula directly reproves the Yoneda lemma (`Functor/Hom/Yoneda.v:133`, `:182`), and that the equalizer form generalizes it.

In-tree donors: `Theory/Kan/Extension.v`, `Construction/Slice.v`, `Structure/Limit.v`, `Structure/Limit/Product.v`, `Structure/Equalizer/Fork.v`, `Structure/Coequalizer.v`, `Theory/Coend/Yoneda.v`, `Instance/Sets/End.v`, `Instance/Sets/Coend.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.5 displays (6.5.3) and (6.5.5) and Propositions 6.5.4 and 6.5.6 (printed pp. 243–244), paraphrased; `≈` on morphisms, never `=`
- [ ] Both formulas proved for a **general** codomain with the relevant (co)limits, not only for setoids
- [ ] The (co)slice-indexed diagrams formed over `Construction/Slice.v` and genuine `Limit`/`Colimit` data produced
- [ ] The (co)equalizer diagrams **exhibited** — both indexed products/coproducts constructed as objects and the fork/cofork witnessed by `IsEqualizer`/`IsCoequalizer`
- [ ] The comparison with the existing `Sets` end and coend forms proved, so the presentations are reconciled rather than duplicated
- [ ] The Yoneda-lemma recovery recorded in the header with its file references
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (this joins the coend calculus to the Kan-extension spine)

## Verification

```sh
nix develop --command coqc -R . Category Theory/Kan/SelfExtension.v Theory/Kan/YonedaEqualizer.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Kan.YonedaEqualizer. Print Assumptions functor_is_coslice_limit. Print Assumptions yoneda_equalizer. Print Assumptions coyoneda_coequalizer." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the codomain is general; the equalizer is exhibited as a diagram, not only as a carrier isomorphism; the reconciliation with `yoneda_reduction`/`coyoneda_reduction` is proved.

## Dependencies

Depends on: #603 (Kan extensions along the identity and the terminal functor)
Depends on: #599 (pointwise Kan extensions and the comma-category (co)limit criterion)
Depends on: #589 (the pointwise (co)limit formula)
Depends on: #416 (limits from products and equalizers — the engine of both propositions)

<!-- catalog: {"ids":["riehl:6.5:eq3","riehl:6.5:prop4","riehl:6.5:eq5","riehl:6.5:prop6"],"deps":["#603","#599","#589","#416"]} -->

---8<---

```yaml
title: "Riehl 6.5: Adjunctions out of a presheaf category — left Kan extension along Yoneda and the nerve-realization paradigm"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.5:prop9]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.5 Proposition 6.5.9, printed pp. 245–246 (PDF pp. 265–266). Item: `riehl:6.5:prop9`.

Paraphrase: a functor from a small category to a locally small cocomplete category gives rise to an adjunction between the presheaf category on the small category and the target, whose left adjoint is left Kan extension along the Yoneda embedding and whose right adjoint sends an object of the target to the presheaf of maps out of the functor's values. Moreover **every** adjunction whose left adjoint is defined on a presheaf category and valued in a locally small cocomplete category arises this way — for the converse one applies the fact that a left adjoint preserves left Kan extensions to the identity, which is the left Kan extension of the Yoneda embedding along itself, recovering an arbitrary left adjoint as the extension of its own restriction along Yoneda.

## Background

The nerve–realization paradigm: a presheaf category is the free cocompletion, so left adjoints out of it correspond to arbitrary functors out of the site. It is the hub from which geometric realization, the nerve, the étale-space construction and the slice equivalences all follow. See [nLab: nerve and realization](https://ncatlab.org/nlab/show/nerve+and+realization) and [nLab: free cocompletion](https://ncatlab.org/nlab/show/free+cocompletion).

## Current state in the library

Absent, though the Yoneda ingredients are all in place.

- `rg -ci 'nerve' / 'Lan_y' / 'Lan y' / 'singular functor'` returns 0 files each. The only Kan-relevant occurrences are comments: `Theory/Kan/Extension.v:36` (the nLab nerve-and-realization URL) and `:90–93` ("Geometric realization is the left Kan extension of a cosimplicial space along the Yoneda embedding, the nerve its restricted-Yoneda right adjoint").
- `Lan` never leaves `Theory/Kan/Extension.v`, so no adjunction anywhere is built from a left Kan extension, and `Lan` is never applied to any concrete functor, in particular never to a Yoneda embedding.
- No universal property of a presheaf category is stated: `Construction/Day.v:110–111` and `Theory/Sheaf.v:117` mention "free (monoidal) cocompletion" in header prose only, and `Presheaves` (`Theory/Sheaf.v:127`) is a bare abbreviation.
- The ingredients are present: `Functor/Hom.v:146` — `Definition Curried_CoHom (C : Category) : C ⟶ [C^op, Sets] := Curried_Hom C^op` — with the notation at `:149`, and full faithfulness at `Functor/Hom/Yoneda.v:231` `Yoneda_Embedding : ∀ A B : C, Presheaves [Hom ─,A] [Hom ─,B] ≊ A ~> B`.
- The nearest in-tree adjunction characterisation is off-target: `Theory/Profunctor/Adjunction.v:70` `representable_adjunction : (F ⊣ U) ↔ (Repr_left F ≅[[D^op ∏ C, Sets]] Repr_right U)` is about profunctor representability, not about left adjoints out of presheaf categories.
- The converse half's prerequisite — a left adjoint preserves left Kan extensions — is exactly the abandoned `left_adjoints_preserve` (`Theory/Kan/Extension.v:386–438`, three `admit`s, `Abort.` at `:438`, honestly disclosed at `:376–384`); replacing it is already in #598's Definition of Done.

## Work to be done

Suggested module: `Theory/Kan/Presheaf.v` (new).

1. For a functor from a small category to a locally small cocomplete category, construct the left Kan extension along the Yoneda embedding using #590 for existence and #589 for the formula, and note by #591 that it genuinely extends the original functor with an invertible (indeed identity) unit, since Yoneda is fully faithful.
2. Define the right adjoint sending an object of the target to the presheaf of maps out of the functor's values, functorial by postcomposition.
3. Prove the adjunction by Riehl's chain of isomorphisms: the density theorem (#346) expresses a presheaf as a colimit of representables, continuity of the hom-functor is applied twice, the definition of the right adjoint is unfolded, and #589's formula together with the identification of the Yoneda comma category with the category of elements (#716, generalised by the comma-indexing issue) closes the loop.
4. Prove the converse: apply #598 (a left adjoint preserves left Kan extensions) to #600's identity-as-`Lan`-of-Yoneda-along-itself to recover an arbitrary left adjoint out of a presheaf category as the left Kan extension of its own restriction along Yoneda, so the correspondence is a genuine bijection up to isomorphism.
5. State the result in a form the applications can consume directly — it is the hub for the geometric-realization, étale-space and slice-equivalence exercises of §6.5 — and record in the header that this is the library's free-cocompletion statement.

In-tree donors: `Functor/Hom.v`, `Functor/Hom/Yoneda.v`, `Theory/Kan/Extension.v`, `Instance/Fun.v`, `Structure/Limit.v`, `Theory/Adjunction.v`, `Construction/Comma.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.5 Proposition 6.5.9 (printed pp. 245–246), paraphrased; `≈` on morphisms, never `=`
- [ ] The left adjoint constructed as a left Kan extension along the existing Yoneda embedding, not as a bespoke colimit
- [ ] The adjunction proved as an `Adjunction` instance
- [ ] The **converse** proved: every left adjoint out of a presheaf category into a locally small cocomplete category is the left Kan extension of its restriction along Yoneda
- [ ] The result stated so the §6.5 applications can instantiate it without re-deriving the adjunction
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter`
- [ ] `Print Assumptions` closed under the global context for each principal artifact
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] CLAUDE.md Key Files index updated (the free-cocompletion/nerve-realization theorem is flagship-level)

## Verification

```sh
nix develop --command coqc -R . Category Theory/Kan/Presheaf.v
nix develop --command bash -c 'echo "Require Import Category.Theory.Kan.Presheaf. Print Assumptions lan_yoneda_adjunction. Print Assumptions left_adjoint_is_lan_yoneda." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: both directions are proved; the density theorem is consumed rather than re-proved; the smallness and cocompleteness hypotheses match §6.5.

## Dependencies

Depends on: #590 (existence of Kan extensions from (co)completeness)
Depends on: #589 (the pointwise (co)limit formula)
Depends on: #591 (fully faithful `K` gives a genuine extension — applied at Yoneda)
Depends on: #346 (the density theorem: set-valued functors as colimits of representables)
Depends on: #600 (dense and codense functors — the identity as the left Kan extension of Yoneda along itself)
Depends on: #598 (a left adjoint preserves left Kan extensions — the converse half)
Depends on: #716 (the category of elements is equivalent to the Yoneda slice)

<!-- catalog: {"ids":["riehl:6.5:prop9"],"deps":["#590","#589","#591","#346","#600","#598","#716"]} -->

---8<---

```yaml
title: "Riehl 6.5: The sheaf and etale-space adjunction from the inclusion of opens into spaces over a base"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:6.5:exiv]
deps_item_ids: [riehl:6.5:prop9]
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.5 Exercise 6.5.iv, printed p. 248 (PDF p. 268). Item: `riehl:6.5:exiv`.

Paraphrase: for a fixed space there is a natural functor from its poset of open subsets into the category of spaces over it, sending an open subset to its inclusion. Applying the presheaf-adjunction theorem to that functor produces an adjunction between the presheaf category on the opens and the slice category of spaces over the base. Since every adjunction restricts to an adjoint equivalence between the subcategories on which the unit and counit are invertible, this one restricts to an adjoint equivalence between the sheaves on the space and the étale spaces over it.

## Background

The classical equivalence between sheaves and étale spaces, obtained as the fixed-point restriction of the adjunction manufactured by left Kan extension along Yoneda. See [nLab: étale space](https://ncatlab.org/nlab/show/etale+space) and [nLab: sheaf](https://ncatlab.org/nlab/show/sheaf).

## Current state in the library

Absent, and both of the tools the exercise composes are missing as well.

- There is no category of topological spaces: `rg -in 'Topological'` returns only bibliography and essay prose; `Construction/Slice.v:80`'s remark that "covering spaces of `X` form a full subcategory of `Top/X`" is an essay sentence about the general slice construction, not an in-tree object. `Top` is filed as #259.
- `rg -ni 'locale|frame of opens|open subset'` returns **0 hits**, so the poset of opens does not exist; it is filed as #268. There is no étale space, local homeomorphism, stalk or germ anywhere outside the SGA 4 bibliography lines in `Structure/Topos.v`.
- The restriction principle is also absent: `rg -ni 'restricts to an|fixed subcategor'` returns 0 hits, so the statement that an adjunction restricts to an adjoint equivalence between the fixed subcategories has no in-tree form. It is filed as #386.
- `Theory/Sheaf/Category.v:81`'s `Sheaves` is `Sub (@Presheaves C Sets) Sheaves_sub` over an **abstract** site; it is never instantiated at the opens of a space and never compared with any category of spaces. (Its header already discloses that the inherited sheaf predicate is per-leg and vacuous beyond subsingleton fibres, so the matching-family re-founding needed for a faithful sheaf condition is itself a known open item; #890 owns the honest sheaf condition.)

## Work to be done

Suggested module: `Instance/Top/Etale.v` (new).

1. Over #268's poset of opens and #259's category of spaces, define the functor sending an open subset to its inclusion as an object of the slice over the base, and prove functoriality.
2. Instantiate the presheaf-adjunction theorem at that functor, obtaining the adjunction between the presheaf category on the opens and the slice category — the left adjoint the étale-space construction (left Kan extension along Yoneda), the right adjoint the sheaf of sections.
3. Define local homeomorphisms and the full subcategory of étale spaces over the base.
4. Apply #386 to restrict the adjunction to an adjoint equivalence between its fixed subcategories, and prove those subcategories are exactly the sheaves (in #890's matching-family sense, instantiated at the site of opens) and the étale spaces.
5. Disclose in the header that `Theory/Sheaf/Category.v`'s existing abstract `Sheaves` uses a weaker per-leg predicate, and say which sheaf notion this file uses and why.

In-tree donors: `Construction/Slice.v`, `Instance/Fun.v`, `Theory/Sheaf.v`, `Theory/Sheaf/Category.v`, `Theory/Adjunction.v`, `Theory/Equivalence/Adjoint.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.5 Exercise 6.5.iv (printed p. 248), paraphrased; `≈` on morphisms, never `=`
- [ ] The opens-into-slice functor defined and the adjunction obtained by **instantiating** the presheaf-adjunction theorem, not re-derived
- [ ] Local homeomorphisms and étale spaces defined
- [ ] The adjoint equivalence obtained by restricting to the fixed subcategories, and those subcategories **identified** with the sheaves and the étale spaces
- [ ] The sheaf notion used is stated in the header, together with why the existing abstract `Sheaves` predicate is or is not adequate here
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] docs/INHABITATION.md updated: the sheaf development acquires a concrete site and a concrete equivalence

## Verification

```sh
nix develop --command coqc -R . Category Instance/Top/Etale.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Top.Etale. Print Assumptions opens_slice_adjunction. Print Assumptions sheaves_etale_equivalence." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the adjunction is an instance of the general theorem; the two fixed subcategories are identified by proof; the sheaf condition used is the honest one.

## Dependencies

Depends on: riehl:6.5:prop9 (adjunctions out of a presheaf category — the theorem being instantiated)
Depends on: #268 (Open(X) and the presheaf of continuous functions)
Depends on: #259 (Top, the category of topological spaces)
Depends on: #386 (an adjunction restricts to an adjoint equivalence on the fixed subcategories)
Depends on: #890 (sheaves on a topological space — matching families and unique gluing)

<!-- catalog: {"ids":["riehl:6.5:exiv"],"deps":["riehl:6.5:prop9","#268","#259","#386","#890"]} -->

---8<---

```yaml
title: "Riehl 6.5: Geometric realization and the total singular complex"
labels: [book:riehl, kind:exercise, coverage-gap]
projects: [10]
covers: [riehl:6.5:exvi]
deps_item_ids: [riehl:6.5:prop9]
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.5 Exercise 6.5.vi, printed p. 248 (PDF p. 268). Item: `riehl:6.5:exvi`.

Paraphrase: apply the presheaf-adjunction theorem to the functor from the simplex category to spaces sending an ordinal to the topological simplex on its elements. The left adjoint, defined by left Kan extension along Yoneda, is geometric realization; the right adjoint is the total singular complex used to define singular homology; together they give the realization–singular adjunction between simplicial sets and spaces.

## Background

The archetype of the nerve–realization paradigm, and the reason the general theorem is worth having. See [nLab: geometric realization](https://ncatlab.org/nlab/show/geometric+realization) and [nLab: singular simplicial complex](https://ncatlab.org/nlab/show/singular+simplicial+complex).

## Current state in the library

Absent; both the domain and the codomain of the adjunction are unnameable today.

- "Geometric realization" occurs exactly twice, both comments: `Theory/Kan/Extension.v:90` ("Geometric realization is the left Kan extension of a cosimplicial space along the Yoneda embedding, the nerve its restricted-Yoneda right adjoint") and `Structure/Coend.v:113` (realization as a single coend).
- `rg -i 'singular'` returns **0 hits** in the entire tree: there is no singular complex and no such functor.
- `rg -n 'Definition Top|Instance Top|Category Top|Program Definition Top'` returns 0 hits and `ls Instance/` has no `Top.v`; `rg -nw 'Delta'` returns 0 hits and there is no `Delta.v`/`Simplex.v`/`sSet.v`. The simplex category is filed as #225, simplicial sets as #515, `Top` as #259, and the cosimplicial-space functor itself as #514 — which supplies the functor only, not the adjunction.

## Work to be done

Suggested module: `Instance/Delta/Singular.v` (new).

1. Over #514's functor from the simplex category to spaces, instantiate the presheaf-adjunction theorem, obtaining the left adjoint as the left Kan extension along Yoneda and the right adjoint as the presheaf of maps out of the topological simplices.
2. Prove the left adjoint computes geometric realization in the expected form — the pointwise colimit formula presents it as a quotient of a coproduct of topological simplices indexed by the simplices of the simplicial set — and prove the right adjoint is the total singular complex.
3. Record in the header that this is the standard witness for the general theorem, and that singular homology is defined from the right adjoint (without formalizing homology here).

In-tree donors: `Instance/Fun.v`, `Theory/Kan/Extension.v`, `Structure/Coend.v`, `Structure/Limit.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.5 Exercise 6.5.vi (printed p. 248), paraphrased; `≈` on morphisms, never `=`
- [ ] The adjunction obtained by **instantiating** the presheaf-adjunction theorem, not re-derived
- [ ] Geometric realization identified with the expected quotient-of-simplices description via the colimit formula
- [ ] The right adjoint identified as the total singular complex
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Instance/Delta/Singular.v
nix develop --command bash -c 'echo "Require Import Category.Instance.Delta.Singular. Print Assumptions realization_singular_adjunction." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the adjunction is an instance, not a hand construction; the realization description is derived from the colimit formula.

## Dependencies

Depends on: riehl:6.5:prop9 (adjunctions out of a presheaf category)
Depends on: #514 (the geometric-realization functor from the simplex category to spaces)
Depends on: #515 (simplicial sets and simplicial objects)
Depends on: #225 (the simplicial category Δ)
Depends on: #259 (Top, the category of topological spaces)

<!-- catalog: {"ids":["riehl:6.5:exvi"],"deps":["riehl:6.5:prop9","#514","#515","#225","#259"]} -->

---8<---

```yaml
title: "Riehl 6.5: The ultrafilter monad as the codensity monad of the inclusion of finite sets"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.5:example12]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.5 Example 6.5.12, printed p. 247 (PDF p. 267). Item: `riehl:6.5:example12`.

Paraphrase: familiar monads arise as codensity monads. The codensity monad of the inclusion of finite sets into sets is the ultrafilter monad. The limit formula presents its value at a set as a limit over the comma category of finite quotients; that limit is the set of cones with singleton summit, and by the cone/natural-transformation correspondence that is the set of natural transformations from the hom-functor into the inclusion to the inclusion. A component of such a transformation takes a function into a finite set and returns an element of it; an ultrafilter induces one by returning the unique element whose fibre belongs to the ultrafilter. The result is attributed to Kennison and Gildenhuys, with proofs cited to Leinster.

## Background

The codensity monad measures how far a functor is from being codense; for the inclusion of finite sets into sets, the answer is exactly the ultrafilter monad, whose algebras are the compact Hausdorff spaces. See [nLab: codensity monad](https://ncatlab.org/nlab/show/codensity+monad) and [nLab: ultrafilter monad](https://ncatlab.org/nlab/show/ultrafilter+monad).

## Current state in the library

Absent, and — the sharpest point — even the functor whose codensity monad is to be taken does not exist.

- Every "ultrafilter" occurrence in the tree is prose: `Theory/Monad.v:65` (the Manes remark in a background essay that the algebras of the ultrafilter monad are the compact Hausdorff spaces) and `Theory/Kan/Extension.v:39`, `:86` (the Leinster citation, and the sentence naming this very example). There is no filter or ultrafilter datatype; the ultrafilter functor and unit are #700's obligation and the monad structure #998's.
- There is **no functor from the skeletal finite sets into setoids anywhere in the tree**: `rg -n 'FinSet' | rg -i sets` yields only `Theory/Lawvere/Sets.v`, prose in `Structure/Pullback.v` and prose in `Construction/PROP/Signature.v`. So the codensity monad of that inclusion has no in-tree functor to be taken of, quite apart from the missing codensity construction.
- The codensity monad itself does not exist: `rg -ni 'codensity|codense'` returns 7 hits, all inside the background essay of `Theory/Kan/Extension.v` (`:35`, `:39`, `:83`, `:85`, `:103`, `:105`, `:108`), none a definition, class or theorem. It is filed as #605.

## Work to be done

Suggested modules: `Instance/FinSet/ToSets.v` and `Monad/Instance/Codensity/Ultrafilter.v` (new).

1. Define the faithful functor from `Instance/FinSet.v`'s skeletal finite sets into `Instance/Sets.v`, and prove its functor laws. This is a missing piece in its own right — the tree currently has no comparison functor between those two instances.
2. Compute the codensity monad of that functor with #589's limit formula: the value at a set is the limit over the comma category whose objects are the functions from that set into a finite set. Use #599's cone/natural-transformation correspondence to identify that limit with the set of natural transformations from the hom-functor into the inclusion to the inclusion.
3. Prove that set is in bijection with the ultrafilters on the set, naturally in the set — the forward map sends an ultrafilter to the transformation returning the unique element whose fibre lies in the ultrafilter; the backward map recovers the ultrafilter from the component at the characteristic functions.
4. Prove the induced monad structure — the unit and multiplication produced by #605's codensity construction — coincides with #998's monad structure on the ultrafilter functor, so the tree ends with one monad presented two ways.
5. Cite Kennison–Gildenhuys and Leinster in the header, and record the connection to the Manes remark already in `Theory/Monad.v:65`.

In-tree donors: `Instance/FinSet.v`, `Instance/Sets.v`, `Theory/Kan/Extension.v`, `Construction/Comma.v`, `Theory/Monad.v`, `Structure/Limit.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.5 Example 6.5.12 (printed p. 247), paraphrased; `≈` on morphisms, never `=`
- [ ] The functor from the skeletal finite sets into setoids defined with its laws proved
- [ ] The codensity monad computed by the **limit formula**, with the cone/natural-transformation step used explicitly
- [ ] The bijection with ultrafilters proved, and proved natural
- [ ] The codensity monad structure proved to agree with the independently constructed ultrafilter monad
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] docs/INHABITATION.md updated: the codensity monad acquires its first concrete computation

## Verification

```sh
nix develop --command coqc -R . Category Instance/FinSet/ToSets.v Monad/Instance/Codensity/Ultrafilter.v
nix develop --command bash -c 'echo "Require Import Category.Monad.Instance.Codensity.Ultrafilter. Print Assumptions codensity_finset_is_ultrafilter." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the identification goes through the limit formula rather than being asserted; naturality is proved; the two monad structures are compared, not assumed equal.

## Dependencies

Depends on: #605 (the codensity monad and codensity as the right Kan extension of a functor along itself)
Depends on: #998 (the ultrafilter monad on Sets)
Depends on: #700 (the ultrafilter functor and its unit)
Depends on: #589 (the pointwise (co)limit formula)
Depends on: #599 (pointwise Kan extensions and the cone/natural-transformation correspondence)

<!-- catalog: {"ids":["riehl:6.5:example12"],"deps":["#605","#998","#700","#589","#599"]} -->

---8<---

```yaml
title: "Riehl 6.5: The codensity monad of the inclusion of fields into commutative rings"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.5:example11]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.5 Example 6.5.11, printed p. 247 (PDF p. 267). Item: `riehl:6.5:example11`.

Paraphrase: the inclusion of fields into commutative rings has no left adjoint, since such a functor would have to send the integers to an initial field, which does not exist. It nevertheless has a codensity monad, whose value at a commutative ring is the product, over the prime ideals of that ring, of the fields of fractions of the corresponding quotients — each quotient being an integral domain because the ideal is prime. Proofs are cited to Leinster.

## Background

A codensity monad exists whenever the relevant limits do, even when no adjoint does; this is the standard example of that phenomenon in commutative algebra. See [nLab: codensity monad](https://ncatlab.org/nlab/show/codensity+monad) and Wikipedia on the [field of fractions](https://en.wikipedia.org/wiki/Field_of_fractions).

## Current state in the library

Absent, along with all of commutative algebra.

- `rg -n 'Ring'` returns **zero hits** in the entire tree: there is no ring theory of any kind. The algebraic structures in tree are `Structure/Group.v` (internal group objects), `Structure/Monoid.v`, and `Instance/CMon.v` (commutative monoids over setoids — the only concrete algebraic instance).
- `rg -ni '\bCRing\b|commutative ring|\bField\b|integral domain|prime ideal|field of fractions|\bSpec\b'` returns only false positives on Coq record *fields*. `ls Instance/` contains no `Ring`, `Field`, `CRing` or `Domain`.
- The codensity monad itself does not exist (its 7 occurrences are all header prose in `Theory/Kan/Extension.v`); it is filed as #605.
- The no-left-adjoint half of the example is already filed as #971, which owns the category of fields.
- This is **not** out of scope: fields and commutative rings are ordinary formalizable categories in this setting (commutative monoids already are); they are simply absent.

## Work to be done

Suggested modules: `Instance/CRing.v` and `Monad/Instance/Codensity/Fields.v` (new).

1. Over #971's category of fields, build the category of commutative rings and the inclusion functor, following the setoid-based pattern of `Instance/CMon.v` (carrier setoid plus operations plus laws, homomorphisms respecting `≈`).
2. Define the prime spectrum as the set of prime ideals, the quotient by a prime ideal, and its field of fractions; prove the quotient is an integral domain and the construction functorial where needed.
3. Construct the product over the spectrum and prove it is the codensity monad of the inclusion — i.e. it is the right Kan extension of the inclusion along itself, with #605's unit and multiplication.
4. Record in the header that this exhibits a codensity monad for a functor with no left adjoint (the fact filed as #971), which is the point of the example, and cite Leinster.

In-tree donors: `Instance/CMon.v` (the setoid-algebra pattern), `Structure/Limit/Product.v` (indexed products), `Theory/Kan/Extension.v`, `Theory/Monad.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.5 Example 6.5.11 (printed p. 247), paraphrased; `≈` on morphisms, never `=`
- [ ] The category of commutative rings and the inclusion of fields constructed on the existing setoid-algebra pattern
- [ ] The prime spectrum, the quotient by a prime, and the field of fractions constructed, with the integral-domain property proved
- [ ] The product over the spectrum proved to be the right Kan extension of the inclusion along itself, with the codensity unit and multiplication
- [ ] The header records that this functor has no left adjoint, cross-referencing that result
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits

## Verification

```sh
nix develop --command coqc -R . Category Instance/CRing.v Monad/Instance/Codensity/Fields.v
nix develop --command bash -c 'echo "Require Import Category.Monad.Instance.Codensity.Fields. Print Assumptions field_codensity_monad." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the monad is proved to be the Kan extension, not merely defined by the formula; the integral-domain step is proved; the setoid discipline is respected in the algebraic definitions.

## Dependencies

Depends on: #605 (the codensity monad and codensity as the right Kan extension of a functor along itself)
Depends on: #971 (the forgetful functors out of the category of fields admit no adjoints — the category of fields, and the no-left-adjoint half of this example)

<!-- catalog: {"ids":["riehl:6.5:example11"],"deps":["#605","#971"]} -->

---8<---

```yaml
title: "Riehl 6.5: The Giry monad as a codensity monad"
labels: [book:riehl, kind:theory, coverage-gap]
projects: [10]
covers: [riehl:6.5:example13]
deps_item_ids: []
deps_pending: []
```

## Source

Riehl, *Category Theory in Context*, 2nd ed. (printed = PDF − 20), §6.5 Example 6.5.13, printed pp. 247–248 (PDF pp. 267–268). Item: `riehl:6.5:example13`.

Paraphrase: the Giry monad is the codensity monad of the inclusion into measurable spaces of the subcategory whose objects are the finite powers of the unit interval with its Borel structure, together with the measurable space of sequences in the interval converging to zero; viewing those objects as convex subspaces of Euclidean space, the morphisms are taken to be all affine maps between them. Omitting the space of sequences — keeping only the finite powers of the interval and the affine maps — generates instead the variant of the Giry monad for finitely additive probability measures. Cited to Avery.

## Background

Probability monads as codensity monads: the whole of the Giry construction is recovered from a small subcategory of convex spaces by a right Kan extension along the inclusion. See [nLab: Giry monad](https://ncatlab.org/nlab/show/Giry+monad) and [nLab: codensity monad](https://ncatlab.org/nlab/show/codensity+monad).

## Current state in the library

Absent; the ambient category, the subcategory and the codensity construction are all missing.

- `rg -ni 'giry'` returns 2 hits, both comments in `Structure/Monoidal/Markov.v` (`:56` an nLab URL, `:65` prose about the Kleisli category of the Giry monad); no Giry monad is constructed. `rg -n 'Meas\b|sigma-algebra|Borel|measurable space'` returns a single comment: there is no category of measurable spaces. The Giry monad and that category are filed as #996.
- `rg -ni 'unit interval|affine map|convex'` returns **0 hits**, so neither the finite powers of the interval nor the affine maps between them exist; the subcategory of the example is entirely absent.
- The library's probability development is synthetic, and says so honestly: `Structure/Monoidal/Markov.v:68–70` records that none of the concrete probability examples is formalized and that the sole in-tree instance route is the cartesian one, so the abstract Markov theory currently has no concrete model — exactly what docs/INHABITATION.md tracks.
- The codensity monad does not exist (7 occurrences, all header prose in `Theory/Kan/Extension.v`); it is filed as #605.

## Work to be done

Suggested module: `Monad/Instance/Codensity/Giry.v` (new).

1. Over #996's category of measurable spaces and its Giry monad, build the subcategory of the example: objects the finite powers of the unit interval with the Borel structure together with the space of sequences converging to zero, morphisms the affine maps; prove it is a subcategory and construct the inclusion.
2. Prove the right Kan extension of the inclusion along itself exists — Riehl's footnote to the definition makes clear that "sufficient limits" means exactly those needed for a *pointwise* right Kan extension, so state the hypothesis through #599's criterion — and prove the resulting codensity monad is the Giry monad.
3. Prove the variant: omitting the sequence space yields the finitely-additive probability monad, and state precisely how the two differ.
4. Cite Avery in the header, and record that this gives the synthetic Markov development a concrete model route.

In-tree donors: `Structure/Monoidal/Markov.v`, `Construction/Subcategory.v`, `Theory/Kan/Extension.v`, `Theory/Monad.v`, `Structure/Limit.v`.

## Definition of Done

- [ ] Statement fidelity to Riehl §6.5 Example 6.5.13 (printed pp. 247–248), paraphrased; `≈` on morphisms, never `=`
- [ ] The subcategory of convex spaces and affine maps constructed, including the sequence space, with the inclusion functor
- [ ] Existence of the pointwise right Kan extension of the inclusion along itself proved, with the limits actually required stated explicitly
- [ ] The codensity monad proved to be the Giry monad
- [ ] The finitely-additive variant proved for the subcategory without the sequence space, with the difference stated
- [ ] No `Admitted`, `admit`, or new `Axiom`/`Parameter` beyond the enumerated `Instance/`-layer stdlib axioms
- [ ] `Print Assumptions` reported for each principal artifact and checked against docs/AXIOMS.md
- [ ] New file(s) registered in `_CoqProject`
- [ ] Full `make` green on Rocq 9.1
- [ ] Builds on Coq 8.19/8.20 (nix targets)
- [ ] `make todo` adds no new hits
- [ ] docs/INHABITATION.md updated if this supplies the Markov development with a concrete model

## Verification

```sh
nix develop --command coqc -R . Category Monad/Instance/Codensity/Giry.v
nix develop --command bash -c 'echo "Require Import Category.Monad.Instance.Codensity.Giry. Print Assumptions giry_is_codensity. Print Assumptions finitely_additive_variant." | coqtop -R . Category'
nix develop --command make && nix develop --command make todo
nix build .#category-theory_8_20 && nix build .#category-theory_8_19
```

Review items: the identification is with #996's Giry monad, not a re-definition; the required-limits hypothesis is stated through the pointwise criterion; the variant is proved, not asserted.

## Dependencies

Depends on: #605 (the codensity monad and codensity as the right Kan extension of a functor along itself)
Depends on: #996 (the Giry monad on measurable spaces)
Depends on: #599 (pointwise Kan extensions — the "sufficient limits" hypothesis of Riehl's footnote)

<!-- catalog: {"ids":["riehl:6.5:example13"],"deps":["#605","#996","#599"]} -->
