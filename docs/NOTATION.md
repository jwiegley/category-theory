# Notation reference

A one-page reference for the exported notations of
`jwiegley/category-theory`. Every line below is `Notation` (not
`Reserved Notation`); they all become visible on `Require Import` of
the named file plus the right `Open Scope`.

## Naming conventions

- Plain forms (`f ∘ g`, `x ~> y`, `x ≅ y`, …) use the default scope.
- Disambiguated forms (`f ∘[C] g`, `x ~{C}~> y`, `x ⨂[M] y`, …) take
  an explicit category / monoidal-instance argument and are needed when
  Coq's typeclass inference can't pick the right instance.
- Bracketed forms (`obj[C]`, `id[x]`, `fobj[F]`, `mu[Mon]`) are
  projections — they read as "the field of the named structure."

## Scopes

| Scope            | Opened by                                          | Contains                       |
|------------------|----------------------------------------------------|--------------------------------|
| `category_scope` | `Theory/Category.v` (via `Open Scope category_scope.`) | `obj[]`, `~>`, `~{}~>`, `<~`, `<~{}~`, `≅`, `≅[]` |
| `morphism_scope` | `Theory/Category.v`                                | `f ∘ g`, `f ∘[C] g`, `id[x]`, `id{C}`, `≈[C]`, `f ⁻¹` |
| `functor_scope`  | `Theory/Functor.v`                                 | `C ⟶ D`, `fobj[F]`, `Id[C]`, `(⨂)` |
| `object_scope`   | implicit (used by `x ⨂ y` and `⟦n⟧`)               | `⨂`, `⨂[M]`, `⟦n⟧`, `iter_tensor n` |
| `isomorphism_scope` | `Theory/Isomorphism.v`                          | `f ⊙ g` (iso composition)      |
| `nat_scope`      | Coq stdlib                                         | Numerals `0`, `1`, ..., `+`     |

## Core morphism / category notations

| Notation        | Definition                                                  | Source file                |
|-----------------|-------------------------------------------------------------|----------------------------|
| `x ~> y`        | `@hom _ x y` — hom-set in the inferred category             | `Theory/Category.v`        |
| `x ~{C}~> y`    | `@hom C x y` — hom-set with explicit category               | `Theory/Category.v`        |
| `x <~ y`        | `@hom _ y x` — opposite hom direction                       | `Theory/Category.v`        |
| `x <~{C}~ y`    | `@hom C y x` — explicit-category opposite                   | `Theory/Category.v`        |
| `f ∘ g`         | morphism composition                                        | `Theory/Category.v`        |
| `f ∘[C] g`      | explicit-category composition                               | `Theory/Category.v`        |
| `f ≈ g`         | setoid equivalence on a hom-set (the universal `=` for morphisms) | `Theory/Category.v` (via `Setoid`) |
| `f ≈[C] g`      | explicit-category setoid equivalence                        | `Theory/Category.v`        |
| `id[x]`         | identity morphism at `x`                                    | `Theory/Category.v`        |
| `id{C}`         | identity morphism in `C` (object inferred)                  | `Theory/Category.v`        |
| `obj[C]`        | object type of category `C`                                 | `Theory/Category.v`        |
| `hom[C]`        | hom-set family of category `C`                              | `Theory/Category.v`        |

**Always use `≈`, NEVER `=`, between morphisms.** The library is
setoid-based; morphism `=` is a category error (and won't proof-check).

## Isomorphisms

| Notation     | Definition                                          | Source file              |
|--------------|-----------------------------------------------------|--------------------------|
| `x ≅ y`      | `Isomorphism x y` in the inferred category          | `Theory/Isomorphism.v`   |
| `x ≅[C] y`   | `Isomorphism x y` in `C`                            | `Theory/Isomorphism.v`   |
| `f ⁻¹`       | `from f` — inverse of an isomorphism                | `Theory/Isomorphism.v`   |
| `f ⊙ g`      | `iso_compose f g` — composition of isomorphisms     | `Theory/Isomorphism.v`   |

## Functors and natural transformations

| Notation       | Definition                                       | Source file               |
|----------------|--------------------------------------------------|---------------------------|
| `C ⟶ D`        | `Functor C D`                                    | `Theory/Functor.v`        |
| `Id[C]`        | identity functor on `C`                          | `Theory/Functor.v`        |
| `F ◯ G`        | functor composition                              | `Theory/Functor.v`        |
| `fobj[F]`      | object-action of `F`                             | `Theory/Functor.v`        |
| `F ⟹ G`        | natural transformation `F → G`                   | `Theory/Natural/Transformation.v` |
| `F ∙ G`        | vertical composition of nat. transformations     | `Theory/Natural/Transformation.v` |
| `N ⊲ F`        | right whisker (post-compose by `F`)              | `Theory/Natural/Transformation.v` |
| `F ⊳ N`        | left whisker (pre-compose by `F`)                | `Theory/Natural/Transformation.v` |

## Monoidal / symmetric monoidal

| Notation     | Definition                                                  | Source file              |
|--------------|-------------------------------------------------------------|--------------------------|
| `x ⨂ y`      | `(tensor on objects) (x, y)` in inferred monoidal           | `Structure/Monoidal.v`   |
| `x ⨂[M] y`   | explicit-monoidal `(tensor M) (x, y)`                       | `Structure/Monoidal.v`   |
| `f ⨂ g`      | `bimap` of two morphisms via inferred monoidal              | `Structure/Monoidal.v`   |
| `f ⨂[M] g`   | explicit-monoidal `bimap[tensor M] f g`                     | `Structure/Monoidal.v`   |
| `(⨂)`        | the tensor bifunctor itself                                 | `Structure/Monoidal.v`   |
| `I`          | the monoidal unit (projection from a `Monoidal` instance)   | `Structure/Monoidal.v`   |
| `braid`      | the braiding (from a `BraidedMonoidal` instance)            | `Structure/Monoidal/Braided.v` |

## Algebraic structures

| Notation         | Definition                            | Source file                          |
|------------------|---------------------------------------|--------------------------------------|
| `mu[Mon]`        | `μ` of an explicit `Monoid` instance  | `Theory/Algebra/Monoid.v`            |
| `eta[Mon]`       | `η` of an explicit `Monoid` instance  | `Theory/Algebra/Monoid.v`            |
| `delta[Co]`      | `δ` of an explicit `Comonoid` instance | `Theory/Algebra/Comonoid.v`          |
| `epsilon[Co]`    | `ε` of an explicit `Comonoid` instance | `Theory/Algebra/Comonoid.v`          |

Flat projections — preferred for new code:

  `scfa_mu`, `scfa_eta`, `scfa_delta`, `scfa_epsilon`
  (in `Theory/Algebra/SpecialCommutativeFrobenius.v`)

  `cmon_mu`, `cmon_eta`
  (in `Theory/Algebra/CommutativeMonoid.v`)

## PROP notations

| Notation     | Definition                                                | Source file              |
|--------------|-----------------------------------------------------------|--------------------------|
| `⟦n⟧`        | `prop_of_nat P n` — the PROP-object of arity `n`           | `Construction/PROP.v`    |

This notation is bound INSIDE `Section PROPLemmas` (which sets
`Context (P : PROP)`) and unfolds via the implicit `P` to
`@prop_of_nat P n`. To use it outside that section, redefine it locally
with your concrete `P`.

## Library-foundational symbols (not notations)

| Symbol       | Meaning                                                |
|--------------|--------------------------------------------------------|
| `Setoid`     | Setoid record (carrier + equivalence)                  |
| `Setoid_Theory` | proof-of-setoidness                                 |
| `Equivalence` | `Equivalence ≈` is the universal homset equivalence claim |
| `Proper`     | morphism respects pointwise equivalence                |

A `Setoid` is **automatically opened** as soon as the file declaring it
is required (no extra `Open Scope` needed).

## Migration note: morphism equality

If you are migrating from another project that used `=` between
morphisms, you must change EVERY one to `≈`. The library's `Setoid`
instances make all `≈` rewrites work via the standard `setoid_rewrite`
plumbing, but `=` between morphisms is, in setoid-Coq, a category
error and will simply fail to unify. There is no automatic translation.
