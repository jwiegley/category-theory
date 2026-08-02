```yaml
title: "Seven Sketches 5.2.1: Strict props — objects exactly ℕ, and the bijectivity the PROP class omits"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.1:def5.2]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.1 (Definition 5.2 and
the five data (i)–(v) listed after it). Printed p. 149; PDF p. 161.
Item IDs: `7sketches:5.2.1:def5.2`.

## Background

A prop is a symmetric *strict* monoidal category whose objects are literally the
natural numbers, with `0` as the monoidal unit and addition as the monoidal
product on objects; every object is then the n-fold tensor power of the
generating object `1`. See [nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[Wikipedia: PROP (category theory)](https://en.wikipedia.org/wiki/PROP_(category_theory)),
and [nLab: strict monoidal category](https://ncatlab.org/nlab/show/strict+monoidal+category)
for the strictness that makes the object monoid literally `(ℕ, +, 0)`.

## Current state in the library

`Class PROP` (`Construction/PROP.v:68`) bundles a category with a
`StrictMonoidal` and a `SymmetricMonoidal` structure, a naming function
`prop_of_nat : nat -> obj`, and two propositional strictness equalities
(`prop_unit_zero : I = ⟦0⟧`, `prop_tensor_plus : ⟦m⟧ ⨂ ⟦n⟧ = ⟦m+n⟧`). The
file's own header (`Construction/PROP.v:60-66`) states that the class
"does NOT assert the full 'objects are exactly ℕ' condition". The book's
closing remark — every object is the n-fold product of `1` — *is* proved, as
`prop_of_nat_iter` (`Construction/PROP.v:201`) with the companion
`prop_of_nat_S` (`:210`).

The precise gap is that the class admits models whose object monoid is merely
*generated* by ℕ: nothing requires `prop_of_nat` to be bijective, and no
consumer bundles the missing hypothesis. The exact condition holds only inside
the concrete instances, where `obj` is `nat` definitionally —
`Construction/PROP/Instance.v:82` (`FreePROP`, `prop_of_nat := fun n => n`,
`prop_unit_zero := eq_refl`, `prop_tensor_plus := fun m n => eq_refl`) and
`Construction/PROP/Presentation.v:312` (`PresentedPROP`, same shape) — never as
a class-level requirement. Secondarily, the two monoidal paths (strict and
symmetric) are reconciled only by the propositional field
`prop_monoidal_coherence`, a bookkeeping burden the book's definition does not
carry.

## Work to be done

Add a refinement of the class that captures Definition 5.2 exactly, without
disturbing the existing relaxed class (which downstream files consume):

- In a new `Construction/PROP/Strict.v`, define a mixin
  `Class StrictPROP (P : PROP)` carrying the missing condition — either a
  bijection witness `prop_of_nat_bijective : ∀ x : obj P, ∃! n, ⟦n⟧ = x`, or the
  stronger skeletal form `prop_obj_is_nat : obj P = nat` together with the
  agreement `prop_of_nat = id` under it. Prefer the ∃!-form: it is
  proof-irrelevant-friendly and survives universe polymorphism.
- Derive the consequences the book states informally: the object monoid of a
  `StrictPROP` is isomorphic (as a monoid) to `(ℕ, +, 0)`; `prop_of_nat` is
  injective; and the five data (i)–(v) are recovered as an explicit accessor
  pack (`phom m n := ⟦m⟧ ~> ⟦n⟧`, `pid`, `psym m n : ⟦m+n⟧ ~> ⟦n+m⟧` from
  `braid`, `pcomp`, `ptensor` from `bimap`), so a consumer can quantify over the
  book's presentation directly.
- Discharge the two existing in-tree props as `StrictPROP` instances by
  `eq_refl`/`Fin`-free reasoning: `FreePROP` (`Construction/PROP/Instance.v:82`)
  and `PresentedPROP` (`Construction/PROP/Presentation.v:312`).
- Record honestly, in the file header, that `Theory/Lawvere/PROP.v:179`
  (`Lawvere_PROP`) is *not* expected to be a `StrictPROP` without further
  hypotheses, since its object naming is inherited from the relaxed
  `LawvereTheory` shape.

In-tree donors: `Construction/PROP.v` (the class and `prop_of_nat_iter`),
`Structure/Monoidal/Strict.v:52` (`StrictMonoidal`),
`Structure/Monoidal/Symmetric.v` (`braid`), and the `eq_refl`-computing
instances named above.

## Definition of Done

- [ ] `StrictPROP` states Definition 5.2's object condition, with the five data
      (i)–(v) available as named accessors.
- [ ] The object-monoid isomorphism with `(ℕ, +, 0)` and injectivity of
      `prop_of_nat` are proved.
- [ ] `FreePROP` and `PresentedPROP` are given `StrictPROP` instances.
- [ ] Statement fidelity to the book (§5.2.1, Definition 5.2), with the setoid
      `≈` discipline on morphisms — never `=` on morphisms (object-level
      strictness equalities remain propositional `=`, as the existing class
      already does).
- [ ] No `Admitted`, `admit`, or new `Axiom`; the file stays inside the
      zero-axiom core scope of `docs/AXIOMS.md`.
- [ ] `Print Assumptions` reported closed for `StrictPROP`, the object-monoid
      isomorphism, and both instances.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index entry for `Construction/PROP/` updated to
      mention the strict refinement.

## Verification

```
coqc -R . Category Construction/PROP/Strict.v
# then, in coqtop with the file loaded:
#   Print Assumptions StrictPROP_of_FreePROP.
#   Print Assumptions StrictPROP_of_PresentedPROP.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the statement matches Seven Sketches §5.2.1, Definition 5.2 —
in particular that the object set is *exactly* ℕ, not merely indexed by it.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:5.2.1:def5.2"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.1: FinSet as a prop — the symmetric strict monoidal structure on the skeleton"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.1:example5.3, 7sketches:5.2.1:ex5.5]
deps_item_ids: [7sketches:5.2.1:def5.2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.1 (Example 5.3, the
displayed disjoint-union formula (5.4), and Exercise 5.5). Printed p. 150;
PDF p. 162. Item IDs: `7sketches:5.2.1:example5.3`, `7sketches:5.2.1:ex5.5`.

## Background

The skeleton of the category of finite sets — objects the natural numbers,
morphisms the functions between standard finite sets — is the motivating prop,
with disjoint union as the monoidal product. See
[nLab: FinSet](https://ncatlab.org/nlab/show/FinSet),
[nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[nLab: skeleton](https://ncatlab.org/nlab/show/skeleton).

## Current state in the library

The underlying category is already exactly the book's: `FinSet`
(`Instance/FinSet.v:116`) has `obj := nat` and `hom m n := Fin.t m -> Fin.t n`,
so composition (Exercise 5.5 part 3) is literal function composition and the
identity (part 4) is `fun i => i`. The coproduct is present with the right
object action: `FinSet_Cocartesian` (`Instance/FinSet.v:250`) has
`product_obj := fun m n => (m + n)%nat` with `Fin.L`/`Fin.R` as the injections,
and the generic cocartesian `cover` (`Structure/Cocartesian.v:354`, `:358`)
is precisely the two-case formula of the book's (5.4) written point-free
(Exercise 5.5 part 2). The symmetry candidate exists generically as `paws`
(`Structure/Cocartesian.v:275`, `:279`) (part 5), and `merge_computes`
(`Instance/FinSet.v:291`) checks the routing by `eq_refl` (part 1).

What is missing is the monoidal packaging itself: `FinSet` carries **no**
`Monoidal`, `BraidedMonoidal`, `SymmetricMonoidal` or `StrictMonoidal`
instance, hence no `PROP` instance. The disjoint union of morphisms exists only
as the generic cocartesian `cover`, never as `⨂`, and the symmetry only as
`paws`, never as `braid`; none of the symmetric-strict-monoidal axioms
(interchange, hexagons, `σ ∘ σ ≈ id` as a *braid*) is asserted for `FinSet`.
The file says so in terms at `Instance/FinSet.v:29-31`: the monoidal assembly
"and the [PROP] instance riding on it, need the coherence machinery and are not
yet built." The Lawvere-side bridge `Theory/Lawvere/PROP.v:179` is likewise
conditional on a `StrictMonoidal` hypothesis the `FinSet^op` base does not
supply (`Theory/Lawvere/PROP.v:65`).

## Work to be done

- In a new `Instance/FinSet/Monoidal.v`, build `FinSet_Monoidal` from
  `FinSet_Cocartesian`, then `FinSet_BraidedMonoidal` and
  `FinSet_SymmetricMonoidal` from `paws`, and `FinSet_StrictMonoidal` — the
  strictness is the point: `0 + n = n`, `(m + n) + p = m + n + p` hold by
  `Nat.add` computation on the *objects*, so the unitors and associator should
  be `eq_refl`-driven rather than the generic cocartesian isomorphisms.
- Prove the two monoidal routes agree (`prop_monoidal_coherence`) and assemble
  `FinSet_PROP : PROP` in `Instance/FinSet/PROP.v`, together with the
  `StrictPROP` refinement of §5.2.1 (objects are `nat` definitionally, so this
  is `eq_refl`-cheap).
- Discharge Exercise 5.5 as a small named pack in the same file: the five data
  exhibited *as* the prop's data — `FinSet_prop_hom`, `FinSet_prop_id`,
  `FinSet_prop_sym m n : ⟦m+n⟧ ~> ⟦n+m⟧`, `FinSet_prop_comp`,
  `FinSet_prop_tensor` — plus `Example`s computing the small instances the
  exercise asks the reader to draw (a `3 -> 2` map, a `2 -> 4` map, their
  tensor as a `5 -> 6` map, and a symmetry `σ_{m,n}`), each by `eq_refl` in the
  style of `Instance/FinSet.v:215` (`fin_split_computes`) and `:291`.
- Where the generic cocartesian operations coincide with the new tensor and
  braid, record that as a lemma (`FinSet_tensor_is_cover`,
  `FinSet_braid_is_paws`) so downstream files can move between the two
  vocabularies.

In-tree donors: `Instance/FinSet.v`, `Structure/Cocartesian.v`,
`Structure/Monoidal/Internal/Cocartesian.v`-style cocartesian-to-monoidal
assembly, `Structure/Monoidal/Strict.v:52`, and the `FinSet`
product/exponential files (`Instance/FinSet/Product.v:105`,
`Instance/FinSet/Closed.v:132`) as precedent for `eq_refl`-computing
skeletal structure.

## Definition of Done

- [ ] `FinSet` carries `Monoidal`, `Braided`, `Symmetric` and `Strict`
      instances whose object action is `Nat.add` and whose unit is `0`.
- [ ] `FinSet_PROP : PROP` exists, with the strict refinement of §5.2.1.
- [ ] The five prop data of Exercise 5.5 are named, and the small worked
      instances compute by `eq_refl`.
- [ ] The header note at `Instance/FinSet.v:29-31` is updated: it currently
      states the monoidal assembly is not built.
- [ ] Statement fidelity to the book (§5.2.1, Example 5.3 and Exercise 5.5),
      with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `FinSet_SymmetricMonoidal`,
      `FinSet_StrictMonoidal` and `FinSet_PROP`.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (FinSet is a flagship instance and
      its entry currently advertises no monoidal structure).

## Verification

```
coqc -R . Category Instance/FinSet/Monoidal.v Instance/FinSet/PROP.v
#   Print Assumptions FinSet_PROP.
#   Print Assumptions FinSet_SymmetricMonoidal.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the tensor on morphisms matches the book's displayed formula (5.4)
— `i ↦ f(i)` on the left summand and `i ↦ m' + g(i)` on the right — and the
statement matches Seven Sketches §5.2.1.

## Dependencies

Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement, for the
`StrictPROP` instance).

<!-- catalog: {"ids":["7sketches:5.2.1:example5.3","7sketches:5.2.1:ex5.5"],"deps":["7sketches:5.2.1:def5.2"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.1: Bij, the prop of finite bijections, and the free prop on the empty signature"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.1:example5.6, 7sketches:5.2.4:example5.27]
deps_item_ids: [7sketches:5.2.1:example5.3, 7sketches:5.2.1:def5.2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.1 (Example 5.6) and
§5.2.4 (Example 5.27). Printed pp. 150 and 156; PDF pp. 162 and 168.
Item IDs: `7sketches:5.2.1:example5.6`, `7sketches:5.2.4:example5.27`.

## Background

`Bij` is the prop whose morphisms `m -> n` are the bijections between standard
finite sets, so its hom-sets are empty off the diagonal and its endomorphism
monoids are the symmetric groups; it is the free prop on the empty signature,
since a labelling into the empty set forces the vertex set to be empty. See
[nLab: core groupoid](https://ncatlab.org/nlab/show/core),
[nLab: symmetric group](https://ncatlab.org/nlab/show/symmetric+group) and
[nLab: PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

`Bij` is never named or formed. The generic construction exists —
`Groupoid (C : Category) : Category` with `hom := @Isomorphism C`
(`Construction/Groupoid.v:103`) — and `Groupoid FinSet` is a well-typed term
whose objects are already `nat` and whose homs `m ~> n` are exactly the
bijections `Fin.t m <-> Fin.t n`; but no in-tree term instantiates it at
`FinSet` (its only uses are at `Fun C Sets` in
`Structure/UniversalProperty.v`). Consequently:

- there is no prop or monoidal structure on it, since `FinSet` itself carries
  no `Monoidal` instance (see the FinSet-as-a-prop work of §5.2.1);
- the inclusion `Bij ↪ FinSet` has no witness — no forgetful functor
  `Groupoid C ⟶ C` exists in tree (`Construction/Groupoid.v` is 109 lines with
  exactly one definition);
- "`Bij(m,n)` is empty for `m ≠ n`" is unproven; the nearest result is
  `finset_monic_iff_injective` (`Instance/FinSet/Classifier.v:335`), which does
  not yield `m = n` from an isomorphism.

`Construction/PROP.v:265-278` records the closely related permutation prop as
"literature canonical, not yet in the library … the permutation subcategory
`[Perm n]` itself remains unbuilt".

For Example 5.27, neither side of the identification is citable: `Empty_Sig`
exists (`Construction/PROP/Signature.v:58`, used only at `:23`, `:54` and
`Construction/PROP/Tietze.v:757`), so `FreePROP Empty_Sig` is a well-typed
term, but nothing computes or characterises it.

## Work to be done

- In a new `Instance/FinSet/Bij.v`, define `Bij := Groupoid FinSet` and prove
  the three claims the book makes about it:
  - the pigeonhole result `Bij(m,n) ≅ ∅` for `m ≠ n`, i.e. an isomorphism
    `Fin.t m <-> Fin.t n` forces `m = n` (an axiom-free counting argument on
    `Fin.t`, in the style of `Instance/FinSet/Classifier.v`);
  - the inclusion functor `Bij_Forget : Bij ⟶ FinSet`, obtained by adding the
    missing generic `Groupoid_Forget : Groupoid C ⟶ C` to
    `Construction/Groupoid.v` (`fobj := id`, `fmap := to`);
  - the prop structure: transport the symmetric strict monoidal structure of
    `FinSet` along the wide subcategory inclusion, then `Bij_PROP : PROP` and
    its strict refinement.
- In `Construction/PROP/Instance/Empty.v` (or alongside `Bij`), prove
  Example 5.27: `FreePROP Empty_Sig ≅ Bij` as props. In-tree this is a
  *syntactic* statement and therefore tractable: `Term Empty_Sig m n`
  (`Construction/PROP/Term.v:39`) has no `T_gen` inhabitants, so every term is
  built from `T_id`, `T_braid`, `T_comp`, `T_tens`; the content is that the
  quotient by `TermEq` (`Construction/PROP/Free.v:52`) is exactly the symmetric
  group `S_n` when `m = n` and empty otherwise. Prove it as a prop functor
  isomorphism in both directions, with the `Perm n` normal form the
  `Construction/PROP.v:265-278` note anticipates.

In-tree donors: `Construction/Groupoid.v:103`, `Instance/FinSet.v:116`,
`Instance/FinSet/Classifier.v` (Fin-level counting),
`Construction/PROP/Term.v`, `Construction/PROP/TermEq.v` (the braid
coherence constructors), `Construction/PROP/Signature.v:58`.

## Definition of Done

- [ ] `Bij` is defined, with `Bij(m,n)` proved empty for `m ≠ n`.
- [ ] `Groupoid_Forget` added generically, and `Bij_Forget : Bij ⟶ FinSet`
      derived from it.
- [ ] `Bij_PROP : PROP` with the strict refinement of §5.2.1.
- [ ] `FreePROP Empty_Sig ≅ Bij` proved, in both directions, as an isomorphism
      of props.
- [ ] The `Construction/PROP.v:265-278` note is updated once `Perm n` exists.
- [ ] Statement fidelity to the book (§5.2.1 Example 5.6, §5.2.4 Example 5.27),
      with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom` — in particular the pigeonhole
      argument must be axiom-free (no `funext`, no `UIP` beyond the in-tree
      Hedberg idiom).
- [ ] `Print Assumptions` reported closed for `Bij_PROP` and the Example 5.27
      isomorphism.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (the free-prop-on-no-generators
      identification is flagship-level for the PROP development).

## Verification

```
coqc -R . Category Instance/FinSet/Bij.v
#   Print Assumptions Bij_PROP.
#   Print Assumptions FreePROP_Empty_iso_Bij.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the statements match Seven Sketches §5.2.1 Example 5.6 (hom-sets
empty off the diagonal; `Bij` a subcategory of `FinSet` sharing its monoidal
product) and §5.2.4 Example 5.27.

## Dependencies

Depends on: 7sketches:5.2.1:example5.3 (FinSet as a prop — the ambient
symmetric strict monoidal structure being transported).
Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement).

<!-- catalog: {"ids":["7sketches:5.2.1:example5.6","7sketches:5.2.4:example5.27"],"deps":["7sketches:5.2.1:example5.3","7sketches:5.2.1:def5.2"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.1: Corel as a prop — corelations over the skeletal finite sets"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.1:example5.7]
deps_item_ids: [7sketches:5.2.1:def5.2, 7sketches:5.2.1:example5.3]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.1 (Example 5.7).
Printed p. 150; PDF p. 162. Item ID: `7sketches:5.2.1:example5.7`.

## Background

A corelation `m -> n` is a partition of the disjoint union of the two finite
sets; corelations compose by joining partitions across the shared boundary, and
the resulting compact closed category is a prop. See
[nLab: co-relation](https://ncatlab.org/nlab/show/corelation) and
[nLab: PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

The abstract construction exists: `CorelCat` (`Construction/Cospan/Corelation.v:259`)
over an arbitrary base, with `CorelationArrow` (`:56`) as a jointly-epic
cospan, `corelation_id` (`:112`), `corelation_compose` (`:168`) and the
embedding `Corel_to_Cospan` (`:295`). Three things are missing.

1. `CorelCat` is never instantiated at the skeletal `FinSet`, even though the
   inputs exist — `FinSet_Cocartesian` (`Instance/FinSet.v:250`) and
   `FinSet_HasPushouts` (`Instance/FinSet/Pushout.v:513`), modulo the
   `CorelComposable` hypothesis — so corelations are never realised on objects
   ℕ.
2. `CorelCat` carries **no** monoidal structure. `Cospan_Monoidal`
   (`Construction/Cospan/Hypergraph.v:1973`) and `Cospan_SymmetricMonoidal`
   (`Construction/Cospan/Symmetric.v:398`) are built on `CospanCat` only; their
   restriction along `Corel_to_Cospan` is not proved, so there is no `⨂`, no
   `σ`, and no `PROP` instance.
3. The book's concrete description of `Corel(m,n)` as the set of partitions of
   the disjoint union is nowhere: a search for "partition" finds only
   list-partitioning in `Theory/Coq/List.v`.

## Work to be done

- In a new `Construction/Cospan/Corelation/Monoidal.v`, show that the
  symmetric monoidal structure of `CospanCat` restricts to `CorelCat`: the
  tensor of two jointly-epic cospans is jointly epic, so the wide-subcategory
  structure is inherited. State it as an explicit transport along
  `Corel_to_Cospan`, so the embedding becomes a strict monoidal functor.
- In `Instance/FinSet/Corel.v`, instantiate at the skeleton:
  `FinCorel := CorelCat FinSet _ _`, discharging `CorelComposable` from
  `FinSet_HasPushouts`; then assemble `FinCorel_PROP : PROP` together with the
  strict refinement of §5.2.1 (objects are `nat` definitionally).
- Prove the concrete reading the book gives: `FinCorel(m, n)` is in bijection
  with the partitions of `Fin.t (m + n)`, i.e. with the quotients of the
  disjoint union — this is the jointly-epic cospan seen as a surjection onto
  its apex, and it makes the prop computable in the style of the other
  `Instance/FinSet/*` files.

In-tree donors: `Construction/Cospan/Corelation.v`,
`Construction/Cospan/Symmetric.v:398`, `Construction/Cospan/Hypergraph.v:1973`,
`Instance/FinSet/Pushout.v:513`, `Instance/FinSet.v:250`.

## Definition of Done

- [ ] `CorelCat` inherits the symmetric (strict, on a skeletal base) monoidal
      structure from `CospanCat`, proved rather than assumed.
- [ ] `FinCorel := CorelCat FinSet …` exists, with `FinCorel_PROP : PROP` and
      the strict refinement of §5.2.1.
- [ ] `FinCorel(m,n)` is identified with the partitions of the disjoint union,
      as the book describes.
- [ ] Statement fidelity to the book (§5.2.1, Example 5.7), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `FinCorel_PROP` and the
      partition characterisation.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (this is the first concrete base for
      the corelation development, which the index currently describes only
      abstractly).

## Verification

```
coqc -R . Category Construction/Cospan/Corelation/Monoidal.v Instance/FinSet/Corel.v
#   Print Assumptions FinCorel_PROP.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the statement matches Seven Sketches §5.2.1 Example 5.7 — a
corelation `m -> n` is a partition of the disjoint union, and the claim being
formalized is that these data satisfy Definition 5.2.

## Dependencies

Depends on: #824 (Corel as a compact closed category — the corelation
development this instantiates).
Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement).
Depends on: 7sketches:5.2.1:example5.3 (FinSet as a prop — the skeletal base
and its coproduct/pushout structure).

<!-- catalog: {"ids":["7sketches:5.2.1:example5.7"],"deps":["#824","7sketches:5.2.1:def5.2","7sketches:5.2.1:example5.3"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.1: FinRel — relations between finite sets as a prop, with the disjoint-union tensor"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.1:example5.8, 7sketches:5.2.1:ex5.10]
deps_item_ids: [7sketches:5.2.1:def5.2, 7sketches:5.2.1:example5.3]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.1 (Example 5.8 with
its footnote on the monoidal product, and Exercise 5.10). Printed pp. 150–151;
PDF pp. 162–163. Item IDs: `7sketches:5.2.1:example5.8`,
`7sketches:5.2.1:ex5.10`.

## Background

Relations between finite sets, composed by the usual existential-witness rule,
form a prop whose monoidal product is disjoint union of relations. See
[nLab: Rel](https://ncatlab.org/nlab/show/Rel) and
[nLab: PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

`Rel` (`Instance/Rel.v:45`) matches the book on the composition clause exactly:
`obj := @obj Coq`, `hom A B := A ~> Ensemble B`, hom-equivalence pointwise
`<->`, `id := Singleton`, and composition by the existential witness. Two gaps.

1. **Not skeletal.** `Rel`'s objects are arbitrary Coq types, so "morphisms
   `m -> n` are relations contained in `{1..m} × {1..n}`" is not the in-tree
   statement, and no finite/skeletal variant exists (a search for `FinRel`
   returns nothing).
2. **No monoidal structure whatsoever.** The `Rel_Cartesian` (`:97`),
   `Rel_Cocartesian` (`:127`) and `Rel_Closed` (`:146`) instances are all
   inside a comment block that opens at `Instance/Rel.v:96` and closes at
   `:157`; the live content is `Rel_Initial` (`:90`), `some_number` (`:161`)
   and `Relation_Functor` (`:167`). So the disjoint-union tensor of the book's
   footnote is absent, as are the symmetries, and no `PROP` instance exists.

Exercise 5.10 asks the reader to supply the five prop data for one of `Bij`,
`Corel` or `Rel`. For all three permitted choices, the two genuinely
prop-specific data — the symmetry (iii) and the monoidal product on morphisms
(v) — are missing; only the category-level data (i), (ii), (iv) exist, and
none of the three is skeletal on ℕ.

## Work to be done

- In a new `Instance/FinRel.v`, define the skeletal prop of finite relations
  directly: `obj := nat`, `hom m n := Fin.t m -> Fin.t n -> Type` (or the
  `Ensemble`-style presentation already used by `Instance/Rel.v`, kept
  proof-irrelevant by a hom-setoid of pointwise `iffT`), with the book's
  composition and the diagonal identity.
- Build the monoidal layer that `Instance/Rel.v` lacks: the disjoint-union
  tensor on morphisms (the footnote's formula, `R₁ + R₂ ⊆ (m₁ ⊎ m₂) × (n₁ ⊎ n₂)`
  supported only on the two diagonal blocks), the braid, the strictness
  equalities on objects, and `FinRel_PROP : PROP` with the strict refinement of
  §5.2.1.
- Discharge Exercise 5.10 in the same file as a named pack exhibiting the five
  data (i)–(v) for `FinRel`, with `Example`s computing the book's picture (the
  tensor of a `2 -> 2` relation with a `3 -> 1` relation as a `5 -> 3`
  relation) by decision on `Fin.t`.
- Relate the skeletal prop back to the ambient `Rel` by a full and faithful
  functor `FinRel ⟶ Rel` factoring through `Fin.t`, so the two developments do
  not drift apart.
- While in `Instance/Rel.v`: decide the fate of the dead `Rel_Cartesian` /
  `Rel_Cocartesian` / `Rel_Closed` block (`:96-157`). Either revive it (it is
  the natural donor for the tensor) or record in the header why it stays
  commented out; do not leave the file in its current ambiguous state.

In-tree donors: `Instance/Rel.v`, `Instance/FinSet.v` (skeletal idioms,
`fin_split`/`merge`), `Structure/Monoidal/Strict.v:52`,
`Instance/FinSet/Classifier.v` (decidability on `Fin.t`).

## Definition of Done

- [ ] `FinRel` exists as a skeletal category on `nat` with the book's
      composition and identity.
- [ ] The disjoint-union tensor and the braid are defined and proved to satisfy
      the symmetric strict monoidal axioms.
- [ ] `FinRel_PROP : PROP` with the strict refinement of §5.2.1.
- [ ] Exercise 5.10's five data are exhibited for `FinRel`, with worked
      computing examples.
- [ ] A full and faithful `FinRel ⟶ Rel` is provided.
- [ ] LIBRARY DEFECT (found during the coverage pass, to be fixed while this
      file is being touched): the header comment at `Instance/Rel.v:33`
      describes the library's composition order as "diagrammatic", but the
      order it then fixes (`compose f g` applies `g` first) is the classical
      one; correct the comment.
- [ ] Statement fidelity to the book (§5.2.1, Example 5.8 with its footnote,
      and Exercise 5.10), with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `FinRel_PROP` and the embedding
      into `Rel`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (`Instance/Rel.v`'s entry currently
      advertises a bare category).

## Verification

```
coqc -R . Category Instance/FinRel.v
#   Print Assumptions FinRel_PROP.
#   Print Assumptions FinRel_to_Rel.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: composition matches the book's existential-witness formula and the
tensor matches the footnote of Example 5.8; the statement matches Seven
Sketches §5.2.1.

## Dependencies

Depends on: #262 (Rel, converse relations, and the graph embedding — the
ambient relational development).
Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement).
Depends on: 7sketches:5.2.1:example5.3 (FinSet as a prop — the skeletal
idioms and the `Fin.t` splitting used by the tensor).

<!-- catalog: {"ids":["7sketches:5.2.1:example5.8","7sketches:5.2.1:ex5.10"],"deps":["#262","7sketches:5.2.1:def5.2","7sketches:5.2.1:example5.3"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.1: Posetal props — thin props as symmetric monoidal preorders on (ℕ, +)"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:5.2.1:ex5.9]
deps_item_ids: [7sketches:5.2.1:def5.2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.1 (Exercise 5.9).
Printed p. 151; PDF p. 163. Item ID: `7sketches:5.2.1:ex5.9`.

## Background

A posetal prop is a prop that is also a poset: equivalently, a symmetric
monoidal preorder carried by `(ℕ, ≤)` whose monoidal product on objects is
addition. See [nLab: thin category](https://ncatlab.org/nlab/show/thin+category)
and [nLab: preorder](https://ncatlab.org/nlab/show/preorder).

## Current state in the library

Nothing in-tree connects a prop to an order. A search for "posetal prop",
"monoidal preorder" and "ordered monoid" returns no definitions (only prose at
`Construction/Enriched.v:78`). The near-misses are genuinely near-misses:
`LessThanEqualTo_Category` (`Instance/Poset.v:120`) *is* `(ℕ, ≤)` as a thin
category, and `Omega` (`Instance/Omega.v:72`) is `(ℕ, le_t)`, but neither
carries a tensor and nothing in the library relates either order to addition;
`Two_Monoidal` (`Instance/Two/Monoidal.v:105`) is a monoidal thin category but
on the two-element order, with meet as tensor.

## Work to be done

- In a new `Construction/PROP/Posetal.v`, define `PosetalPROP` as a prop whose
  underlying category is thin (any two parallel morphisms are `≈`), and prove
  the exercise's identification: a posetal prop is exactly a preorder relation
  `≤` on ℕ that is reflexive, transitive, and monotone for addition in both
  arguments (so that `+` is a monotone bifunctor and the symmetry is forced by
  thinness together with commutativity of `+` on objects).
- Give the three witnesses the exercise asks for, as instances:
  - the discrete order (`m ≤ n` iff `m = n`) — the "no non-identity morphisms"
    prop, which is also the skeleton of `Bij`'s object level;
  - the usual order `(ℕ, ≤)`, donated by `Instance/Omega.v:72` / 
    `Instance/Poset.v:120`, with `+` monotone;
  - the divisibility order on ℕ is *not* one (addition is not monotone for it —
    a deliberate non-example worth recording), so use instead the codiscrete
    order (`m ≤ n` always), or the order `m ≤ n` iff `m = 0 ∨ m = n`.
- Relate to the enriched spine: a posetal prop is a symmetric monoidal preorder
  in the sense of the Chapter 2 development, restricted to the carrier ℕ with
  `+`; state that bridge rather than duplicating the axioms.

In-tree donors: `Construction/PROP.v:68`, `Instance/Omega.v:72`,
`Instance/Poset.v:120`, `Instance/Two/Monoidal.v:105` (a worked thin monoidal
category), `Instance/Proset.v:33`.

## Definition of Done

- [ ] `PosetalPROP` defined, with the thinness condition stated in the setoid
      idiom (parallel morphisms are `≈`, not `=`).
- [ ] The characterisation "posetal prop = symmetric monoidal preorder on
      `(ℕ, +, 0)`" proved in both directions.
- [ ] Three instances exhibited, plus the divisibility non-example recorded
      with its counterexample.
- [ ] Statement fidelity to the book (§5.2.1, Exercise 5.9), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the characterisation and each
      instance.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated if the Chapter 2 bridge lands here.

## Verification

```
coqc -R . Category Construction/PROP/Posetal.v
#   Print Assumptions posetal_prop_iff_monoidal_preorder.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the statement matches Seven Sketches §5.2.1 Exercise 5.9, and the
three examples really are posetal props (each monotonicity check written out).

## Dependencies

Depends on: #771 (symmetric monoidal preorders — the class this identifies
posetal props with).
Depends on: #775 (monoidal structures on the arithmetic preorders — ℕ with `+`
as a monoidal preorder, the second witness).
Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement).

<!-- catalog: {"ids":["7sketches:5.2.1:ex5.9"],"deps":["#771","#775","7sketches:5.2.1:def5.2"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.1: Prop functors and the category of props"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.1:def5.11]
deps_item_ids: [7sketches:5.2.1:def5.2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.1 (Definition 5.11).
Printed p. 151; PDF p. 163. Item ID: `7sketches:5.2.1:def5.11`.

## Background

A morphism of props is a functor that is the identity on objects and preserves
the monoidal product of morphisms; props and prop functors form a category. See
[nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[nLab: monoidal functor](https://ncatlab.org/nlab/show/monoidal+functor).

## Current state in the library

There is no class of prop morphisms: the definition's two clauses are never
bundled, and searches for "prop functor", `PROPFunctor`, `prop_functor` and
"morphism of PROPs" return nothing beyond prose at
`Functor/Structure/Monoidal/Strict.v:44`.

Clause (a) — identity on objects — is carried only ad hoc, as a definitional
choice inside particular constructions (`RelabelFunctor`'s
`fobj := fun n : nat => n`, `Construction/PROP/Tietze.v:164`) or as an explicit
hypothesis family `Hobj : ∀ n, G n = ⟦n⟧` in
`Construction/PROP/Universal.v` (used by `interp_unique`, `:603`). Nothing
quantifies over "the prop functors `C -> D`", so there is no category of props
and no identity/composition of prop functors as such; only the generic
`Id_StrictMonoidalFunctor` / `Compose_StrictMonoidalFunctor`
(`Functor/Structure/Monoidal/Strict.v:150`, `:163`) exist.

The notion actually used in tree is *incomparable* with the book's:
`StrictMonoidalFunctor` (`Functor/Structure/Monoidal/Strict.v:54`) additionally
demands unit preservation and full monoidal-functor coherence, and the
library's PROP-morphism bundle also demands the braid square
(`Construction/PROP/Universal.v:445`), none of which Definition 5.11 asks for —
while conversely nothing in `StrictMonoidalFunctor` implies clause (a).
`RelabelFunctor_Strict` / `RelabelFunctor_Symmetric`
(`Construction/PROP/Tietze.v:265`, `:288`) is a genuine in-tree witness of a
prop functor between two free props, but only as an instance.

## Work to be done

- In a new `Construction/PROP/Functor.v`, define
  `Class PROPFunctor (C D : PROP)` carrying an underlying functor plus exactly
  the book's two clauses: `pf_obj : ∀ n, fobj ⟦n⟧ = ⟦n⟧` and
  `pf_tensor : ∀ f g, fmap (f ⨂ g) ≈ hom_cast … (fmap f ⨂ fmap g)` (the casts
  being forced by the propositional strictness equalities of `Class PROP`).
- Prove the relationships with the existing vocabulary, both directions where
  they hold: a `PROPFunctor` between strict props induces a
  `StrictMonoidalFunctor` when it also preserves the unit (and note in the
  header that the book does not require this); conversely a
  `StrictMonoidalFunctor` satisfying `pf_obj` is a `PROPFunctor`.
- Build identity and composition of prop functors and assemble the category
  `PROPCat` of props and prop functors, so downstream statements
  ("`Free(G) -> C` prop functors correspond to …") can quantify over a hom-set
  rather than over an ad hoc hypothesis family.
- Re-express the existing witnesses as instances: `RelabelFunctor`
  (`Construction/PROP/Tietze.v:164`), `PresentedProj`
  (`Construction/PROP/Presentation.v:188`) and `InterpF`
  (`Construction/PROP/Universal.v:174`) under its `Hobj` hypothesis.

In-tree donors: `Functor/Structure/Monoidal/Strict.v`,
`Construction/PROP.v:68`, `Construction/PROP/Universal.v` (the `Hobj`
discipline and `hom_cast`), `Construction/PROP/Tietze.v:265`.

## Definition of Done

- [ ] `PROPFunctor` states exactly Definition 5.11's two clauses, no more.
- [ ] The comparison lemmas with `StrictMonoidalFunctor` are proved, and the
      strictly-stronger/incomparable directions are disclosed in the header.
- [ ] Identity and composition of prop functors, and the category `PROPCat`.
- [ ] `RelabelFunctor`, `PresentedProj` and `InterpF` recorded as instances.
- [ ] Statement fidelity to the book (§5.2.1, Definition 5.11), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `PROPCat` and each instance.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (the PROP entry currently lists no
      morphism notion).

## Verification

```
coqc -R . Category Construction/PROP/Functor.v
#   Print Assumptions PROPCat.
#   Print Assumptions PROPFunctor_of_RelabelFunctor.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the class asks for identity-on-objects and preservation of the
monoidal product on morphisms, and nothing else — matching Seven Sketches
§5.2.1 Definition 5.11.

## Dependencies

Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement — `pf_obj` is
stated against the object naming that refinement pins down).

<!-- catalog: {"ids":["7sketches:5.2.1:def5.11"],"deps":["7sketches:5.2.1:def5.2"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.1: Two prop functors — the inclusion of bijections and the graph functor into relations"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.1:example5.12]
deps_item_ids: [7sketches:5.2.1:def5.11, 7sketches:5.2.1:example5.3, 7sketches:5.2.1:example5.6, 7sketches:5.2.1:example5.8]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.1 (Example 5.12).
Printed p. 151; PDF p. 163. Item ID: `7sketches:5.2.1:example5.12`.

## Background

The two basic prop functors are the inclusion of the bijections into the finite
sets, and the functor sending a function to its graph, a relation. See
[nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[nLab: Rel](https://ncatlab.org/nlab/show/Rel).

## Current state in the library

Clause 1 (the inclusion of bijections into finite sets) is entirely absent: the
groupoid of bijections is never formed at the skeletal finite sets, and no
forgetful functor out of `Construction/Groupoid.v`'s `Groupoid` exists (the
file is 109 lines with exactly one definition), so there is nothing to be the
inclusion.

Clause 2 exists only in a weakened form. `Relation_Functor`
(`Instance/Rel.v:167`) is the graph functor, identity on objects with
`fmap f = fun x y => In (Singleton (f x)) y`, and the surrounding comment
(`:163-165`) calls it identity-on-objects and faithful — but it runs
`Coq ⟶ Rel` over *all* Coq types, not from a skeletal finite-set prop, and it
carries no monoidal-functor structure at all. That is unavoidable today, since
neither source nor target is a prop in tree (`Rel`'s monoidal instances are
inside the comment block `Instance/Rel.v:96-157`). So neither of the example's
two claims — that these are prop functors — is stated.

## Work to be done

- Once the prop instances of §5.2.1 exist, define in
  `Instance/FinSet/PropFunctors.v`:
  - `Bij_inclusion : PROPFunctor Bij_PROP FinSet_PROP`, built from the generic
    `Groupoid_Forget`, with clause (a) by `eq_refl` and clause (b) from the
    fact that the tensor on `Bij` is the restriction of `FinSet`'s;
  - `FinSet_graph : PROPFunctor FinSet_PROP FinRel_PROP`, sending `f` to
    `{(i, j) : f i = j}`, with clause (b) the check that the graph of a
    disjoint union is the disjoint union of the graphs.
- Prove the properties the example implicitly relies on: `Bij_inclusion` is
  faithful and wide; `FinSet_graph` is faithful (and *not* full — worth a
  recorded counterexample, since it is the reason `FinRel` is strictly larger).
- Relate `FinSet_graph` to the existing `Relation_Functor`
  (`Instance/Rel.v:167`) by a commuting square along the skeletal embeddings,
  so the general and the skeletal graph functors are known to agree.

In-tree donors: `Construction/Groupoid.v:103`, `Instance/Rel.v:167`,
`Instance/FinSet.v:116`, and the `PROPFunctor` class of §5.2.1.

## Definition of Done

- [ ] `Bij_inclusion` and `FinSet_graph` exist as `PROPFunctor` instances.
- [ ] Faithfulness of both, and a counterexample to fullness of the graph
      functor.
- [ ] The commuting square relating `FinSet_graph` to `Relation_Functor`.
- [ ] Statement fidelity to the book (§5.2.1, Example 5.12), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for both prop functors.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated only if the PROP entry gains a
      worked-morphisms subsection.

## Verification

```
coqc -R . Category Instance/FinSet/PropFunctors.v
#   Print Assumptions Bij_inclusion.
#   Print Assumptions FinSet_graph.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the statement matches Seven Sketches §5.2.1 Example 5.12 — in
particular that the second functor sends a function to its graph relation.

## Dependencies

Depends on: 7sketches:5.2.1:def5.11 (prop functors).
Depends on: 7sketches:5.2.1:example5.3 (FinSet as a prop).
Depends on: 7sketches:5.2.1:example5.6 (Bij as a prop).
Depends on: 7sketches:5.2.1:example5.8 (FinRel as a prop).

<!-- catalog: {"ids":["7sketches:5.2.1:example5.12"],"deps":["7sketches:5.2.1:def5.11","7sketches:5.2.1:example5.3","7sketches:5.2.1:example5.6","7sketches:5.2.1:example5.8"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.2: Port graphs — the acyclic (m,n)-port-graph datatype"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.2:def5.13, 7sketches:5.2.2:example5.14]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.2 (Definition 5.13
and Example 5.14 with the displayed diagram (5.15)). Printed pp. 151–152;
PDF pp. 163–164. Item IDs: `7sketches:5.2.2:def5.13`,
`7sketches:5.2.2:example5.14`.

## Background

An `(m,n)`-port graph is a finite set of vertices, each with an in-degree and
an out-degree, together with a *bijection* wiring the `m` outer inputs and all
vertex outputs to all vertex inputs and the `n` outer outputs, subject to
acyclicity of the induced internal flow graph. These are the combinatorial
carriers of string diagrams for props. See
[nLab: string diagram](https://ncatlab.org/nlab/show/string+diagram) and
[Wikipedia: directed acyclic graph](https://en.wikipedia.org/wiki/Directed_acyclic_graph).

## Current state in the library

Nothing of the kind exists. Searches for "port graph"/"portgraph"/"open graph"
return no hits; `\bacyclic` occurs exactly twice, both in prose
(`Comonad/Coalgebra.v:102`, `Instance/Coq.v:90`); "in-degree"/"out-degree" and
"DAG" return nothing. The only combinatorial graph datatype in the tree is
`Class Quiver` (`Construction/Free/Quiver.v:54`), which carries nodes and
endpoint-indexed edge sets — a directed multigraph with no degrees, no port
structure, no boundary and no acyclicity condition. The wiring-diagram language
appears throughout the PROP and cospan headers, but only as prose (for example
`Theory/DoubleCategory.v:155`); no file carries a graph-valued datatype for it,
and there is no worked `2 -> 3` witness anywhere.

## Work to be done

- In a new `Construction/PROP/PortGraph.v`, define the datatype following the
  book: a record `PortGraph (m n : nat)` with a vertex type `V` (finite —
  either `Fin.t k` for a carried `k`, or an abstract type with a decidable
  finiteness witness; pick the `Fin.t` route to keep everything computable and
  axiom-free, as `Instance/FinSet.v` does), degree functions `vin, vout : V -> nat`,
  and the structure bijection `ι` between `Fin.t m ⊎ O` and `I ⊎ Fin.t n`,
  where `I` and `O` are the sigma-types of vertex inputs and vertex outputs.
- Define the induced internal flow relation (an arrow `u -> v` whenever
  `ι` sends an output port of `u` to an input port of `v`) and the acyclicity
  predicate as "the only path from a vertex to itself is trivial", using the
  reflexive-transitive closure idiom already in the tree
  (`Instance/Lambda/Multi.v:46`) or `Lib/TList.v` paths.
- Prove the basic structural facts a prop construction will need: `ι` being a
  bijection is equivalent to a pair of mutually inverse functions (so the
  datatype stays computable); acyclicity is decidable for a finite vertex type;
  and two port graphs are isomorphic exactly when there is a degree-preserving
  bijection of vertices commuting with `ι` (define `PortGraphIso` now — the
  prop of port graphs will have it as its hom-setoid equivalence).
- Discharge Example 5.14 as an executable witness in the same file: the
  `(2,3)`-port graph on three vertices with the book's degrees, its explicit
  `ι`, and `Example`s checking by `eq_refl`/decision that `ι` is a bijection
  and that the internal flow graph is acyclic.

In-tree donors: `Instance/FinSet.v` (`fin_split`, `merge`, and the
decide-by-computation style), `Construction/Free/Quiver.v` (path idioms),
`Lib/TList.v`, `Instance/FinSet/Classifier.v` (decidability on `Fin.t`).

## Definition of Done

- [ ] `PortGraph m n` defined with vertices, degrees, the structure bijection
      and the acyclicity condition, exactly as Definition 5.13 states.
- [ ] `PortGraphIso` defined as the notion of sameness (a setoid on
      `PortGraph m n`), with the groupoid laws proved.
- [ ] Acyclicity decidable for the finite carrier, proved without axioms.
- [ ] Example 5.14 present as a computing witness (the `(2,3)`-port graph, its
      bijection, and its acyclic flow graph).
- [ ] Statement fidelity to the book (§5.2.2, Definition 5.13 and Example
      5.14); morphism-level equations use `≈`, never `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom` — in particular no `funext` for
      the bijection condition (state it as a pair of pointwise inverse laws).
- [ ] `Print Assumptions` reported closed for `PortGraph`, the decidability
      result and the Example 5.14 witness.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (this introduces the library's first
      combinatorial diagram datatype).

## Verification

```
coqc -R . Category Construction/PROP/PortGraph.v
#   Print Assumptions PortGraph.
#   Print Assumptions portgraph_acyclic_dec.
#   Print Assumptions example_5_14.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the structure bijection has the book's exact domain and codomain
(outer inputs plus vertex outputs, to vertex inputs plus outer outputs), and
the acyclicity condition is the one Seven Sketches §5.2.2 states.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:5.2.2:def5.13","7sketches:5.2.2:example5.14"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.2: PG, the prop of port graphs"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.2:construction-pg, 7sketches:5.2.2:ex5.16, 7sketches:5.2.2:ex5.18]
deps_item_ids: [7sketches:5.2.2:def5.13, 7sketches:5.2.1:def5.2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.2 (the unnumbered
construction of the category PG developed across two run-in paragraphs, with
the displayed composition law (5.17), and Exercises 5.16 and 5.18). Printed
pp. 152–153; PDF pp. 164–165. Item IDs:
`7sketches:5.2.2:construction-pg`, `7sketches:5.2.2:ex5.16`,
`7sketches:5.2.2:ex5.18`.

## Background

Port graphs compose by splicing: the vertex sets are joined and the two
structure bijections are chained through the shared boundary, yielding a prop
whose objects are the natural numbers. See
[nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[nLab: string diagram](https://ncatlab.org/nlab/show/string+diagram).

## Current state in the library

Nothing: with no port-graph datatype there is no PG. An enumeration of the
whole PROP layer — `Construction/PROP.v`, `Construction/PROP/Free.v` (whose
header states the hom is `Term S m n` quotiented by `TermEq`, "the standard
free = syntactic construction"), `Construction/PROP/Instance.v`,
`Construction/ColouredPROP/*`, `Instance/ZX.v`, `Instance/FinSet.v` — finds no
graph-valued hom anywhere. The nearest gluing machinery is cospan composition
by pushout (`Construction/Cospan/Category.v`,
`Construction/DecoratedCospan/Category.v`), which is a pushout in an arbitrary
category, never a port-graph splice. `Construction/Free/Quiver.v` carries no
monoidal or coproduct structure (`rg -n 'Monoidal|Coproduct'` over that file
returns nothing), so no graph category in the tree is even a candidate.

## Work to be done

- In a new `Construction/PROP/PortGraph/Category.v`, build `PG`: objects `nat`,
  `hom m n := PortGraph m n` with the isomorphism setoid of §5.2.2 as
  hom-equivalence, composition by the book's three-case splice (route through
  the first bijection; if it lands on the shared boundary, continue through the
  second; ports of the second graph are handled by the second bijection alone),
  and the identity on `n` the vertex-free port graph whose bijection is the
  identity.
- Discharge the proof obligations the book leaves implicit: the composite
  bijection really is a bijection; the composite is acyclic when both factors
  are; composition respects the isomorphism setoid (a `Proper` instance);
  associativity and both unit laws up to `PortGraphIso`.
- Add the monoidal layer — the tensor is disjoint union of vertex sets with the
  two bijections placed side by side — and the braid, then `PG_PROP : PROP`
  with the strict refinement of §5.2.1.
- Exercise 5.16 asks how composition looks in the nested-box picture; formalize
  its mathematical content as the *interchange/locality* lemma: the vertices
  and the internal wiring of each factor are preserved by the splice, and only
  boundary ports are rerouted. State it as a pair of lemmas
  (`pg_compose_vertices : V (g ∘ f) ≅ V f ⊎ V g` and a description of the
  restricted flow relation), and add a non-trivial worked composite as an
  `Example`.
- Exercise 5.18 is a worked tensor: the monoidal product of the Example 5.14
  `(2,3)`-port graph with itself, checked to be a `(4,6)`-port graph, as a
  computing `Example`.

In-tree donors: the port-graph datatype of §5.2.2,
`Instance/FinSet.v` (`fin_split`/`merge` for the boundary case analysis),
`Construction/PROP.v:68`, `Structure/Monoidal/Strict.v:52`.

## Definition of Done

- [ ] `PG : Category` with the book's composition and identity, all laws proved
      up to the port-graph isomorphism setoid.
- [ ] Composition proved to preserve bijectivity and acyclicity, with a
      `Proper` instance for the hom-setoid.
- [ ] `PG_PROP : PROP` with the tensor, the braid and the strict refinement of
      §5.2.1.
- [ ] The locality lemma of Exercise 5.16 plus a non-trivial worked composite.
- [ ] The Exercise 5.18 tensor witness computes.
- [ ] Statement fidelity to the book (§5.2.2, the PG construction with its
      displayed composition law, and Exercises 5.16, 5.18), with the setoid `≈`
      discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `PG` and `PG_PROP`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (a graph-valued prop is flagship-level
      for the PROP development).

## Verification

```
coqc -R . Category Construction/PROP/PortGraph/Category.v
#   Print Assumptions PG.
#   Print Assumptions PG_PROP.
#   Print Assumptions exercise_5_18.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: composition matches the book's displayed three-case law, and the
identity is the vertex-free port graph; the statement matches Seven Sketches
§5.2.2.

## Dependencies

Depends on: 7sketches:5.2.2:def5.13 (the port-graph datatype).
Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement).

<!-- catalog: {"ids":["7sketches:5.2.2:construction-pg","7sketches:5.2.2:ex5.16","7sketches:5.2.2:ex5.18"],"deps":["7sketches:5.2.2:def5.13","7sketches:5.2.1:def5.2"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.4: G-labeled port graphs and the port-graph model of the free prop"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.2.4:def5.25, 7sketches:5.2.4:ex5.28]
deps_item_ids: [7sketches:5.2.2:def5.13, 7sketches:5.2.2:construction-pg]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.4 (Definition 5.25,
clauses (a) prop signature, (b) G-labeling, (c) the free prop `Free(G)`; and
Exercise 5.28). Printed pp. 155–156; PDF pp. 167–168. Item IDs:
`7sketches:5.2.4:def5.25`, `7sketches:5.2.4:ex5.28`.

## Background

The free prop on a signature is presented by the book *semantically*, as the
prop whose morphisms are port graphs with vertices labelled by generators of
matching arity — the diagrammatic counterpart of the syntactic "terms modulo
the axioms" presentation. See
[nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[nLab: string diagram](https://ncatlab.org/nlab/show/string+diagram).

## Current state in the library

Clause (a) is faithful and already present: `Signature := nat -> nat -> Type`
(`Construction/PROP/Signature.v:50`) is the fibred form of the book's
`(G, s, t)` — `S m n` is the type of generators of in-arity `m` and out-arity
`n` — so the arity functions are the indexing and no side condition is needed.

Clause (c)'s *object* also exists, but only in the syntactic model:
`FreeCat S` (`Construction/PROP/Free.v:81`) has `hom := @Term S` with
`homset := @Term_Setoid` (`:52`), i.e. terms (`Construction/PROP/Term.v:39`)
modulo the strict-symmetric-monoidal congruence `TermEq`, and `FreePROP S`
(`Construction/PROP/Instance.v:82`) packages it as a prop, with the universal
property in `Construction/PROP/Universal.v`.

Clause (b) is entirely absent, and with it the identification the book actually
makes: there is no port-graph (or any combinatorial open-graph) datatype in the
tree, hence no vertices, degrees, structure bijection or labelling function
whose arities match the degrees, and **no theorem identifying the syntactic
free prop with the prop of G-labelled port graphs**. Searches for "port graph",
"open graph", "vertex/vertices/incident" and "labelling" return only unrelated
hits (cone vertices in `Theory/Equivalence/Limit.v`; signature *re*-labelling in
`Construction/PROP/Tietze.v` and `Relabel.v`).

Exercise 5.28 — that the free prop on one generator per arity is PG — cannot
even be stated: the source side is expressible (`Single_Sig`/`Sum_Sig`,
`Construction/PROP/Signature.v:68`, `:79`), the target side does not exist.

## Work to be done

- In a new `Construction/PROP/PortGraph/Labeled.v`, define `G`-labelings:
  a function from vertices to generators such that `l v : S (vin v) (vout v)`
  (in the library's fibred encoding the arity side condition of the book
  becomes typing, exactly as it does for `Signature`). Define
  `LPortGraph S m n` and its isomorphism setoid (label-preserving port-graph
  isomorphism), and build the prop `FreeDiagram S : PROP` with PG's composition
  and tensor, labels carried along.
- Prove the identification that Definition 5.25 clause (c) asserts and the
  library currently lacks: a prop isomorphism
  `FreePROP S ≅ FreeDiagram S`. The forward direction is a denotation
  `⟦-⟧ : Term S m n -> LPortGraph S m n` defined by structural recursion
  (`T_id`, `T_braid`, `T_comp` by splice, `T_tens` by juxtaposition, `T_gen` by
  a single labelled vertex), shown to respect `TermEq`
  (`Construction/PROP/TermEq.v`) — soundness. The backward direction is a
  normal-form/layering argument reading any labelled port graph as a term, and
  the two round trips give completeness. Alternatively derive one direction
  from the universal property (`Construction/PROP/Universal.v:174` `InterpF`,
  `:603` `interp_unique`) applied at `FreeDiagram S`, which is the cheaper
  route for soundness and uniqueness.
- Discharge Exercise 5.28: for the signature with exactly one generator of each
  arity (`Rho m n := unit`), prove `FreeDiagram Rho ≅ PG`, i.e. the labelling
  is redundant.
- Update the honest scope note: the header of `Construction/PROP/Free.v` should
  point at the diagrammatic model once it exists, and vice versa.

In-tree donors: the port-graph datatype and PG of §5.2.2,
`Construction/PROP/Term.v:39`, `Construction/PROP/TermEq.v:104`,
`Construction/PROP/Universal.v:174`/`:603`,
`Construction/PROP/Signature.v:50`/`:68`/`:79`,
`Construction/PROP/Instance.v:82`.

## Definition of Done

- [ ] `LPortGraph` and label-preserving isomorphism defined; `FreeDiagram S`
      is a prop.
- [ ] The denotation `Term S m n -> LPortGraph S m n` is defined and proved
      sound for `TermEq`.
- [ ] `FreePROP S ≅ FreeDiagram S` proved as an isomorphism of props (both
      directions).
- [ ] Exercise 5.28 proved: `FreeDiagram` on one-generator-per-arity is `PG`.
- [ ] Statement fidelity to the book (§5.2.4, Definition 5.25 and Exercise
      5.28), with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the denotation, the isomorphism
      and the Exercise 5.28 identification.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated — "free = syntactic" is currently
      advertised as the whole story for `Construction/PROP/Free.v`.

## Verification

```
coqc -R . Category Construction/PROP/PortGraph/Labeled.v
#   Print Assumptions FreePROP_iso_FreeDiagram.
#   Print Assumptions exercise_5_28.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the labelling condition is the book's arity agreement, and the
identification proved is the one Definition 5.25 clause (c) makes — matching
Seven Sketches §5.2.4.

## Dependencies

Depends on: 7sketches:5.2.2:def5.13 (the port-graph datatype).
Depends on: 7sketches:5.2.2:construction-pg (PG, the prop of port graphs —
also the target of Exercise 5.28).

<!-- catalog: {"ids":["7sketches:5.2.4:def5.25","7sketches:5.2.4:ex5.28"],"deps":["7sketches:5.2.2:def5.13","7sketches:5.2.2:construction-pg"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.4: A worked three-generator prop signature — expressions and their diagrams"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:5.2.4:example5.31, 7sketches:5.2.4:ex5.32]
deps_item_ids: [7sketches:5.2.4:def5.25]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.4 (Example 5.31 and
Exercise 5.32), over the signature with generators of arities `1 -> 1`,
`2 -> 2` and `2 -> 1`. Printed pp. 157–158; PDF pp. 169–170. Item IDs:
`7sketches:5.2.4:example5.31`, `7sketches:5.2.4:ex5.32`.

## Background

Prop expressions are built from identities, the symmetry, generators, the
monoidal sum and composition; two different expressions may denote the same
morphism of the free prop, and the diagram is the normal form that makes that
visible. See [nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[nLab: string diagram](https://ncatlab.org/nlab/show/string+diagram).

## Current state in the library

The formation rules are fully in tree: `Term` (`Construction/PROP/Term.v:39`)
with constructors `T_id`, `T_braid`, `T_comp`, `T_tens`, `T_gen`, and
`T_swap := T_braid 1 1` (`:65`) as the book's symmetry `σ : 2 -> 2`. So each
expression the example lists *is* a well-typed inhabitant of `Term S m n` at
the stated arity.

What is missing is any worked instantiation. The only closed `Term` examples in
the tree are the trivial arbitrary-signature ones at
`Construction/PROP/Term.v:86-92` (`wire := T_id 1`, `wire2 := T_id 2`,
`T_nothing := T_id 0`, `T_swap`), and `Single_Sig`/`Sum_Sig`
(`Construction/PROP/Signature.v:68`, `:79`) are used only inside
`Construction/PROP/Tietze.v`'s definitional-extension machinery (`:448`,
`:485`), never to build an illustrative signature. Nothing constructs a
composite of the shape the example gives, and the identity-absorption
illustration is available only as the generic `TE_id_right`
(`Construction/PROP/TermEq.v`), never instantiated at a concrete generator.

Exercise 5.32 asks for the *picture* of a specific expression. Its target does
not exist today — there is no port-graph datatype for a term to denote into and
no term-to-diagram interpretation function (the string-diagram talk at
`Construction/PROP/Signature.v:45` is prose). Note this is a library gap, not a
non-formalizable item: the denotation is exactly what the free-prop diagram
model of §5.2.4 supplies.

## Work to be done

- In a new `Test/SevenSketches5.v` (or `Construction/PROP/Examples.v`, matching
  whichever convention the reviewers prefer for worked material), build the
  book's three-generator signature explicitly as a `Signature`, either by
  `Sum_Sig` of three `Single_Sig`s or directly by a `match` on arities.
- Record each of the example's expressions as a named `Definition` of the right
  `Term S m n` type — the arity being enforced by the indices is the point, so
  the types should be written out rather than inferred.
- Prove the identity-absorption the example illustrates at this concrete
  signature (`f ; id ≈ f`), by instantiating `TE_id_right`.
- Discharge Exercise 5.32 by computing the diagram: apply the term-to-labelled-
  port-graph denotation of §5.2.4 to the exercise's expression and record the
  resulting labelled port graph as a computing `Example` (vertex set, degrees,
  and the structure bijection), plus an `Example` checking it against the
  hand-built diagram the exercise asks the reader to draw.

In-tree donors: `Construction/PROP/Term.v`, `Construction/PROP/TermEq.v`,
`Construction/PROP/Signature.v:68`/`:79`, the diagram denotation of §5.2.4,
`Test/Issue138.v` as precedent for `eq_refl`-checked worked material.

## Definition of Done

- [ ] The three-generator signature is built and each example expression is a
      named, arity-annotated `Term`.
- [ ] The identity-absorption equation is proved at the concrete signature.
- [ ] Exercise 5.32's expression is denoted as a labelled port graph, checked
      by computation against the intended diagram.
- [ ] Statement fidelity to the book (§5.2.4, Example 5.31 and Exercise 5.32),
      with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the worked denotation.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index update not expected (worked-example material).

## Verification

```
coqc -R . Category Test/SevenSketches5.v
#   Print Assumptions exercise_5_32_diagram.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the expressions match those listed in Seven Sketches §5.2.4
Example 5.31, and the exercise's composite has the arity the book states.

## Dependencies

Depends on: 7sketches:5.2.4:def5.25 (the diagram model of the free prop —
the target of the drawing).

<!-- catalog: {"ids":["7sketches:5.2.4:example5.31","7sketches:5.2.4:ex5.32"],"deps":["7sketches:5.2.4:def5.25"]} -->

---8<---

```yaml
title: "Seven Sketches 5.2.5: The free prop versus the prop presented with no equations"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:5.2.5:ex5.35]
deps_item_ids: [7sketches:5.2.4:def5.25]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.2.5 (Exercise 5.35,
following Rough Definition 5.33 and Remark 5.34). Printed p. 159; PDF p. 171.
Item ID: `7sketches:5.2.5:ex5.35`.

## Background

Presenting a prop by generators and no equations ought to give back the free
prop; the exercise asks whether anything subtle separates the two, the
subtlety being that the book defines the free prop diagrammatically and the
presented prop syntactically. See
[nLab: generators and relations](https://ncatlab.org/nlab/show/generators+and+relations)
and [nLab: PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

Both sides are constructed and the comparison map exists, but the comparison
itself is never stated.

- Free side: `FreeCat Σ` / `FreePROP Σ` (`Construction/PROP/Free.v:81`,
  `Construction/PROP/Instance.v:82`).
- Presented side: `PresentedCat E` (`Construction/PROP/Presentation.v:180`)
  as the quotient of `FreeCat` by `TermEqW` (`:136`), and `PresentedPROP`
  (`:312`).
- Comparison: `PresentedProj` (`Construction/PROP/Presentation.v:188`), which
  is the identity on objects and on carriers.

Missing: (1) no lemma says `TermEqW E s t <-> TermEq Σ s t` when `E` is
axiom-free — the only `<->` in proof text under `Construction/PROP/` is
`Construction/PROP/Tietze.v:397` — so nothing shows the quotient is trivial;
(2) no isomorphism or equivalence between the presented prop of the axiom-free
theory and the free prop is asserted; (3) the axiom-free theory is formed
in-tree exactly once, as a `Local Definition` scratch value
(`Construction/PROP/Tietze.v:756`) used only to test that a retraction reduces,
never compared with `FreeCat`. The nearest result,
`AddEqn_derivable_conservative` (`Construction/PROP/Tietze.v:395`), covers
adding a *derivable* equation to an arbitrary theory, not the empty-theory
comparison.

Finally, the book's own "subtle difference" turns on `Free(G)` being defined by
port graphs while the presented prop is expressions-modulo-axioms; that
identification is itself missing in tree (see the diagram-model work of
§5.2.4), so the in-tree pair is currently the two syntactic constructions only.

## Work to be done

- In `Construction/PROP/Presentation/Free.v`, prove the conservativity lemma:
  for the theory with an uninhabited equation system,
  `TermEqW E s t <-> TermEq Σ s t` (the forward direction by induction on
  `TermEqW`, the `TEW_ax` case vacuous; the backward direction by `TEW_termeq`).
- Derive the isomorphism of props `PresentedPROP (Σ, ∅) ≅ FreePROP Σ`, with
  `PresentedProj` as one leg, and record it as an `Iso`/prop-functor
  isomorphism rather than a mere equivalence, since the carriers agree.
- Answer the exercise's actual question in the file header, with the two
  answers separated: *syntactically* there is no difference (the isomorphism
  just proved); *diagrammatically* the book's `Free(G)` is a prop of labelled
  port graphs, so the honest statement is a three-way identification once the
  diagram model exists — state that corollary too, chaining through the
  §5.2.4 isomorphism.

In-tree donors: `Construction/PROP/Presentation.v:136`/`:180`/`:188`/`:312`,
`Construction/PROP/Free.v:52`/`:81`, `Construction/PROP/TermEq.v`,
`Construction/PROP/Tietze.v:395` as the proof pattern for a conservativity
argument.

## Definition of Done

- [ ] The conservativity lemma for the axiom-free theory is proved in both
      directions.
- [ ] `PresentedPROP (Σ, ∅) ≅ FreePROP Σ` proved as props.
- [ ] The three-way corollary through the diagram model is stated and proved.
- [ ] The exercise's "is there a subtle difference?" is answered explicitly in
      the header, with the syntactic and diagrammatic readings distinguished.
- [ ] Statement fidelity to the book (§5.2.5, Exercise 5.35), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the conservativity lemma and the
      isomorphism.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated if the three-way identification lands.

## Verification

```
coqc -R . Category Construction/PROP/Presentation/Free.v
#   Print Assumptions TermEqW_empty_iff_TermEq.
#   Print Assumptions PresentedPROP_empty_iso_FreePROP.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the statement answers Seven Sketches §5.2.5 Exercise 5.35, and
distinguishes the syntactic from the diagrammatic reading of `Free(G)`.

## Dependencies

Depends on: 7sketches:5.2.4:def5.25 (the diagram model of the free prop —
needed for the book's "subtle difference" half).

<!-- catalog: {"ids":["7sketches:5.2.5:ex5.35"],"deps":["7sketches:5.2.4:def5.25"]} -->

---8<---

```yaml
title: "Seven Sketches 5.3.1: Rigs — the class, the naturals and the booleans, and rings as rigs"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.3.1:def5.36, 7sketches:5.3.1:example5.37, 7sketches:5.3.1:example5.38, 7sketches:5.3.1:example5.42]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.3.1 (Definition 5.36
with its footnotes, Examples 5.37, 5.38 and 5.42). Printed pp. 159–160;
PDF pp. 171–172. Item IDs: `7sketches:5.3.1:def5.36`,
`7sketches:5.3.1:example5.37`, `7sketches:5.3.1:example5.38`,
`7sketches:5.3.1:example5.42`.

## Background

A rig (semiring) is a ring without negatives: a commutative monoid for `+`, a
monoid for `·` (not assumed commutative), with `·` distributing over `+` on
both sides and `0` annihilating. See [nLab: rig](https://ncatlab.org/nlab/show/rig)
and [Wikipedia: semiring](https://en.wikipedia.org/wiki/Semiring).

## Current state in the library

There is no standalone rig structure anywhere: `rg -n '\brig\b|semiring'` finds
only two comment lines in `Theory/Algebra.v` (`:16`, `:25`), and those concern
*rig categories* — categorified high-school algebra in a bicartesian closed
category — a different notion. There is no `Rig` record, no rig homomorphism
and no rig instance.

The axioms do exist, but one categorical level up and for a whole category:
`Class Preadditive` (`Structure/Preadditive.v:34`) is the commutative-monoid
enrichment of hom-setoids, and its fields are exactly the rig clauses when
specialised to a **one-object** category — clause (a) is
`padd_assoc`/`padd_comm`/`padd_zero_left`, (b) is the category's
`comp_assoc`/`id_left`/`id_right`, (c) is `compose_padd_left`/`right`, and (d)
is `compose_pzero_left`/`right`. That one-object specialisation is never taken.

For the naturals (Example 5.37) the library asserts only the *categorified*
statement: on the skeletal `FinSet` (objects literally `nat`), `Nat.add` is the
coproduct (`Instance/FinSet.v:250`), `Nat.mul` is the product
(`Instance/FinSet/Product.v:105`), `0` is initial and `1` terminal, so the rig
laws hold up to isomorphism of finite sets (`Structure/BiCCC.v:46`
`prod_coprod_l`, `:208` `prod_zero_l`); the passage from those isomorphisms to
equations of naturals is not formalized, and the stdlib lemmas
(`Nat.add_assoc`, `Nat.mul_1_l`, …) are consumed pointwise
(e.g. `Instance/FinSet/Product.v:145`) but never assembled.

For the booleans (Example 5.38) only the multiplicative monoid exists, as
`AndGrade` (`Monad/Graded.v:268`, a grading monoid for the exception monad);
`orb` does not occur anywhere in the tree, and neither distributivity nor
annihilation is stated for booleans. The truth-value route
(`Instance/Props.v:53`/`:61`/`:69`/`:80`/`:94`) makes every rig law hold up to
bi-implication, but on `Prop` rather than the two-element algebra.

For Example 5.42 the containment "ring = rig + negatives" *is* asserted, again
one level up: `Class Additive` (`Structure/Additive.v:34`) is a `Preadditive`
category plus `pneg` with `padd f (pneg f) ≈ pzero` (`:47`). There is no
set-level ring, no set-level rig, no `ℝ`, and in fact no `Additive` instance at
all (the only `Preadditive` instance in the tree is `CMon_Preadditive`,
`Instance/CMon/Biproduct.v:573`, which has no negation).

## Work to be done

- In a new `Theory/Algebra/Rig.v`, define `Class Rig` over a setoid carrier —
  `rig_zero`, `rig_add`, `rig_one`, `rig_mul` with `Proper` instances for the
  setoid equivalence, and the four clauses of Definition 5.36 stated with `≈`.
  Add `RigHom` and the category `Rig` (mirroring
  `Theory/Algebra/Monoid/Hom.v`'s `Mon`/`Mon_Forget` shape), plus the
  forgetful functors to `CMon` and `Mon`.
- Prove the bridge the library's existing algebra makes natural and currently
  omits: a `Rig` is exactly a `Preadditive` structure on a one-object category
  (both directions, with the round trips). This is the honest way to connect
  the new set-level notion to `Structure/Preadditive.v:34` and to make every
  preadditive lemma reusable.
- Instances:
  - `Nat_Rig : Rig` on `nat` (Example 5.37), assembling the stdlib arithmetic
    lemmas into one artifact, with the setoid being `eq` on `nat`;
  - `Bool_Rig : Rig` on `bool` with `(false, orb, true, andb)` (Example 5.38),
    proved by `destruct`/`reflexivity`; relate its multiplicative half to the
    existing `AndGrade` (`Monad/Graded.v:268`) so the two do not drift;
  - the ring-to-rig forgetting of Example 5.42: define `Class Ring` as `Rig`
    plus additive inverses (mirroring how `Structure/Additive.v:34` extends
    `Structure/Preadditive.v:34`), give the forgetful `Ring -> Rig`, and record
    the mnemonic in the header. A concrete `ℝ` witness may be supplied by
    importing Coq's stdlib `Reals` — if it is, disclose the stdlib axioms it
    brings in, per `docs/AXIOMS.md` scoping; otherwise state the containment
    parametrically and note the absent witness in `docs/INHABITATION.md`.
- Relate `Nat_Rig` to the categorified statement already in tree: the rig laws
  on `nat` are the *skeletality* shadow of `FinSet`'s bicartesian closed
  structure. Prove at least one direction (`FinSet` coproduct/product object
  actions agree with `Nat_Rig`'s operations) so the two are connected.

In-tree donors: `Structure/Preadditive.v:34`, `Structure/Additive.v:34`,
`Theory/Algebra/Monoid.v:44`, `Theory/Algebra/CommutativeMonoid.v:46`,
`Theory/Algebra/Monoid/Hom.v`, `Instance/CMon.v:32`,
`Instance/FinSet.v:250`, `Instance/FinSet/Product.v:105`,
`Monad/Graded.v:268`.

## Definition of Done

- [ ] `Rig`, `RigHom` and the category of rigs exist, with the four clauses of
      Definition 5.36 stated over a setoid carrier using `≈`.
- [ ] The one-object `Preadditive` ⟺ `Rig` bridge is proved in both
      directions.
- [ ] `Nat_Rig` and `Bool_Rig` instances, with the `AndGrade` reconciliation.
- [ ] `Ring` defined as `Rig` + negatives, with the forgetful functor; the ℝ
      witness either supplied (with its stdlib axioms disclosed) or explicitly
      recorded as absent.
- [ ] The `Nat_Rig` / `FinSet` agreement lemma.
- [ ] Statement fidelity to the book (§5.3.1, Definition 5.36 and Examples
      5.37, 5.38, 5.42) — in particular multiplication is **not** assumed
      commutative.
- [ ] No `Admitted`, `admit`, or new `Axiom` in the core `Rig` development.
- [ ] `Print Assumptions` reported closed for `Rig`, the bridge, `Nat_Rig` and
      `Bool_Rig`.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated — a rig is a new algebraic spine and
      every downstream Chapter 5 issue consumes it.

## Verification

```
coqc -R . Category Theory/Algebra/Rig.v
#   Print Assumptions Rig.
#   Print Assumptions Nat_Rig.
#   Print Assumptions Bool_Rig.
#   Print Assumptions rig_iff_one_object_preadditive.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the axioms match Seven Sketches §5.3.1 Definition 5.36 clause for
clause, including two-sided distributivity and two-sided annihilation, and
including the deliberate omission of commutativity of multiplication.

## Dependencies

None.

<!-- catalog: {"ids":["7sketches:5.3.1:def5.36","7sketches:5.3.1:example5.37","7sketches:5.3.1:example5.38","7sketches:5.3.1:example5.42"],"deps":[]} -->

---8<---

```yaml
title: "Seven Sketches 5.3.1: Every quantale determines a rig"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.3.1:example5.39]
deps_item_ids: [7sketches:5.3.1:def5.36]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.3.1 (Example 5.39).
Printed p. 160; PDF p. 172. Item ID: `7sketches:5.3.1:example5.39`.

## Background

A quantale — a monoidal preorder with all joins, whose tensor distributes over
them — yields a rig with binary join as addition, the empty join as `0`, and
the monoidal product as multiplication. See
[nLab: quantale](https://ncatlab.org/nlab/show/quantale) and
[nLab: rig](https://ncatlab.org/nlab/show/rig).

## Current state in the library

Neither end of the construction exists as a definition. `rg -iln 'quantale'`
finds a single prose line (`Construction/Enriched.v:78`, "preorder- and
quantale-enriched categories"); "complete lattice" appears only as prose at
`Instance/Poset.v:93` and `Structure/Complete.v:71`; and there is no rig
structure at all (see the rig work of §5.3.1). Even the Boolean quantale has no
base: `Two_Initial`, `Two_Cocartesian` and `two_join` do not exist.

## Work to be done

- In a new `Theory/Algebra/Rig/Quantale.v`, construct the rig of a quantale:
  carrier the quantale's underlying setoid (with `≈` the order's
  antisymmetry-free equivalence, i.e. mutual `≤`), `+` binary join, `0` the
  empty join, `·` the monoidal product, `1` the monoidal unit.
- Prove the four rig clauses from the quantale axioms, being explicit about
  where each hypothesis is used: commutativity and associativity of `+` from
  the universal property of joins; distributivity of `·` over binary `+` and
  annihilation by the empty join from the join-preservation the quantale
  demands of its tensor. This is where the Chapter 2 result that closedness is
  equivalent to distributivity of the tensor over joins does the work.
- Record the two instances the surrounding text makes obvious once the
  construction exists: the Boolean quantale gives back the boolean rig of
  §5.3.1, and the Cost quantale gives the tropical rig (min-plus). Prove the
  first as an isomorphism of rigs, since both sides will then be in tree.
- Note in the header what the construction does *not* give: the resulting rig
  is always additively idempotent, so not every rig arises this way — the
  naturals do not.

In-tree donors: the rig class of §5.3.1, `Construction/Enriched.v`,
`Instance/Two/Monoidal.v:105`, and the Chapter 2 quantale development.

## Definition of Done

- [ ] `Rig_of_Quantale` constructed, with all four clauses proved.
- [ ] The Boolean instance identified with the boolean rig of §5.3.1, as an
      isomorphism of rigs.
- [ ] The Cost/tropical instance recorded.
- [ ] The additive-idempotence limitation disclosed in the header.
- [ ] Statement fidelity to the book (§5.3.1, Example 5.39), with the setoid
      `≈` discipline (here: mutual `≤` in the preorder).
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `Rig_of_Quantale` and the Boolean
      identification.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated if the quantale spine gains an entry.

## Verification

```
coqc -R . Category Theory/Algebra/Rig/Quantale.v
#   Print Assumptions Rig_of_Quantale.
#   Print Assumptions Bool_Rig_iso_Rig_of_Bool_quantale.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the additive operation is binary join and the additive unit is the
*empty* join, exactly as Seven Sketches §5.3.1 Example 5.39 states.

## Dependencies

Depends on: #799 (unital commutative quantales — the class this consumes).
Depends on: #801 (closedness of a monoidal preorder equals distributivity of
the tensor over joins — the distributivity clause).
Depends on: 7sketches:5.3.1:def5.36 (the rig class).

<!-- catalog: {"ids":["7sketches:5.3.1:example5.39"],"deps":["#799","#801","7sketches:5.3.1:def5.36"]} -->

---8<---

```yaml
title: "Seven Sketches 5.3.1: Square matrices over a rig form a rig, and are not commutative"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.3.1:example5.40, 7sketches:5.3.1:ex5.41]
deps_item_ids: [7sketches:5.3.1:def5.36]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.3.1 (Example 5.40 and
Exercise 5.41). Printed p. 160; PDF p. 172. Item IDs:
`7sketches:5.3.1:example5.40`, `7sketches:5.3.1:ex5.41`.

## Background

`n × n` matrices over a rig form a rig under entrywise addition and the
sum-of-products product; it is the standard example showing why rig
multiplication is not assumed commutative. See
[nLab: matrix](https://ncatlab.org/nlab/show/matrix) and
[Wikipedia: semiring](https://en.wikipedia.org/wiki/Semiring).

## Current state in the library

There is no `Mat_n(R)`: no rig to take entries from, no type of `n × n`
matrices, no entrywise addition or Σ-product, and no theorem that matrices form
a rig. What exists is the `n = 2` shadow of the matrix calculus inside a
CMon-enriched category: `bi_pair_decomp` (`Structure/Semiadditive.v:86`)
exhibits a column as the `padd` of its entries, so addition of matrices is
entrywise `padd`; `bi_copair_pair` (`:101`) is exactly the 1×2-row-against-2×1-
column instance of the sum-of-products law. Only the *binary* `Biproduct`
(`Structure/Biproduct.v:42`) exists — there are no n-ary biproducts — and
nothing states that the resulting collection is itself a rig.

For Exercise 5.41 part (1), the identity matrix appears only in disguise and
only at `n = 2`: `can_comparison` (`Structure/Semiadditive.v:288`, with the
comment at `:287` naming it "the identity matrix") has its four entries
computed — `exl_can_inl ≈ id` (`:299`), `exr_can_inl ≈ zero_mor` (`:305`),
`exl_can_inr ≈ zero_mor` (`:311`), `exr_can_inr ≈ id` (`:317`) — but the
morphism is introduced as the canonical coproduct-to-product comparison (whose
invertibility is the hypothesis of `bicartesian_preadditive`,
`Structure/Semiadditive.v:573`), never as a multiplicative identity. Part (2) —
an explicit non-commuting pair over the naturals — is entirely absent and
cannot be phrased until a rig and `Mat_n` exist.

## Work to be done

- In a new `Theory/Algebra/Rig/Matrix.v`, define `SqMat R n` as
  `Fin.t n -> Fin.t n -> carrier R` with the pointwise setoid, entrywise
  addition, the zero matrix, the Σ-product (a `Fin`-indexed fold using the rig's
  `+`, with its `Proper` instance), and the Kronecker-delta identity matrix.
- Prove `SqMat_Rig : Rig (SqMat R n)`: additive commutative monoid entrywise;
  associativity of the product by the usual double-sum exchange (state the
  Σ-swap lemma separately, it will be reused by the matrix prop of §5.3.3);
  two-sided distributivity; annihilation. Answer Exercise 5.41 part (1) by
  proving the Kronecker delta is the multiplicative unit.
- Answer Exercise 5.41 part (2) with a concrete counterexample over `Nat_Rig`
  at `n = 2`, decided by computation (`eq_refl`-checked entries), plus the
  general statement that `SqMat` is not commutative even when `R` is.
- Connect to the existing categorical shadow: show that for `n = 2` the entries
  of `SqMat`'s identity match the four `can_comparison` entry lemmas, so the
  new development and `Structure/Semiadditive.v` agree. If n-ary biproducts are
  added in the process, state the general biproduct-matrix correspondence; if
  not, record explicitly in the header that only the binary case is bridged.

In-tree donors: the rig class of §5.3.1, `Structure/Semiadditive.v:86`/`:101`/
`:288`-`:317`, `Structure/Biproduct.v:42`, `Structure/Preadditive.v:34`,
`Instance/FinSet.v` (Fin-indexed folds and decision by computation).

## Definition of Done

- [ ] `SqMat R n` defined with a setoid, entrywise addition and the
      sum-of-products product, all `Proper`.
- [ ] `SqMat_Rig` proved, including the Σ-swap lemma stated separately for
      reuse.
- [ ] Exercise 5.41 part (1): the identity matrix is the multiplicative unit.
- [ ] Exercise 5.41 part (2): a computing counterexample to commutativity over
      the naturals.
- [ ] The `n = 2` agreement with `can_comparison`'s entries.
- [ ] Statement fidelity to the book (§5.3.1, Example 5.40 and Exercise 5.41),
      with the setoid `≈` discipline throughout.
- [ ] No `Admitted`, `admit`, or new `Axiom` — in particular no `funext` for
      matrix equality (use the pointwise setoid).
- [ ] `Print Assumptions` reported closed for `SqMat_Rig` and the
      counterexample.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated alongside the rig entry.

## Verification

```
coqc -R . Category Theory/Algebra/Rig/Matrix.v
#   Print Assumptions SqMat_Rig.
#   Print Assumptions SqMat_not_commutative.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: addition is entrywise and multiplication is the sum-of-products
over the middle index, exactly as Seven Sketches §5.3.1 Example 5.40 defines
them.

## Dependencies

Depends on: 7sketches:5.3.1:def5.36 (the rig class, and the naturals as a rig
for the counterexample).

<!-- catalog: {"ids":["7sketches:5.3.1:example5.40","7sketches:5.3.1:ex5.41"],"deps":["7sketches:5.3.1:def5.36"]} -->

---8<---

```yaml
title: "Seven Sketches 5.3.2: The signal-flow signature G_R and the free prop SFG_R"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.3.2:def5.45]
deps_item_ids: [7sketches:5.3.1:def5.36, 7sketches:5.2.1:def5.2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.3.2 (Definition 5.45).
Printed p. 163; PDF p. 175. Item ID: `7sketches:5.3.2:def5.45`.

## Background

Simplified (feedback-free) signal flow graphs over a rig `R` are the morphisms
of the free prop on five families of generators: addition `2 -> 1`, zero
`0 -> 1`, copy `1 -> 2`, discard `1 -> 0`, and one amplifier `1 -> 1` for each
element of `R`. See
[Wikipedia: signal-flow graph](https://en.wikipedia.org/wiki/Signal-flow_graph)
and [nLab: PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

The general machinery is complete and directly reusable: `Signature`
(`Construction/PROP/Signature.v:50`) with the `Single_Sig` (`:68`) and
`Sum_Sig` (`:79`) constructors, and `FreePROP S : PROP`
(`Construction/PROP/Instance.v:82`) with its universal property in
`Construction/PROP/Universal.v`. The fibred arity encoding (`S m n` is the
*type* of generators `m -> n`) even makes an `R`-indexed amplifier family
directly expressible.

What is absent is this item's particular data: the signature with the five
generator families and the abbreviation naming its free prop. No signal-flow
generators exist anywhere (searches for "signal flow"/"SFG"/"amplif" return
only bibliographic prose in six file headers, e.g.
`Construction/ColouredPROP.v:34`), and the rig indexing the amplifiers does not
exist either (see the rig work of §5.3.1). The only concrete generator
signatures in tree are `Empty_Sig`, `Single_Sig`, the coloured supply
generators (`Construction/ColouredPROP/Supply/Instance.v:114`) and
`Instance/ZX.v`.

## Work to be done

- In a new `Instance/SignalFlow.v`, define the signature over a rig `R`:
  `SFSig R : Signature := fun m n => match (m, n) with (2,1) => unit (* add *)
  | (0,1) => unit (* zero *) | (1,2) => unit (* copy *) | (1,0) => unit
  (* discard *) | (1,1) => carrier R (* amplify *) | _ => Empty_set end`,
  or the equivalent inductive presentation with five constructors — prefer the
  inductive one, since it gives named constructors (`sf_add`, `sf_zero`,
  `sf_copy`, `sf_discard`, `sf_amp a`) that every downstream statement will
  quote, and it avoids `match`-on-arity clutter in later proofs.
- Define `SFG R := FreePROP (SFSig R)` and export the five generators as
  morphisms of the free prop at their stated arities, together with the
  drawing-convention note (§5.3.2 Example 5.46, a purely typographical remark
  which the library records as prose, not as a definition).
- Prove the small sanity facts a later semantics will lean on: the signature is
  decidable/`Empty_set` off the five arities, the amplifier family is `Proper`
  for the rig's setoid equality (so that `a ≈ b` gives `sf_amp a ≈ sf_amp b`
  after interpretation), and the generators are pairwise distinct as terms.
- Record in the header the scope the book itself flags: "simplified" means
  feedback-free, and feedback is added by the mirrored-generator prop of
  §5.4.3.

In-tree donors: `Construction/PROP/Signature.v:50`/`:68`/`:79`,
`Construction/PROP/Instance.v:82`, `Construction/PROP/Term.v:39`,
`Instance/ZX.v` (precedent for a concrete generator set), the rig class of
§5.3.1.

## Definition of Done

- [ ] `SFSig R` and `SFG R := FreePROP (SFSig R)` defined, with the five
      generators exported at the arities Definition 5.45 assigns them.
- [ ] The amplifier family respects the rig's setoid equality.
- [ ] The "simplified means feedback-free" scope note recorded in the header.
- [ ] Statement fidelity to the book (§5.3.2, Definition 5.45), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `SFG` and each exported
      generator.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (signal flow graphs are a new
      application spine for the PROP development).

## Verification

```
coqc -R . Category Instance/SignalFlow.v
#   Print Assumptions SFG.
#   Print Assumptions sf_amp_Proper.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the five generators have the arities Seven Sketches §5.3.2 assigns
by counting dangling wires — add `2 -> 1`, zero `0 -> 1`, copy `1 -> 2`,
discard `1 -> 0`, amplify `1 -> 1`.

## Dependencies

Depends on: 7sketches:5.3.1:def5.36 (the rig class — the amplifier index).
Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement).

<!-- catalog: {"ids":["7sketches:5.3.2:def5.45"],"deps":["7sketches:5.3.1:def5.36","7sketches:5.2.1:def5.2"]} -->

---8<---

```yaml
title: "Seven Sketches 5.3.3: Mat(R), the prop of matrices over a rig"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.3.3:eq5.48, 7sketches:5.3.3:remark5.49, 7sketches:5.3.3:def5.50, 7sketches:5.3.3:ex5.51]
deps_item_ids: [7sketches:5.3.1:def5.36, 7sketches:5.2.1:def5.2]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.3.3 (the displayed
matrix-composition law (5.48), Remark 5.49 on the row-vector convention,
Definition 5.50, and Exercise 5.51). Printed p. 164; PDF p. 176. Item IDs:
`7sketches:5.3.3:eq5.48`, `7sketches:5.3.3:remark5.49`,
`7sketches:5.3.3:def5.50`, `7sketches:5.3.3:ex5.51`.

## Background

Matrices with entries in a rig form a prop: objects the natural numbers,
morphisms `m -> n` the `m × n` matrices, composition matrix multiplication in
diagrammatic order, monoidal product the direct (block-diagonal) sum. See
[nLab: matrix](https://ncatlab.org/nlab/show/matrix),
[nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[nLab: opposite category](https://ncatlab.org/nlab/show/opposite+category)
for the orientation Remark 5.49 fixes.

## Current state in the library

No matrix datatype exists. `rg -il 'matrix|Matrix|\bMat\b'` finds 13 files and
every hit is prose in a header essay (`Structure/Abelian.v`,
`Structure/Semiadditive.v`, `Structure/Preadditive.v`,
`Structure/Bicartesian.v`, `Instance/ZX.v`, `Functor/Hom/Yoneda.v`,
`Theory/Profunctor.v`, `Theory/Equivalence.v`, the monoidal files,
`Construction/Enriched.v`, `Construction/Comma.v`); there is no
`Definition`/`Record`/`Class`. An enumeration of every `PROP` instance in the
tree returns exactly four — `FreePROP` (`Construction/PROP/Instance.v:82`),
`PresentedPROP` (`Construction/PROP/Presentation.v:312`), `Lawvere_PROP`
(`Theory/Lawvere/PROP.v:179`), `RepeatPROP`
(`Construction/ColouredPROP/UnitBridge.v:344`) — and none has matrix homs. Nor
is there a rig to take entries from (see §5.3.1). Consequently Exercise 5.51's
concrete block-diagonal computation cannot be stated: neither the carrier nor
the tensor exists.

Remark 5.49's content — that the book's matrices act on *row* vectors so that
composition runs in the same left-to-right order as the composition operator —
also has no counterpart. The library fixes the classical order
(`Instance/Rel.v:33`: `compose f g` applies `g` first), so the orientation must
be stated deliberately rather than inherited.

## Work to be done

- In a new `Instance/Mat.v`, define `Mat R` over a rig: `obj := nat`,
  `hom m n := Fin.t m -> Fin.t n -> carrier R` with the pointwise setoid,
  identity the Kronecker delta, composition the sum-over-the-middle-index law
  of the book's (5.48) — being explicit about orientation, since the library's
  `∘` is classical while the book's `;` is diagrammatic. State the relationship
  as a lemma (`Mat_compose_is_book_semicolon : g ∘ f = f ; g`) and put
  Remark 5.49's convention in the header, together with the observation that
  choosing the other orientation gives `Mat R ^op` and that for a commutative
  rig transposition is an isomorphism `Mat R ≅ (Mat R)^op`.
- Prove the category laws (associativity by the Σ-swap lemma, unit laws by
  Kronecker collapse) and the `Proper` instance for composition.
- Add the monoidal layer: the direct sum `A ⊕ B : m + p -> n + q` as the
  block-diagonal matrix (zero off the blocks), the braid as the permutation
  matrix, strictness on objects by `Nat.add`, and `Mat_PROP : PROP` with the
  strict refinement of §5.2.1.
- Discharge Exercise 5.51 as a computing `Example` over the naturals: the given
  `2 × 3` and `1 × 4` matrices, their direct sum as the stated `3 × 7`
  block-diagonal matrix, checked entrywise by `eq_refl`.
- Relate to the existing biproduct matrix calculus: for a CMon-enriched
  category with biproducts there is a functor from `Mat R` into it once `R` is
  the endomorphism rig of the unit; at minimum, state the `n = 2` agreement
  with `bi_copair_pair` (`Structure/Semiadditive.v:101`) so the two matrix
  vocabularies are connected.

In-tree donors: the rig class and the Σ-swap lemma of §5.3.1,
`Instance/FinSet.v` (Fin folds, `fin_split`/`merge` for the block case
analysis), `Structure/Semiadditive.v:86`/`:101`, `Construction/PROP.v:68`,
`Structure/Monoidal/Strict.v:52`.

## Definition of Done

- [ ] `Mat R : Category` with the book's composition law, all laws proved, and
      the composition `Proper` instance.
- [ ] The orientation lemma and Remark 5.49's convention recorded, with the
      `Mat R ≅ (Mat R)^op` transposition statement for a commutative rig.
- [ ] The direct sum, the braid and `Mat_PROP : PROP` with the strict
      refinement of §5.2.1.
- [ ] Exercise 5.51's direct sum computes by `eq_refl`.
- [ ] The `n = 2` agreement with the in-tree biproduct matrix calculus.
- [ ] Statement fidelity to the book (§5.3.3, (5.48), Remark 5.49, Definition
      5.50, Exercise 5.51), with the setoid `≈` discipline on morphisms — the
      hom-setoid is entrywise `≈` in the rig, never `=` on functions.
- [ ] No `Admitted`, `admit`, or new `Axiom` — in particular no `funext`.
- [ ] `Print Assumptions` reported closed for `Mat`, `Mat_PROP` and the
      Exercise 5.51 witness.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated — this is the library's first matrix
      category and a flagship target for the PROP development.

## Verification

```
coqc -R . Category Instance/Mat.v
#   Print Assumptions Mat.
#   Print Assumptions Mat_PROP.
#   Print Assumptions exercise_5_51.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: composition matches the book's displayed law (5.48) up to the
declared orientation, and the monoidal product is the block-diagonal direct sum
with zero off-diagonal blocks — matching Seven Sketches §5.3.3 Definition 5.50.

## Dependencies

Depends on: #221 (the matrix category Matr_K — the field-entry ancestor of this
prop; this issue generalises the entries to a rig and adds the monoidal
structure the earlier issue does not scope).
Depends on: #789 (V-matrices over a quantale and the category Mat(V) — the
quantale-entry sibling; the two should share the Σ-fold infrastructure).
Depends on: 7sketches:5.3.1:def5.36 (the rig class).
Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement).

<!-- catalog: {"ids":["7sketches:5.3.3:eq5.48","7sketches:5.3.3:remark5.49","7sketches:5.3.3:def5.50","7sketches:5.3.3:ex5.51"],"deps":["#221","#789","7sketches:5.3.1:def5.36","7sketches:5.2.1:def5.2"]} -->

---8<---

```yaml
title: "Seven Sketches 5.3.4: The semantics prop functor S : SFG_R → Mat(R)"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.3.4:construction-generator-matrix-table, 7sketches:5.3.4:thm5.53, 7sketches:5.3.2:ex5.43, 7sketches:5.3.4:ex5.55]
deps_item_ids: [7sketches:5.3.2:def5.45, 7sketches:5.3.3:def5.50, 7sketches:5.2.1:def5.11]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.3.4 (the generator
interpretation table (5.52) and Theorem 5.53), together with §5.3.2
(Exercise 5.43) and §5.3.4 (Exercise 5.55). Printed pp. 162, 165–167; PDF
pp. 174, 177–180. Item IDs:
`7sketches:5.3.4:construction-generator-matrix-table`,
`7sketches:5.3.4:thm5.53`, `7sketches:5.3.2:ex5.43`, `7sketches:5.3.4:ex5.55`.

## Background

Assigning a matrix to each generator icon extends, by the universal property of
the free prop, to a unique prop functor from signal flow graphs to matrices —
the denotational semantics of the graphical calculus. See
[nLab: PROP](https://ncatlab.org/nlab/show/PROP) and
[Wikipedia: signal-flow graph](https://en.wikipedia.org/wiki/Signal-flow_graph).

## Current state in the library

Only the abstract half is present, but at full strength. The free-prop
universal property is in tree as `InterpF` (`Construction/PROP/Universal.v:174`)
with `InterpF_extends_valuation` (`:186`, by `eq_refl`),
`InterpF_Strict` (`:416`), `InterpF_Symmetric` (`:525`) and the uniqueness
theorem `interp_unique` (`:603`); `Theory/Lawvere/PROP.v:209`
(`Lawvere_PROP_interp`) already instantiates exactly this machinery at another
target, so the pattern is proven.

What is missing is this item's data: (i) the target prop of matrices with
matrix multiplication as composition and direct sum as tensor (see §5.3.3);
(ii) the signal-flow signature and its free prop (see §5.3.2); (iii) the
valuation realising the interpretation table. Consequently Theorem 5.53 cannot
be instantiated, and neither exercise can be posed — Exercise 5.43's evaluation
of a concrete diagram has no semantics to evaluate under, and Exercise 5.55's
two re-associated copy diagrams have no matrices to compare.

## Work to be done

- In a new `Instance/SignalFlow/Semantics.v`, define the valuation realising
  table (5.52): amplify by `a` ↦ the `1 × 1` matrix `(a)`; add ↦ the `2 × 1`
  column of ones; zero ↦ the `0 × 1` empty matrix; copy ↦ the `1 × 2` row of
  ones; discard ↦ the `1 × 0` empty matrix. Keep the two empty matrices
  distinct by their shapes, as the accompanying prose stresses — in the `Fin`
  encoding this is automatic, and it is worth an `Example` recording that
  `0 × 1` and `1 × 0` are not interchangeable.
- Obtain `S : SFG R ⟶ Mat R` by applying `InterpF` to that valuation, and
  package it as a `PROPFunctor` (§5.2.1) using `InterpF_Strict` and
  `InterpF_Symmetric`; state Theorem 5.53 as the named artifact, and its
  uniqueness as the corresponding instance of `interp_unique`, so that "the
  semantics is *the* prop functor extending the table" is the recorded form.
- Record the automatic consequences the theorem's one-line proof relies on: `S`
  preserves identities, composition, monoidal products and the symmetry — each
  as a named lemma, since later chapters cite them.
- Discharge Exercise 5.43 by evaluating the book's displayed diagram over the
  naturals: build the term (two amplify-by-3 icons, one amplify-by-5, two
  copies, two adds), apply `S`, and check the resulting `2 × 2` matrix by
  computation; state the two output signals as the two entries of the row
  action.
- Discharge Exercise 5.55: build the two `1 -> 3` diagrams that copy and then
  re-copy the upper, respectively the lower, wire; compute both matrices;
  prove they are equal (both the row of ones), which is the coassociativity law
  of copy as read through the semantics.

In-tree donors: `Construction/PROP/Universal.v:174`/`:186`/`:416`/`:525`/`:603`,
`Theory/Lawvere/PROP.v:209` as the instantiation precedent, the signal-flow
signature of §5.3.2, the matrix prop of §5.3.3, the prop-functor class of
§5.2.1.

## Definition of Done

- [ ] The valuation realising table (5.52) is defined, with the two empty
      matrices distinguished by shape.
- [ ] `S : SFG R ⟶ Mat R` exists as a `PROPFunctor`, with Theorem 5.53 stated
      as a named artifact and its uniqueness recorded.
- [ ] Preservation of identities, composition, tensor and symmetry recorded as
      named lemmas.
- [ ] Exercise 5.43's diagram evaluates by computation to the stated outputs.
- [ ] Exercise 5.55's two diagrams are computed and proved equal.
- [ ] Statement fidelity to the book (§5.3.4, table (5.52) and Theorem 5.53;
      §5.3.2 Exercise 5.43; §5.3.4 Exercise 5.55), with the setoid `≈`
      discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `S`, its uniqueness, and both
      exercise witnesses.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (the first denotational semantics for
      a graphical calculus in the library).

## Verification

```
coqc -R . Category Instance/SignalFlow/Semantics.v
#   Print Assumptions SFG_semantics.
#   Print Assumptions SFG_semantics_unique.
#   Print Assumptions exercise_5_43.
#   Print Assumptions exercise_5_55.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: each generator receives the matrix table (5.52) assigns it, and
the functor is obtained from the free-prop universal property exactly as
Seven Sketches §5.3.4 Theorem 5.53 argues.

## Dependencies

Depends on: 7sketches:5.3.2:def5.45 (the signal-flow signature and SFG).
Depends on: 7sketches:5.3.3:def5.50 (the matrix prop).
Depends on: 7sketches:5.2.1:def5.11 (prop functors).

<!-- catalog: {"ids":["7sketches:5.3.4:construction-generator-matrix-table","7sketches:5.3.4:thm5.53","7sketches:5.3.2:ex5.43","7sketches:5.3.4:ex5.55"],"deps":["7sketches:5.3.2:def5.45","7sketches:5.3.3:def5.50","7sketches:5.2.1:def5.11"]} -->

---8<---

```yaml
title: "Seven Sketches 5.3.4: The matrix of a signal flow graph counts amplification along paths"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.3.4:prop5.54]
deps_item_ids: [7sketches:5.3.4:thm5.53, 7sketches:5.2.4:def5.25]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.3.4 (Proposition 5.54
and its proof by structural induction). Printed p. 166; PDF pp. 178–179.
Item ID: `7sketches:5.3.4:prop5.54`.

## Background

The abstractly defined semantics agrees with the concrete reading of a signal
flow graph: the `(i,j)` entry of the matrix is the total amplification the
`i`th input contributes to the `j`th output, summed over paths. See
[Wikipedia: signal-flow graph](https://en.wikipedia.org/wiki/Signal-flow_graph)
and [nLab: PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

Absent, and the reason is structural: in tree there is only *one* semantics and
no matrix entries at all. `interp` (`Construction/PROP/Interp.v:904`) is the
inductive denotation with clauses sending composition to `∘`, the tensor to
`⊞` and a generator to its valuation, and `interp_unique`
(`Construction/PROP/Universal.v:603`) is the structural-induction tool that
would drive the proof — but the proposition's content is the *agreement of two
independently defined semantics*, and the path-tracing one does not exist.

## Work to be done

- In a new `Instance/SignalFlow/PathSemantics.v`, define the concrete reading
  independently of the inductive denotation: for a signal flow graph, the
  amplification from input `i` to output `j` as a sum over the paths through
  the diagram, each path contributing the product of the amplifier labels on
  it. The clean way to do this in the library's setting is to define it on the
  *diagram* model — labelled port graphs (§5.2.4) — where paths are literally
  paths in the internal flow graph, so the definition is genuinely independent
  of the term structure; a term-level definition by recursion would beg the
  question the proposition asks.
- Prove Proposition 5.54: for every signal flow graph, the path-tracing matrix
  equals the matrix produced by the semantics functor. Follow the book's
  induction over the formation rules — base cases the empty diagram (`0 × 0`),
  the wire (`(1)`), the symmetry (the `2 × 2` swap) and amplify-by-`a`
  (`(a)`); inductive cases composition (matrix product, i.e. paths concatenate
  through the middle boundary) and monoidal product (block diagonal, i.e. no
  paths cross between the summands, which is where acyclicity and the
  boundary-disjointness of the tensor are used).
- State the two corollaries that make the proposition usable: the entry is zero
  when no path connects the two ports, and post/pre-composition with a
  permutation permutes rows/columns.

In-tree donors: the semantics functor of §5.3.4, the labelled port-graph model
of §5.2.4, `Construction/PROP/Interp.v:904`,
`Construction/PROP/Universal.v:603`, the Σ-fold lemmas of §5.3.1.

## Definition of Done

- [ ] A path-tracing matrix is defined independently of the inductive
      denotation (on the diagram model, not by recursion on terms).
- [ ] Proposition 5.54 proved: the two agree, by induction over the formation
      rules with all four base cases and both inductive cases.
- [ ] The zero-entry and permutation corollaries are stated and proved.
- [ ] Statement fidelity to the book (§5.3.4, Proposition 5.54), with the
      setoid `≈` discipline — entries compared with the rig's `≈`.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the agreement theorem.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated alongside the signal-flow entry.

## Verification

```
coqc -R . Category Instance/SignalFlow/PathSemantics.v
#   Print Assumptions path_matrix_eq_semantics.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the path-tracing definition is genuinely independent of the
inductive one, so the theorem has content, and the induction follows Seven
Sketches §5.3.4 Proposition 5.54.

## Dependencies

Depends on: 7sketches:5.3.4:thm5.53 (the semantics functor).
Depends on: 7sketches:5.2.4:def5.25 (the labelled port-graph model, on which
the path reading is defined).

<!-- catalog: {"ids":["7sketches:5.3.4:prop5.54"],"deps":["7sketches:5.3.4:thm5.53","7sketches:5.2.4:def5.25"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.1: Fullness of the signal-flow semantics — every matrix is realized"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.1:prop5.56, 7sketches:5.4.1:ex5.58, 7sketches:5.4.1:ex5.59]
deps_item_ids: [7sketches:5.3.4:thm5.53]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.1 (Proposition 5.56
with the displayed `2 × 2` construction (5.57), Exercise 5.58, Exercise 5.59).
Printed p. 169; PDF p. 181. Item IDs: `7sketches:5.4.1:prop5.56`,
`7sketches:5.4.1:ex5.58`, `7sketches:5.4.1:ex5.59`.

## Background

Every matrix over a rig is the semantics of some signal flow graph, built in
four layers — copy/discard, scalars, permutations, add/zero — so the semantics
functor is full. See [nLab: full functor](https://ncatlab.org/nlab/show/full+functor)
and [Wikipedia: signal-flow graph](https://en.wikipedia.org/wiki/Signal-flow_graph).

## Current state in the library

Absent. Neither the source prop nor the target prop of the statement exists
(see §5.3.2 and §5.3.3), so fullness cannot be posed; a whole-tree search for
signal-flow vocabulary returns only header prose in six files, and there is no
matrix type to be surjected onto. `Full` as a functor property does exist
generically in the library and is the right vocabulary to reuse, but it has no
instance here.

## Work to be done

- In a new `Instance/SignalFlow/Full.v`, define the realization map: for an
  `m × n` matrix `M`, the diagram
  `copy^{(n)} ⊗ … ; amplifiers ; permutation ; add^{(m)} …` as the composite of
  the book's four layers, generalized from the displayed `2 × 2` case to
  arbitrary `m, n` (Exercise 5.59 is exactly this generalization, so it is
  discharged by writing the construction, not separately).
  - layer (i): from each of the `m` inputs, an `n`-fold copy (a balanced tree of
    `copy`, with `discard` when `n = 0`);
  - layer (ii): the `m·n` amplifiers, one per entry, labelled `M(i,j)`;
  - layer (iii): the permutation regrouping the wires by output index;
  - layer (iv): into each of the `n` outputs, an `m`-fold add (with `zero`
    when `m = 0`).
- Prove `S(realize M) ≈ M` — by the path-tracing proposition of §5.3.4 if it is
  available (there is exactly one path from input `i` to output `j`, carrying
  exactly one amplifier), or directly by computing the four layers' matrices
  and multiplying, which is self-contained. State the conclusion as fullness of
  the semantics functor using the library's `Full` vocabulary.
- Discharge Exercise 5.58 with three computing `Example`s: the realizations of
  the `1 × 3` matrix with entries `0, 1, 2`, of the `2 × 2` zero matrix (which
  exercises the `discard`/`zero` degenerate layers), and of the `2 × 3` matrix
  with rows `(1 2 3)` and `(4 5 6)`; each checked by `S(realize M) ≈ M` by
  computation.
- Record the degenerate cases explicitly (`m = 0`, `n = 0`), since they are the
  ones the displayed `2 × 2` case hides and the ones a reviewer will probe.

In-tree donors: the semantics functor of §5.3.4, the signal-flow signature of
§5.3.2, the matrix prop of §5.3.3, `Construction/PROP/Term.v` (term
combinators for the balanced trees), and the library's `Full` definition.

## Definition of Done

- [ ] `realize : Mat R m n -> SFG R m n` defined for all `m, n`, including the
      degenerate cases.
- [ ] `S (realize M) ≈ M` proved, and fullness of the semantics functor stated
      with the library's `Full` vocabulary.
- [ ] Exercise 5.58's three matrices realized, with the round trip checked by
      computation.
- [ ] Statement fidelity to the book (§5.4.1, Proposition 5.56 and Exercises
      5.58, 5.59), with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `realize`, the round trip and the
      fullness statement.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated alongside the signal-flow entry.

## Verification

```
coqc -R . Category Instance/SignalFlow/Full.v
#   Print Assumptions SFG_semantics_Full.
#   Print Assumptions exercise_5_58.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the construction is the book's four-layer diagram generalized to
arbitrary `m × n`, and the proof obligation is exactly `S(g) = M` — matching
Seven Sketches §5.4.1 Proposition 5.56 and Exercise 5.59.

## Dependencies

Depends on: 7sketches:5.3.4:thm5.53 (the semantics functor being shown full).

<!-- catalog: {"ids":["7sketches:5.4.1:prop5.56","7sketches:5.4.1:ex5.58","7sketches:5.4.1:ex5.59"],"deps":["7sketches:5.3.4:thm5.53"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.2: Bimonoid objects, and the bimonoid on the object 1 of Mat(R)"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.2:example5.68, 7sketches:5.4.2:example5.70]
deps_item_ids: [7sketches:5.3.3:def5.50]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.2 (Examples 5.68 and
5.70), read against Definition 5.65. Printed pp. 172–173; PDF pp. 184–185.
Item IDs: `7sketches:5.4.2:example5.68`, `7sketches:5.4.2:example5.70`.

## Background

In the prop of matrices the object `1` carries both a commutative monoid
(addition and zero) and a cocommutative comonoid (copy and discard), and the
two interact as a bimonoid — the algebraic content of the graphical calculus.
See [nLab: monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category),
[nLab: comonoid](https://ncatlab.org/nlab/show/comonoid),
[nLab: bimonoid](https://ncatlab.org/nlab/show/bimonoid) and
[Wikipedia: bialgebra](https://en.wikipedia.org/wiki/Bialgebra).

## Current state in the library

The monoid and comonoid layers exist separately and at full strength:
`Class Monoid` (`Theory/Algebra/Monoid.v:44`), `CommutativeMonoid`
(`Theory/Algebra/CommutativeMonoid.v:46`, adding `mu ∘ braid ≈ mu`), `Comonoid`
(`Theory/Algebra/Comonoid.v:40`) and `CommutativeComonoid`
(`Theory/Algebra/CommutativeComonoid.v:49`), plus `MonoidObject`
(`Structure/Monoid.v:124`). The op-duality is available but only for the
*plain* notions: `Construction/Opposite/Monoidal.v` transports `BraidedMonoidal`
and `SymmetricMonoidal` to `C^op` and dualizes `Monoid ↔ Comonoid`
(`:192`, `:232`, with the hom versions at `:288`, `:301`), but it never states
`CommutativeMonoid (C^op) x ↔ CommutativeComonoid C x` — the braid clauses
`mu ∘ braid ≈ mu` and `braid ∘ delta ≈ delta` are not related, so the
commutative half of Example 5.70's "equivalently" is missing.

The bimonoid/bialgebra interaction has **no in-tree counterpart at all**:
searches for `bimonoid`, `bialgebra`, `hopf` return comments only. The library
has monoids and comonoids separately, and Frobenius / special-Frobenius
interaction (`Theory/Algebra/Frobenius.v`,
`Theory/Algebra/SpecialCommutativeFrobenius.v`), but never the bialgebra law.

The concrete witness is likewise off-target: `supply_wire_comonoid`
(`Construction/ColouredPROP/Supply/Instance.v:260`) is a genuine
`CommutativeComonoid`, but on a wire of the free supplied coloured prop, not on
the object `1` of a matrix prop, which does not exist. The general per-object
version is `CopyDiscard`'s field `cd_comonoid`
(`Structure/Monoidal/CopyDiscard.v:88`), which *assumes* rather than derives the
structure.

## Work to be done

- In a new `Theory/Algebra/Bimonoid.v`, define `Class Bimonoid (X : C)` in a
  symmetric monoidal category: a `CommutativeMonoid` and a
  `CommutativeComonoid` on the same object, subject to the four interaction
  laws — copying a product equals the middle-interchange of two copies
  (`delta ∘ mu ≈ (mu ⊗ mu) ∘ middle ∘ (delta ⊗ delta)`), the unit/counit
  compatibilities (`epsilon ∘ mu ≈ epsilon ⊗ epsilon`,
  `delta ∘ eta ≈ eta ⊗ eta`) and the bit `epsilon ∘ eta ≈ id_I`. Add
  `BimonoidHom` if the homomorphism notion is cheap, reusing
  `Theory/Algebra/Monoid/Hom.v:34` and `Theory/Algebra/Comonoid/Hom.v:60`.
- Close the duality gap the coverage pass identified: prove
  `CommutativeMonoid (C^op) x ↔ CommutativeComonoid C x` in
  `Construction/Opposite/Monoidal.v`, so Example 5.70's "equivalently" is a
  theorem rather than a slogan, and derive the `Bimonoid`/`Bimonoid (C^op)`
  duality from it.
- In `Instance/Mat/Bimonoid.v`, discharge the two examples at the matrix prop:
  Example 5.68 — `(1, add, zero)` is a `CommutativeMonoid` object in `Mat R`,
  proved by computing the matrices (the associativity, unitality and
  commutativity laws each become an identity of small matrices over the rig);
  Example 5.70 — `(1, copy, discard)` is a `CommutativeComonoid` object, both
  directly and via the op-transport just proved. Then assemble
  `Mat_one_Bimonoid : Bimonoid (1 : Mat R)` by checking the interaction laws.
- Record in the header that these are exactly the equations the presentation of
  §5.4.1 will impose, so the two developments cite one artifact.

In-tree donors: `Theory/Algebra/Monoid.v:44`,
`Theory/Algebra/CommutativeMonoid.v:46`, `Theory/Algebra/Comonoid.v:40`,
`Theory/Algebra/CommutativeComonoid.v:49`, `Construction/Opposite/Monoidal.v`,
`Structure/Monoidal/CopyDiscard.v:88`,
`Construction/ColouredPROP/Supply/Instance.v:260` as a worked comonoid
precedent, the matrix prop of §5.3.3.

## Definition of Done

- [ ] `Bimonoid` defined with the four interaction laws, in a symmetric
      monoidal ambient, stated with `≈`.
- [ ] `CommutativeMonoid (C^op) x ↔ CommutativeComonoid C x` proved, closing
      the commutative half of the op-duality.
- [ ] Example 5.68 and Example 5.70 discharged at the matrix prop, the latter
      both directly and by op-transport.
- [ ] `Mat_one_Bimonoid` assembled.
- [ ] Statement fidelity to the book (§5.4.2, Examples 5.68 and 5.70, against
      Definition 5.65), with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `Bimonoid`, the op-duality and
      `Mat_one_Bimonoid`.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated — the bialgebra law is a genuine
      addition to the algebra spine, which currently records only monoids,
      comonoids and Frobenius.

## Verification

```
coqc -R . Category Theory/Algebra/Bimonoid.v Instance/Mat/Bimonoid.v
#   Print Assumptions Bimonoid.
#   Print Assumptions CommutativeMonoid_op_iff_CommutativeComonoid.
#   Print Assumptions Mat_one_Bimonoid.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the monoid and comonoid axioms are those of Seven Sketches §5.4.2
Definition 5.65 (associativity, two-sided unitality, commutativity via the
symmetry), and the two examples are read off the object `1` of the matrix prop.

## Dependencies

Depends on: 7sketches:5.3.3:def5.50 (the matrix prop carrying the object `1`).

<!-- catalog: {"ids":["7sketches:5.4.2:example5.68","7sketches:5.4.2:example5.70"],"deps":["7sketches:5.3.3:def5.50"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.1: Mat(R) is presented by the signal-flow generators modulo the bimonoid equations"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.1:thm5.60]
deps_item_ids: [7sketches:5.3.3:def5.50, 7sketches:5.3.2:def5.45, 7sketches:5.4.2:example5.68, 7sketches:5.4.1:prop5.56]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.1 (Theorem 5.60 with
its displayed list of equations). Printed p. 170; PDF p. 182. Item ID:
`7sketches:5.4.1:thm5.60`.

## Background

The prop of matrices over a rig is isomorphic to the prop presented by the
signal-flow generators subject to: the comonoid laws for copy and discard, the
monoid laws for addition and zero, the bimonoid interaction between them, and
the scalar laws making each amplifier a bimonoid homomorphism with
`a ; b = ab`, `1 = id`, `0 = discard ; zero`. This is a sound and complete
graphical calculus for linear algebra over a rig. See
[nLab: bimonoid](https://ncatlab.org/nlab/show/bimonoid),
[nLab: generators and relations](https://ncatlab.org/nlab/show/generators+and+relations)
and [nLab: PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

The headline claim is absent outright, because neither side of the isomorphism
exists. There is no rig (see §5.3.1) and no matrix prop (see §5.3.3) — every
`matrix` hit in the tree is a comment — and no signal-flow signature or
equation system (see §5.3.2). Beyond the missing data, three pieces of the
argument have no in-tree counterpart:

- The **bimonoid/bialgebra interaction equations**: searches for
  `bimonoid`/`bialgebra`/`hopf` return comments only; the library has monoids
  and comonoids separately (`Theory/Algebra/Monoid.v:44`,
  `Theory/Algebra/CommutativeComonoid.v:49`) and Frobenius interaction
  (`Theory/Algebra/Frobenius.v`), but never the bialgebra law.
- The **scalar axioms** and the fact that each amplifier is a bimonoid
  homomorphism: the homomorphism notions exist
  (`Theory/Algebra/Monoid/Hom.v:34`, `Theory/Algebra/Comonoid/Hom.v:60`) but
  there are no scalars to apply them to.
- The **pattern itself**: no prop in the tree is presented and then identified
  with a concrete one. The machinery is complete on the presented side —
  `SMT`/`EqSystem` (`Construction/PROP/Presentation.v:113`, `:109`), `TermEqW`
  (`:136`), `PresentedPROP` (`:312`), with soundness `interpW_sound`
  (`Construction/PROP/Presentation/Universal.v:180`), the factorization
  `Presented_factor` (`:340`) and uniqueness `Presented_unique` (`:435`) — and
  the nearest worked equation system is the per-colour supply theory
  `SupplyEqs`/`SupplySMT` (`Construction/ColouredPROP/Supply/Instance.v:134`),
  which is never compared with a concrete prop. `biproduct_addition`
  (`Structure/Semiadditive.v:130`) and `CommutativeMonoid`
  (`Theory/Algebra/CommutativeMonoid.v:46`) are the closest in-tree relatives of
  the monoid half of the equation list.

## Work to be done

- In a new `Instance/SignalFlow/Presentation.v`, define the equation system
  `E_R : EqSystem (SFSig R)` listing exactly the book's equations, grouped and
  named: (i) copy/discard cocommutative comonoid; (ii) add/zero commutative
  monoid; (iii) the four bimonoid interaction laws; (iv) the scalar laws —
  `amp a ; amp b ≈ amp (a·b)`, `amp 1 ≈ id`, `amp 0 ≈ discard ; zero`, and
  amplifier-vs-copy/add/discard/zero commutation (each amplifier a bimonoid
  homomorphism). Assemble `SFSMT R : SMT` and
  `SFPresented R := PresentedPROP (SFSMT R)`.
- **Soundness**: build the valuation of §5.3.4 into the matrix prop, prove each
  equation of `E_R` holds there (`ESound`,
  `Construction/PROP/Presentation/Universal.v:139`), and obtain the induced
  prop functor `SFPresented R ⟶ Mat R` via `PresentedInterp`
  (`Construction/PROP/Presentation/Universal.v:194`) with
  `PresentedInterp_SymmetricStrict` (`:327`).
- **Completeness**: prove the induced functor is faithful, by a normal-form
  argument — every morphism of the presented prop is equal, modulo `E_R`, to a
  three-layer normal form (comonoid layer, scalars, monoid layer), and the
  normal form is determined by its matrix. This is the substantial half of the
  PR; state the normal-form theorem as a separate named artifact so it can be
  cited and reused.
- Conclude `Mat R ≅ SFPresented R` as an isomorphism of props, using fullness
  (§5.4.1) for essential surjectivity on morphisms and faithfulness for
  injectivity. Record both halves as named corollaries: soundness ("if two
  diagrams are related by the equations, they have the same matrix") and
  completeness ("if two diagrams have the same matrix, the equations relate
  them"), since the exercises of §5.4.1 cite them separately.
- Where the equation list overlaps the bimonoid class of §5.4.2, cite that
  class rather than restating the laws.

In-tree donors: `Construction/PROP/Presentation.v`,
`Construction/PROP/Presentation/Universal.v:139`/`:180`/`:194`/`:327`/`:340`/
`:435`, `Construction/ColouredPROP/Supply/Instance.v:134` as the worked
equation-system precedent, the bimonoid class of §5.4.2, the matrix prop of
§5.3.3, the semantics functor of §5.3.4, the fullness result of §5.4.1.

## Definition of Done

- [ ] `E_R` written out with every equation of Theorem 5.60, grouped and named.
- [ ] Soundness: each equation holds in the matrix prop; the induced prop
      functor exists.
- [ ] The three-layer normal-form theorem is proved as a separate named
      artifact.
- [ ] Completeness: the induced functor is faithful.
- [ ] `Mat R ≅ SFPresented R` proved as an isomorphism of props, with soundness
      and completeness recorded as separate corollaries.
- [ ] Statement fidelity to the book (§5.4.1, Theorem 5.60), with the setoid
      `≈` discipline on morphisms; the equations are stated between terms of
      the free prop, never as `=`.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the normal-form theorem, both
      corollaries and the isomorphism.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated, and `docs/INHABITATION.md` amended —
      this is the library's first concrete prop identified with a presented
      one, so the presentation machinery gains its first non-parametric
      witness.

## Verification

```
coqc -R . Category Instance/SignalFlow/Presentation.v
#   Print Assumptions SF_presentation_sound.
#   Print Assumptions SF_normal_form.
#   Print Assumptions SF_presentation_complete.
#   Print Assumptions Mat_iso_SFPresented.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: every equation in the drafted list corresponds to one of the
diagrams displayed in Seven Sketches §5.4.1 Theorem 5.60, with none added and
none omitted, and the conclusion is an isomorphism of props, not merely an
equivalence.

## Dependencies

Depends on: 7sketches:5.3.3:def5.50 (the matrix prop).
Depends on: 7sketches:5.3.2:def5.45 (the signal-flow signature).
Depends on: 7sketches:5.4.2:example5.68 (the bimonoid class and the bimonoid on
the object `1`, whose laws are the equations imposed here).
Depends on: 7sketches:5.4.1:prop5.56 (fullness of the semantics).

<!-- catalog: {"ids":["7sketches:5.4.1:thm5.60"],"deps":["7sketches:5.3.3:def5.50","7sketches:5.3.2:def5.45","7sketches:5.4.2:example5.68","7sketches:5.4.1:prop5.56"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.1: Graphical reasoning with the presentation of Mat(R) — rewriting, alternatives, and a non-derivability argument"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:5.4.1:example5.61, 7sketches:5.4.1:ex5.62, 7sketches:5.4.1:ex5.63]
deps_item_ids: [7sketches:5.4.1:thm5.60]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.1 (Example 5.61 with
its three displayed rewriting steps, Exercise 5.62, Exercise 5.63 with the
displayed pair (5.64)). Printed p. 171; PDF p. 183. Item IDs:
`7sketches:5.4.1:example5.61`, `7sketches:5.4.1:ex5.62`,
`7sketches:5.4.1:ex5.63`.

## Background

Once the graphical calculus is sound and complete, equality of matrices can be
established *and refuted* by diagram rewriting alone: completeness turns
"same matrix" into a chain of equations, and soundness turns "different
matrices" into a non-derivability argument. See
[nLab: generators and relations](https://ncatlab.org/nlab/show/generators+and+relations)
and [Wikipedia: signal-flow graph](https://en.wikipedia.org/wiki/Signal-flow_graph).

## Current state in the library

Absent in every part, since the presentation it exercises does not exist (see
§5.4.1). More specifically, the library has no example anywhere of a *diagram
rewriting chain* — the presented-prop machinery
(`Construction/PROP/Presentation.v`, `Construction/PROP/Presentation/Universal.v`)
is used only for generic theorems and for the Tietze definitional-extension
tests (`Construction/PROP/Tietze.v`), never to derive one concrete diagram from
another; and there is no in-tree instance of using soundness to prove a
*non*-equality.

## Work to be done

- In a new `Instance/SignalFlow/Rewriting.v`, discharge Example 5.61: build the
  two `0 -> 2` diagrams the book displays for the column vector with entries
  `0` and `6` — the copy/amplify/add one and the single amplify-by-`6` one —
  and derive one from the other **using only the presentation's equations**,
  i.e. as an inhabitant of `TermEqW E_R`, following the book's three steps
  (move the addition and copy nodes past each other by the bimonoid law, merge
  the scalars `2` and `3` into `6` by the scalar composition law). Record each
  step as a named lemma so the chain is readable, and check independently that
  both diagrams have the same matrix.
- Discharge Exercise 5.62: for each of the three matrices of the fullness
  exercise (§5.4.1), build a *second*, structurally different diagram with the
  same matrix, and derive the two from each other in `TermEqW E_R`. Note in the
  header that one may also invoke completeness to get the derivation
  abstractly; the exercise's point is the explicit chain, so give the explicit
  chain and use completeness only as a cross-check.
- Discharge Exercise 5.63 part (1): with the rig of naturals, prove the two
  displayed diagrams are **not** related by the presentation. The honest route
  is soundness: exhibit a prop functor (or simply the semantics functor) under
  which the two diagrams take different values, hence no derivation exists.
  State it that way — as a non-derivability result obtained from soundness plus
  a separating interpretation — rather than by attempting a syntactic
  confluence argument.
- Discharge Exercise 5.63 part (2): over the rig `ℕ/3ℕ`, find and verify a
  minimal representation of the right-hand diagram. This needs the modular rig
  as an instance; add `Zmod_Rig n` alongside the other rig instances if it is
  not already there, with its arithmetic by `Nat.modulo`.

In-tree donors: the presentation of §5.4.1, the semantics functor of §5.3.4,
`Construction/PROP/Presentation.v:136` (`TermEqW`'s constructors, which are the
proof steps), `Construction/PROP/Tietze.v:395` as the precedent for reasoning
inside `TermEqW`, the rig instances of §5.3.1.

## Definition of Done

- [ ] Example 5.61's rewriting chain is formalized step by step in `TermEqW`,
      and both diagrams are independently checked to have the same matrix.
- [ ] Exercise 5.62: three second diagrams, each derived from the first by an
      explicit chain.
- [ ] Exercise 5.63 part (1): non-derivability proved from soundness plus a
      separating interpretation.
- [ ] Exercise 5.63 part (2): the modular rig instance and the minimal
      representation, verified.
- [ ] Statement fidelity to the book (§5.4.1, Example 5.61 and Exercises 5.62,
      5.63), with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the rewriting chains and the
      non-derivability result.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index update not expected (worked-example material),
      unless the modular rig instance lands in the rig entry.

## Verification

```
coqc -R . Category Instance/SignalFlow/Rewriting.v
#   Print Assumptions example_5_61_chain.
#   Print Assumptions exercise_5_63_not_derivable.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the rewriting steps use only equations listed in Seven Sketches
§5.4.1 Theorem 5.60 together with the prop axioms, and the non-derivability
argument in Exercise 5.63 does not compute either matrix as its *method*, only
as the separating interpretation soundness allows.

## Dependencies

Depends on: 7sketches:5.4.1:thm5.60 (the presentation being exercised).

<!-- catalog: {"ids":["7sketches:5.4.1:example5.61","7sketches:5.4.1:ex5.62","7sketches:5.4.1:ex5.63"],"deps":["7sketches:5.4.1:thm5.60"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.2: The underlying-set functor Mat(R) → Set and transport of monoid objects"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:5.4.2:ex5.69]
deps_item_ids: [7sketches:5.3.3:def5.50, 7sketches:5.4.2:example5.68]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.2 (Exercise 5.69,
three parts). Printed p. 173; PDF p. 185. Item ID: `7sketches:5.4.2:ex5.69`.

## Background

Sending `n` to `R^n` and a matrix to the induced vector map is a monoidal
functor from matrices to sets, taking the monoidal unit `0` to a one-element
set and the direct sum to the cartesian product; monoidal functors transport
monoid objects, so `R^n` inherits a commutative monoid structure. See
[nLab: monoidal functor](https://ncatlab.org/nlab/show/monoidal+functor) and
[nLab: monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category).

## Current state in the library

Absent on both the specific and the general side. Specifically: the matrix prop
does not exist (see §5.3.3), so neither the functor nor its source does.
Generally — and this is the part worth extracting — the library has **no
monoid-object transport lemma**: searches over `Functor/` for monoid-preservation
(`rg 'Monoid'`, `rg -i 'preserv.*monoid|monoid.*preserv'`) return only the
monoidal-*structure* files (`MonoidalFunctor`, `LaxMonoidalFunctor`,
`StrictMonoidalFunctor`, `BraidedMonoidalFunctor`) plus header prose.
`Theory/Algebra/Monoid/Hom.v` does build `Mon` and `Mon_Forget : Mon ⟶ C`, but
induces no functor `Mon(C) ⟶ Mon(D)` from a monoidal functor `C ⟶ D`. The
vocabulary for part (1) exists; the theorem for part (2) does not.

## Work to be done

- In a new `Functor/Structure/Monoidal/MonoidTransport.v`, prove the general
  lemma the exercise's part (2) is an instance of: a lax monoidal functor
  `F : C ⟶ D` sends a `MonoidObject` in `C` to a `MonoidObject` in `D`
  (`F M`, with multiplication `F mu ∘ lax_ap` and unit `F eta ∘ lax_pure`), and
  a *braided* lax monoidal functor sends a `CommutativeMonoid` to a
  `CommutativeMonoid`. Package it as a functor `Mon C ⟶ Mon D` extending
  `Theory/Algebra/Monoid/Hom.v`'s `Mon`, and state the dual for comonoids by
  op-transport.
- In `Instance/Mat/Underlying.v`, define `U : Mat R ⟶ Sets` with `fobj n := R^n`
  (the `Fin.t n -> carrier R` setoid) and `fmap M` the vector-matrix action,
  and discharge part (1): `U` preserves the monoidal unit (`R^0` is a
  one-element setoid) and the monoidal product (`R^(m+p) ≅ R^m × R^p`), i.e.
  give it a (strong) monoidal-functor structure.
- Discharge part (3): apply the transport lemma to the commutative monoid
  object on `1` of §5.4.2, obtaining the commutative monoid structure on
  `R^1 ≅ carrier R` — and check it is the rig's own addition, which is the
  point of the exercise.
- Record the general remark the exercise itself makes: part (2) works for any
  monoidal functor, not just this `U`; that is why the lemma is stated
  generically and applied, rather than proved inline.

In-tree donors: `Functor/Structure/Monoidal/`,
`Theory/Algebra/Monoid.v:44`, `Theory/Algebra/CommutativeMonoid.v:46`,
`Theory/Algebra/Monoid/Hom.v:34`, `Structure/Monoid.v:124`,
`Instance/Sets.v` (`Sets_Product_Monoidal`, `:283`), the matrix prop of
§5.3.3, the monoid object of §5.4.2.

## Definition of Done

- [ ] The general transport lemma is proved for lax monoidal functors, with the
      braided/commutative variant, and packaged as `Mon C ⟶ Mon D`.
- [ ] `U : Mat R ⟶ Sets` defined, with its monoidal-functor structure (part 1).
- [ ] Part (2) discharged as an instance of the general lemma.
- [ ] Part (3): `R^n` receives the commutative monoid structure, and it is
      identified with the rig's addition at `n = 1`.
- [ ] Statement fidelity to the book (§5.4.2, Exercise 5.69), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom` — in particular the `Sets`-valued
      functor must avoid `funext` (use the setoid hom).
- [ ] `Print Assumptions` reported closed for the transport lemma and `U`.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated — monoid-object transport along a
      monoidal functor is a generally useful addition to the algebra spine.

## Verification

```
coqc -R . Category Functor/Structure/Monoidal/MonoidTransport.v Instance/Mat/Underlying.v
#   Print Assumptions MonoidObject_transport.
#   Print Assumptions Mat_Underlying_Monoidal.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the functor sends `n` to `R^n` and a matrix to the vector action
in the row-vector orientation of §5.3.3, and the transport statement matches
Seven Sketches §5.4.2 Exercise 5.69 part (2).

## Dependencies

Depends on: 7sketches:5.3.3:def5.50 (the matrix prop — source of the functor).
Depends on: 7sketches:5.4.2:example5.68 (the commutative monoid object being
transported).

<!-- catalog: {"ids":["7sketches:5.4.2:ex5.69"],"deps":["7sketches:5.3.3:def5.50","7sketches:5.4.2:example5.68"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.2: Monoidal structures as commutative monoid objects — in Cat and in Preord"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.2:example5.71, 7sketches:5.4.2:example5.72]
deps_item_ids: []
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.2 (Examples 5.71 and
5.72). Printed p. 173; PDF p. 185. Item IDs: `7sketches:5.4.2:example5.71`,
`7sketches:5.4.2:example5.72`.

## Background

A symmetric strict monoidal category is exactly a commutative monoid object in
the cartesian monoidal category of categories, and a symmetric monoidal
preorder is exactly a commutative monoid object in the cartesian monoidal
category of preorders — the "monoidal structure is an internal monoid one level
up" slogan made precise. See
[nLab: Cat](https://ncatlab.org/nlab/show/Cat),
[nLab: monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category)
and [nLab: preorder](https://ncatlab.org/nlab/show/preorder).

## Current state in the library

Neither identification is stated, and there is a same-name trap to avoid.

For Example 5.71: the in-tree correspondence
`StrictPremonoidal_of_Monoid` / `Monoid_of_StrictPremonoidal`
(`Instance/StrictCat/Premonoid.v:136`, `:145`, with the definitional round trips
at `:165`, `:170`) is at the **funny tensor** `□`, not the cartesian `×`, and
its conclusion is strict *pre*monoidal (a binoidal tensor with no interchange
law) — strictly weaker than the book's strict monoidal. The file's own header
(`:21-26`) names the `(Cat, ∏, 1)` statement as the classical fact its
funny-tensor theorem is "the counterpart of", i.e. explicitly as not done.
Concretely missing: `StrictCat` has no cartesian or product monoidal structure
(`Instance/StrictCat/` holds only `Funny.v`, `Terminal.v`, `Premonoid.v`,
`ToCat.v`), while `Cat_Cartesian` (`Instance/Cat/Cartesian.v:39`) lives on
`Cat`, whose hom-setoid is `Functor_Setoid` (`Instance/Cat.v:145`) — equivalence
of functors rather than the strict `Functor_StrictEq_Setoid`
(`Instance/StrictCat.v:59`) — so a monoid object there would deliver a
pseudomonoid, not a strict monoidal category. The commutative clause is not
addressed on either side.

For Example 5.72: there is no category of preorders at all. `rg -i 'monoidal
preorder|MonoidalPreorder'` returns nothing; `Instance/Proset.v:34` and
`Instance/Poset.v` build the category *of one* preorder/poset, not the category
of all of them; `Construction/Enriched/Two.v:60` (`TwoPreorder`) and `:175`
(`MonotoneMap`) exist but are never assembled into a category;
`Instance/Two/Monoidal.v:105` (`Two_Monoidal`) is the cartesian structure on the
two-element order.

## Work to be done

- In a new `Instance/StrictCat/Cartesian.v`, give `StrictCat` its cartesian
  (product) monoidal structure — the product of categories with the strict
  hom-setoid — and check it is genuinely cartesian for that setoid. Then in
  `Instance/StrictCat/MonoidObject.v` prove Example 5.71 in both directions:
  a `CommutativeMonoid` object in `(StrictCat, ×, 1)` yields a symmetric strict
  monoidal category, and conversely; with the round trips. Disclose in the
  header why the statement is made on `StrictCat` and not on `Cat` (on `Cat`
  the same data give a pseudomonoid, which is the honest weaker statement, and
  is worth recording as a remark).
- In a new `Instance/Preord.v`, build the category of preorders and monotone
  maps, reusing `Construction/Enriched/Two.v:60`/`:175` and
  `Instance/Proset.v:33` for the objects and morphisms, and give it its
  cartesian monoidal structure. Then prove Example 5.72 in both directions:
  a `CommutativeMonoid` object in `(Preord, ×, 1)` is exactly a symmetric
  monoidal preorder in the sense of the Chapter 2 class, and conversely.
- Because both examples are the same statement at two bases, factor what can be
  factored: state once that a `CommutativeMonoid` object at a cartesian tensor
  is a "monoid internal to" structure with the projection-based
  multiplication, and instantiate twice.

In-tree donors: `Instance/StrictCat.v:59`, `Instance/StrictCat/Premonoid.v`,
`Instance/Cat/Cartesian.v:39`, `Structure/Monoidal/Internal/Product.v`
(cartesian-to-monoidal), `Theory/Algebra/CommutativeMonoid.v:46`,
`Structure/Monoid.v:124`, `Construction/Enriched/Two.v:60`/`:175`,
`Instance/Proset.v:33`.

## Definition of Done

- [ ] `StrictCat` carries a cartesian monoidal structure.
- [ ] Example 5.71 proved in both directions, with round trips, on `StrictCat`;
      the `Cat`/pseudomonoid caveat recorded as a remark.
- [ ] `Preord`, the category of preorders and monotone maps, exists with its
      cartesian monoidal structure.
- [ ] Example 5.72 proved in both directions.
- [ ] The shared "commutative monoid object at a cartesian tensor" statement is
      factored out rather than duplicated.
- [ ] Statement fidelity to the book (§5.4.2, Examples 5.71 and 5.72), with the
      setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for both identifications.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated — `Instance/StrictCat/Premonoid.v`'s
      entry currently advertises the funny-tensor theorem as the only such
      correspondence, and the category of preorders is new.

## Verification

```
coqc -R . Category Instance/StrictCat/MonoidObject.v Instance/Preord.v
#   Print Assumptions SymStrictMonoidal_iff_CommutativeMonoid_in_StrictCat.
#   Print Assumptions SymMonoidalPreorder_iff_CommutativeMonoid_in_Preord.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the ambient tensor is the *cartesian* product in both cases (not
the funny tensor), and the monoid object is commutative — matching Seven
Sketches §5.4.2 Examples 5.71 and 5.72.

## Dependencies

Depends on: #771 (symmetric monoidal preorders — the class Example 5.72
identifies with).
Depends on: #786 (the category of preorders — the ambient of Example 5.72).
Depends on: #520 (coherence for symmetric monoidal categories, and
product/coproduct as symmetric tensor — the cartesian-tensor vocabulary).

<!-- catalog: {"ids":["7sketches:5.4.2:example5.71","7sketches:5.4.2:example5.72"],"deps":["#771","#786","#520"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.2: The tensor product of commutative monoids, and rigs as monoid objects in (CMon, ⊗, ℕ)"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.2:example5.73]
deps_item_ids: [7sketches:5.3.1:def5.36]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.2 (Example 5.73).
Printed p. 173; PDF p. 185. Item ID: `7sketches:5.4.2:example5.73`.

## Background

Commutative monoids carry a tensor product classifying bilinear maps, with the
naturals as unit; a monoid object for that tensor is exactly a rig — the
semiring analogue of "a ring is a monoid in abelian groups". See
[nLab: commutative monoid](https://ncatlab.org/nlab/show/commutative+monoid),
[nLab: tensor product](https://ncatlab.org/nlab/show/tensor+product) and
[nLab: rig](https://ncatlab.org/nlab/show/rig).

## Current state in the library

Both the ambient and the conclusion are missing. There is no rig structure
anywhere (`rg 'Class Rig|Record Rig|Semiring'` returns no structural hits; the
two `Theory/Algebra.v` comment lines are about rig *categories*, a different
notion). And `Instance/CMon.v` — which defines `CMonObject` (`:32`), `CMonHom`,
the category `CMon` (`:141`) and `CMon_Forget` — declares **no** `Monoidal`
instance; `Instance/CMon/` contains only `Biproduct.v`, i.e. the
cartesian/biproduct structure (`CMon_Preadditive`,
`Instance/CMon/Biproduct.v:573`), not the tensor the example's ambient
requires.

## Work to be done

- In a new `Instance/CMon/Tensor.v`, construct the tensor product of
  commutative monoids over setoids: `A ⊗ B` as the free commutative monoid on
  `A × B` quotiented by bilinearity, presented in the library's idiom as an
  inductive setoid quotient (the pattern of `Instance/Sets/Coend.v`, which
  builds an inductive setoid quotient by exactly the relations it needs, is the
  right precedent and keeps the construction funext-free).
- Prove the universal property — `CMonHom (A ⊗ B) C` is in bijection with the
  bilinear maps `A × B -> C` — and derive from it the unitors (with `ℕ`, the
  free commutative monoid on one generator, as unit), the associator and the
  braid; assemble `CMon_Monoidal`, `CMon_Braided`, `CMon_Symmetric`.
- In `Theory/Algebra/Rig/MonoidObject.v`, prove Example 5.73 in both
  directions: a `MonoidObject` in `(CMon, ⊗, ℕ)` is exactly a `Rig`, and
  conversely; with the round trips. Multiplication being a monoid map out of
  the tensor is precisely two-sided distributivity plus annihilation, so this
  is the clean explanation of why the rig class has those two clauses.
- Record the corollary the identification makes cheap: a commutative rig is a
  *commutative* monoid object for the same tensor.

In-tree donors: `Instance/CMon.v:32`/`:141`, `Instance/CMon/Biproduct.v`,
`Instance/Sets/Coend.v` (inductive setoid quotient),
`Theory/Algebra/CommutativeMonoid.v:46`, `Structure/Monoid.v:124`,
the rig class of §5.3.1.

## Definition of Done

- [ ] `A ⊗ B` constructed for commutative monoids, with its universal property
      for bilinear maps proved.
- [ ] `CMon_Monoidal` / `Braided` / `Symmetric` with `ℕ` as unit.
- [ ] Example 5.73 proved in both directions with round trips.
- [ ] The commutative-rig corollary recorded.
- [ ] Statement fidelity to the book (§5.4.2, Example 5.73), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom` — in particular the quotient must
      be an inductive setoid quotient, not a `funext`/quotient-type axiom.
- [ ] `Print Assumptions` reported closed for the tensor, its universal
      property, and both directions of the identification.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated — `Instance/CMon.v`'s entry currently
      advertises only the biproduct/semiadditive role.

## Verification

```
coqc -R . Category Instance/CMon/Tensor.v Theory/Algebra/Rig/MonoidObject.v
#   Print Assumptions CMon_Symmetric.
#   Print Assumptions Rig_iff_MonoidObject_in_CMon.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the ambient is `(CMon, ⊗, ℕ)` with the *tensor* product, not the
cartesian product, and the conclusion is a rig in the sense of Seven Sketches
§5.3.1 Definition 5.36.

## Dependencies

Depends on: 7sketches:5.3.1:def5.36 (the rig class being characterised).

<!-- catalog: {"ids":["7sketches:5.4.2:example5.73"],"deps":["7sketches:5.3.1:def5.36"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.2: The prop presenting the theory of monoids, and models in an arbitrary monoidal category"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.2:remark5.74]
deps_item_ids: [7sketches:5.2.1:def5.11]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.2 (Remark 5.74).
Printed p. 173; PDF p. 185. Item ID: `7sketches:5.4.2:remark5.74`.

## Background

The prop presented by a multiplication `2 -> 1` and a unit `0 -> 1` subject to
the monoid equations deserves to be called *the theory of monoids*: its models
in a monoidal category — strict monoidal functors out of it — are exactly the
monoid objects there. This is the germ of Lawvere's algebraic theories. See
[nLab: PROP](https://ncatlab.org/nlab/show/PROP),
[nLab: monoid in a monoidal category](https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category)
and [nLab: Lawvere theory](https://ncatlab.org/nlab/show/Lawvere+theory).

## Current state in the library

Both sides of the claimed correspondence exist separately, but the
correspondence is not stated, and the in-tree universal property is scoped too
narrowly to state it.

- **The theory is never instantiated.** The only prop signatures in tree are
  `Empty_Sig`, `Single_Sig` and `Sum_Sig`
  (`Construction/PROP/Signature.v:58`, `:68`, `:79`), and no concrete `SMT`
  exists beyond `Construction/PROP/Tietze.v`'s generic extension machinery. So
  there is no signature with a multiplication and a unit, no equation system
  carrying the monoid laws, and no theorem relating its models to
  `MonoidObject` — even though the other side is fully present
  (`Theory/Algebra/Monoid.v:44`, `Structure/Monoid.v:124`).
- **The universal property targets only props.** Both
  `Construction/PROP/Universal.v` and
  `Construction/PROP/Presentation/Universal.v` open with `Context (P : PROP)`
  plus `HomEqProp P` and `ObjDecEq P` side conditions, and `Class PROP`
  (`Construction/PROP.v:68`) demands a category whose objects are named by ℕ
  carrying *both* a strict and a symmetric monoidal structure with a
  propositional coherence between them. The remark quantifies over an arbitrary
  monoidal category and asks only for strict *monoidal* (not symmetric)
  functors.
- **The model category in tree is the wrong one.** `Alg`
  (`Construction/PROP/Algebra.v:234`) is the category of models of a bare
  *signature* (`obj := Valuation P S`), with the theory's equations not
  imposed.
- The Lawvere sibling the remark forward-references exists
  (`Theory/Lawvere.v`, `Theory/Lawvere/Model.v:50` `Model`, `:77` `Models`),
  again with no monoid theory instantiated.

## Work to be done

- In a new `Construction/PROP/Theory/Monoid.v`, build the theory: the signature
  with one generator `2 -> 1` and one `0 -> 1`, the equation system carrying
  associativity and the two unit laws, and `MonoidTheory := PresentedPROP …`.
- Extend the universal property to the targets the remark needs. Concretely,
  generalize the interpretation machinery so that a valuation into an arbitrary
  (symmetric, for the braid to be interpretable) monoidal category `C` together
  with a chosen object `X` induces a strict monoidal functor
  `MonoidTheory ⟶ C` sending `⟦n⟧` to `X^{⊗n}`, with uniqueness. This is the
  reusable increment: today `Context (P : PROP)` forces the target to name its
  objects by ℕ, which an arbitrary `C` does not. Keep the existing
  PROP-targeted statements intact and derive them from the general one, or
  state the general one alongside with a bridge lemma — either is acceptable,
  but the PROP-only scope must stop being the only form available.
- Prove the remark: for a symmetric monoidal `C`, the monoid objects in `C`
  correspond to strict monoidal functors `MonoidTheory ⟶ C`, as a bijection of
  setoids (both directions plus round trips). Disclose the hypothesis the book
  suppresses: in a prop the symmetry is always present, so the correspondence
  as stated lands on monoid objects in a *symmetric* ambient; note the relation
  to the plain-monoidal version of the same statement, and to the commutative
  variant obtained by adding the commutativity equation.
- Add the Lawvere pointer the remark makes, linking to `Theory/Lawvere.v` and
  `Theory/Lawvere/Model.v:77`, and — if cheap — the corresponding model-category
  statement, so `Alg`'s equation-free scope is no longer the only option.

In-tree donors: `Construction/PROP/Presentation.v:109`/`:113`/`:312`,
`Construction/PROP/Presentation/Universal.v:139`/`:194`/`:340`/`:435`,
`Construction/PROP/Universal.v:174`/`:603`,
`Construction/PROP/Algebra.v:234`, `Theory/Algebra/Monoid.v:44`,
`Structure/Monoid.v:124`, `Theory/Lawvere/Model.v:50`/`:77`.

## Definition of Done

- [ ] `MonoidTheory` built as a presented prop with the multiplication, the
      unit and the three equations.
- [ ] The interpretation machinery is generalized to a non-PROP monoidal
      target, with existence and uniqueness, and the existing PROP-scoped
      statements derived from or bridged to it.
- [ ] The correspondence "monoid objects in `C` ↔ strict monoidal functors
      `MonoidTheory ⟶ C`" proved as a bijection of setoids, with round trips.
- [ ] The symmetric-ambient hypothesis the book suppresses is disclosed in the
      header, together with the commutative variant.
- [ ] The Lawvere-theory pointer recorded.
- [ ] Statement fidelity to the book (§5.4.2, Remark 5.74), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for `MonoidTheory`, the generalized
      universal property, and the correspondence.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `CLAUDE.md` Key Files index updated (the PROP entry gains its first
      concrete algebraic theory, and the universal property's scope changes).
- [ ] `make todo` adds no new hits.

## Verification

```
coqc -R . Category Construction/PROP/Theory/Monoid.v
#   Print Assumptions MonoidTheory.
#   Print Assumptions MonoidObject_iff_StrictMonoidalFunctor_from_MonoidTheory.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the presented theory has exactly the two generators and the three
equations Seven Sketches §5.4.2 Remark 5.74 names, and the correspondence is
with *strict monoidal* functors.

## Dependencies

Depends on: #512 (the simplicial category as the free strict monoidal category
on a monoid — the plain-monoidal statement of the same correspondence; this
issue is its symmetric/presented-prop counterpart and additionally requires the
interpretation machinery to accept a non-prop target).
Depends on: 7sketches:5.2.1:def5.11 (prop functors).

<!-- catalog: {"ids":["7sketches:5.4.2:remark5.74"],"deps":["#512","7sketches:5.2.1:def5.11"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.3: Rel_R, the prop of relations over a rig"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.3:def5.79, 7sketches:5.4.3:ex5.80]
deps_item_ids: [7sketches:5.3.1:def5.36, 7sketches:5.2.1:def5.2, 7sketches:5.3.3:def5.50]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.3 (Definition 5.79
and Exercise 5.80, with the composition rule displayed as (5.78)). Printed
p. 175; PDF p. 187. Item IDs: `7sketches:5.4.3:def5.79`,
`7sketches:5.4.3:ex5.80`.

## Background

For a rig `R`, the prop of `R`-relations has the natural numbers as objects and
arbitrary subsets of `R^m × R^n` as morphisms, composed relationally; it
contains the matrices as the sub-prop of graphs of linear maps, and is the home
of signal-flow semantics once feedback is allowed. See
[nLab: Rel](https://ncatlab.org/nlab/show/Rel) and
[nLab: PROP](https://ncatlab.org/nlab/show/PROP).

## Current state in the library

The *underlying category* is present and axiom-free, but nothing of the prop
packaging is. `Rel` (`Instance/Rel.v:45`) has `obj := @obj Coq`,
`hom A B := A ~> Ensemble B`, hom-equivalence pointwise `<->`, `id := Singleton`
and composition by the existential witness — the book's composition rule (5.78)
verbatim, up to the diagrammatic-order convention spelled out at
`Instance/Rel.v:33-35`. Missing for `Rel_R`:

1. a monoidal product on `Rel` — the only candidate, `Rel_Cartesian`, sits
   inside the comment block that opens at `Instance/Rel.v:96` and closes at
   `:157`, and no `@Monoidal Rel` exists anywhere;
2. hence no symmetric or strict structure, and no `PROP` instance (the four
   `PROP` instances in tree are `FreePROP`, `PresentedPROP`, `Lawvere_PROP`,
   `RepeatPROP`);
3. the object correspondence `n ↦ R^n` with the strictness equalities;
4. any rig at all (see §5.3.1), hence no `R`-indexing;
5. the identification of the matrices as a sub-prop — only the generic graph
   embedding of Coq functions exists (`Relation_Functor`, `Instance/Rel.v:167`).

Exercise 5.80's monoidal product cannot even be typed today.

## Work to be done

- In a new `Instance/Rel/Rig.v`, define `RelR R`: `obj := nat`,
  `hom m n := R^m -> R^n -> Type` (or `Ensemble`-style, with a hom-setoid of
  pointwise `iffT` so the morphisms are proof-irrelevant subsets), identity the
  diagonal, composition the book's existential-witness rule.
- Discharge Exercise 5.80 by defining the monoidal product explicitly in set
  notation, as the exercise asks: for `B ⊆ R^m × R^n` and `C ⊆ R^p × R^q`,
  `B + C ⊆ R^(m+p) × R^(n+q)` is the set of pairs whose left/right halves lie
  in `B` and `C` respectively, using the splitting `R^(m+p) ≅ R^m × R^p`. Prove
  it is a bifunctor and that it satisfies the symmetric strict monoidal axioms
  with the swap relation as braid.
- Assemble `RelR_PROP : PROP` with the strict refinement of §5.2.1.
- Prove the containment the definition asserts: the graph map
  `Mat R ⟶ RelR R`, `M ↦ {(x, x·M)}`, is a faithful prop functor, and its image
  is exactly the graphs of the linear maps; relate it to the generic
  `Relation_Functor` (`Instance/Rel.v:167`) by a commuting square so the two
  developments agree.
- Where the ambient `Rel` is touched, note in its header that the skeletal
  rig-indexed variant lives in the new file.

In-tree donors: `Instance/Rel.v:45`/`:167`, the rig class of §5.3.1, the matrix
prop of §5.3.3, `Instance/FinSet.v` (splitting idioms),
`Structure/Monoidal/Strict.v:52`, `Construction/PROP.v:68`.

## Definition of Done

- [ ] `RelR R : Category` with the book's composition and diagonal identity,
      hom-setoid pointwise bi-implication.
- [ ] The monoidal product of Exercise 5.80 defined explicitly and proved a
      symmetric strict monoidal structure.
- [ ] `RelR_PROP : PROP` with the strict refinement of §5.2.1.
- [ ] The faithful prop functor from matrices, with its image characterised as
      the graphs of linear maps.
- [ ] Statement fidelity to the book (§5.4.3, Definition 5.79 and Exercise
      5.80), with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom` — in particular no
      propositional-extensionality or `funext` for equality of subsets.
- [ ] `Print Assumptions` reported closed for `RelR_PROP` and the matrix
      embedding.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated (`Instance/Rel.v`'s entry currently
      advertises a bare category).

## Verification

```
coqc -R . Category Instance/Rel/Rig.v
#   Print Assumptions RelR_PROP.
#   Print Assumptions Mat_to_RelR_Faithful.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: composition is the book's displayed rule (5.78) and the monoidal
product is the one Exercise 5.80 asks to be written out — matching Seven
Sketches §5.4.3 Definition 5.79.

## Dependencies

Depends on: #262 (Rel, converse relations, and the graph embedding — the
ambient relational development).
Depends on: 7sketches:5.3.1:def5.36 (the rig class).
Depends on: 7sketches:5.2.1:def5.2 (the strict-prop refinement).
Depends on: 7sketches:5.3.3:def5.50 (the matrix prop embedded as a sub-prop).

<!-- catalog: {"ids":["7sketches:5.4.3:def5.79","7sketches:5.4.3:ex5.80"],"deps":["#262","7sketches:5.3.1:def5.36","7sketches:5.2.1:def5.2","7sketches:5.3.3:def5.50"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.3: Behaviors of signal flow graphs, mirrored generators, and the prop SFG_R⁺"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.3:def-behavior, 7sketches:5.4.3:def-transposed-relation, 7sketches:5.4.3:ex5.77, 7sketches:5.4.3:def-sfg-plus]
deps_item_ids: [7sketches:5.3.2:def5.45, 7sketches:5.3.4:thm5.53, 7sketches:5.4.3:def5.79, 7sketches:5.2.1:def5.11]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.3 (the behavior
definition carried by the display (5.75), the transposed-relation definition
carried by (5.76), Exercise 5.77, and the definition of the non-simplified
signal-flow prop carried by (5.81)). Printed pp. 174–175; PDF pp. 186–187.
Item IDs: `7sketches:5.4.3:def-behavior`,
`7sketches:5.4.3:def-transposed-relation`, `7sketches:5.4.3:ex5.77`,
`7sketches:5.4.3:def-sfg-plus`.

## Background

The behavior of a signal flow graph is the input/output relation — the graph of
the linear map its matrix determines. Reversing a diagram left-to-right
exchanges inputs and outputs, and its behavior is the converse relation; adding
the mirrored generators to the signature gives the prop of non-simplified
signal flow graphs, whose behavior functor lands in relations rather than
matrices. See [nLab: Rel](https://ncatlab.org/nlab/show/Rel) and
[Wikipedia: signal-flow graph](https://en.wikipedia.org/wiki/Signal-flow_graph).

## Current state in the library

What survives is exactly the generic graph-of-a-function-as-a-relation functor:
`Relation_Functor` (`Instance/Rel.v:167`) is identity on objects with
`fmap f = fun x y => In (Singleton (f x)) y`, so the definitional core —
"the behavior of a map is its graph, a relation, and this assignment is
functorial" — is present, in full generality over Coq types. Everything the
item actually needs is missing:

- no rig, no matrix prop, hence no matrix `S(g)` for the behavior to be the
  graph of (see §5.3.1, §5.3.3);
- no signal flow graphs at all (only a bibliographic mention at
  `Construction/ColouredPROP.v:34`);
- no converse of a relation. `Instance/Rel.v:36-41` describes the converse as
  an involution witnessing `Rel ≅ Rel^op` and then states that "none of that
  extra structure is built here"; every other `transpos*` hit in the tree is
  adjunction-transpose prose;
- no mirror-image operation on a signature: nothing like
  `Op_Sig S := fun m n => S n m` exists (searches for `Op_Sig`, `Sig_op`,
  `Flip_Sig` return nothing), so the disjoint union of a signature with its
  mirror cannot be written, although `Sum_Sig`
  (`Construction/PROP/Signature.v:79`) would supply the `⊔` once the mirror
  existed;
- no behavior/black-box functor landing in relations:
  `Construction/Cospan/BlackBox.v` discusses such a functor only in prose and
  builds solely `forget_decoration`.
- Exercise 5.77's two computations are therefore unposable; note also that
  `Rel` carries no copy/discard or comonoid structure with which to state them
  (the `Rel_Cartesian`/`Rel_Cocartesian`/`Rel_Closed` block is commented out,
  `Instance/Rel.v:96-157`).

Only the general prop machinery is at full strength: `FreePROP`
(`Construction/PROP/Instance.v:82`), `InterpF`
(`Construction/PROP/Universal.v:174`) and `interp_unique` (`:603`), plus
`interp_copair_inl` (`Construction/PROP/Tietze.v:338`) for interpreting a
signature sum — so "the universal property specifies the behavior of every
non-simplified signal flow graph" is available the moment the data exist.

## Work to be done

- Add the converse of a relation to `Instance/Rel.v` (or a sibling file):
  `Rel_converse : Rel ≅ Rel^op` as the identity-on-objects involution, with
  `converse (converse R) ≈ R` and `converse (R ∘ S) ≈ converse S ∘ converse R`.
  Do the same for the rig-indexed relations of §5.4.3.
- Add the generic mirror of a signature in
  `Construction/PROP/Signature.v`: `Op_Sig S := fun m n => S n m`, with the
  involution lemma, so `Sum_Sig (SFSig R) (Op_Sig (SFSig R))` is expressible.
- In a new `Instance/SignalFlow/Behavior.v`:
  - define the behavior of a simplified signal flow graph as the graph of its
    matrix, `B(g) := {(x, x·S(g))} ⊆ R^m × R^n`, and prove it is the composite
    of the semantics functor with the matrix-to-relation embedding of §5.4.3 —
    which is what makes it functorial, and is the honest way to state the
    book's motivating check that the behavior of a composite is the relational
    composite of the behaviors;
  - define the mirror of a generator and the transposed relation
    `B(g^op) := converse (B g)`, i.e. the definition carried by (5.76);
  - define `SFGplus R := FreePROP (Sum_Sig (SFSig R) (Op_Sig (SFSig R)))`, and
    obtain the behavior prop functor `SFGplus R ⟶ RelR R` by `InterpF` on the
    copaired valuation (`interp_copair_inl`,
    `Construction/PROP/Tietze.v:338`, is the tool for the two halves), with
    uniqueness from `interp_unique`;
  - prove that the behavior functor restricted along the inclusion
    `SFG R ↪ SFGplus R` agrees with the composite defined first — the
    consistency statement without which the two definitions could drift.
- Discharge Exercise 5.77 as two computing lemmas: the behavior of the reversed
  addition icon (a `1 -> 2` morphism, the relation `{(x, (y,z)) : y + z = x}`)
  and of the reversed copy icon (a `2 -> 1` morphism, the relation
  `{((x,x), x)}`), each stated in the book's set-builder form and proved from
  the transposed-relation definition.

In-tree donors: `Instance/Rel.v:45`/`:167`,
`Construction/PROP/Signature.v:79`, `Construction/PROP/Instance.v:82`,
`Construction/PROP/Universal.v:174`/`:603`,
`Construction/PROP/Tietze.v:338`, the signal-flow signature of §5.3.2, the
semantics functor of §5.3.4, the relations prop of §5.4.3.

## Definition of Done

- [ ] The converse of a relation is built, with the involution and
      contravariance laws, on both `Rel` and the rig-indexed relations.
- [ ] `Op_Sig` added generically, with its involution lemma.
- [ ] The behavior of a simplified signal flow graph is defined and proved to
      be the composite of the semantics with the graph embedding.
- [ ] `SFGplus R` defined, and the behavior prop functor into relations built
      via the free-prop universal property, with uniqueness.
- [ ] The restriction/agreement statement between the two behavior definitions.
- [ ] Exercise 5.77's two behaviors computed, in the book's set-builder form.
- [ ] Statement fidelity to the book (§5.4.3, the displays (5.75), (5.76),
      (5.81) and Exercise 5.77), with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the converse, the behavior
      functor and the Exercise 5.77 computations.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated, and the "not built here" note at
      `Instance/Rel.v:36-41` amended once the converse exists.

## Verification

```
coqc -R . Category Instance/SignalFlow/Behavior.v
#   Print Assumptions Rel_converse.
#   Print Assumptions SFGplus_behavior.
#   Print Assumptions exercise_5_77.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the behavior is the graph of the matrix as in the display (5.75),
the mirrored behavior is the converse as in (5.76), and the non-simplified prop
is the free prop on the signature together with its mirror as in (5.81) —
matching Seven Sketches §5.4.3.

## Dependencies

Depends on: #262 (Rel, converse relations, and the graph embedding — the
converse operation this consumes).
Depends on: 7sketches:5.3.2:def5.45 (the signal-flow signature being mirrored).
Depends on: 7sketches:5.3.4:thm5.53 (the matrix semantics whose graph the
behavior is).
Depends on: 7sketches:5.4.3:def5.79 (the relations prop, the target).
Depends on: 7sketches:5.2.1:def5.11 (prop functors).

<!-- catalog: {"ids":["7sketches:5.4.3:def-behavior","7sketches:5.4.3:def-transposed-relation","7sketches:5.4.3:ex5.77","7sketches:5.4.3:def-sfg-plus"],"deps":["#262","7sketches:5.3.2:def5.45","7sketches:5.3.4:thm5.53","7sketches:5.4.3:def5.79","7sketches:5.2.1:def5.11"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.3: Behaviors of mixed signal flow graphs — solution sets, joint images, kernels and linearity"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:5.4.3:ex5.82, 7sketches:5.4.3:ex5.83, 7sketches:5.4.3:ex5.84]
deps_item_ids: [7sketches:5.4.3:def-sfg-plus, 7sketches:5.3.4:thm5.53]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.3 (Exercises 5.82,
5.83 and 5.84). Printed p. 176; PDF p. 188. Item IDs:
`7sketches:5.4.3:ex5.82`, `7sketches:5.4.3:ex5.83`, `7sketches:5.4.3:ex5.84`.

## Background

Composing a diagram forwards with a mirrored diagram computes the solution set
of a linear equation; the dual order computes the joint image; capping outputs
with reversed zeros gives the kernel and capping inputs with reversed discards
gives the image. Behaviors are always linear subspaces. See
[Wikipedia: kernel (linear algebra)](https://en.wikipedia.org/wiki/Kernel_(linear_algebra))
and [Wikipedia: linear subspace](https://en.wikipedia.org/wiki/Linear_subspace).

## Current state in the library

Absent in every part, and blocked at the root: there are no signal flow graphs,
no rig, no matrix prop and no behavior functor (whole-tree searches for
signal-flow vocabulary return only header prose in five files; searches for
`LinRel`, "linear relation", `Rel_R` return nothing). No kernel or image of a
matrix exists — the in-tree `Structure/Kernel.v` is the categorical
kernel/cokernel of the abelian spine, over a zero object, not the kernel of a
matrix over a field — and no statement anywhere says a behavior is closed under
addition and scaling.

## Work to be done

- In a new `Instance/SignalFlow/Solutions.v`, working over the non-simplified
  signal-flow prop of §5.4.3:
  - **Exercise 5.82**: for `g : m -> n` and `h : l -> n`, prove that the
    behavior of `g` followed by the mirror of `h` is
    `{(x, y) : x·S(g) ≈ y·S(h)}` — the solution set of the linear equation
    between the two matrices. The proof is by unfolding relational composition
    against the graph and converse-graph descriptions.
  - **Exercise 5.83**: for `g : m -> n` and `h : m -> p`, prove that the
    behavior of the mirror of `g` followed by `h` is
    `{(x·S(g), x·S(h)) : x ∈ R^m}` — the joint image.
  - **Exercise 5.84** parts (1) and (2): over a field, post-composing with
    reversed zeros on every output yields the kernel of the matrix, and
    pre-composing with reversed discards on every input yields the image; state
    both as equalities of relations (subsets of `R^m × R^0` and `R^0 × R^n`
    respectively, i.e. as subsets of `R^m` and `R^n` after the unit
    isomorphism).
  - **Exercise 5.84** part (3): for *any* signal flow graph the behavior is a
    linear subspace — closed under addition and under scalar multiplication.
    Prove this for the whole non-simplified prop by induction on the generators
    (each generator's behavior is linear, and both relational composition and
    the monoidal product preserve linearity), which is the statement Exercise
    5.85 then needs.
- Note precisely where the field hypothesis of parts (1)–(2) is used and where
  a rig suffices: linearity in part (3) holds over any rig; the kernel/image
  reading is the one that wants inverses. Record that split in the header
  rather than assuming a field throughout.

In-tree donors: the behavior functor and converse of §5.4.3, the matrix prop of
§5.3.3, the rig class of §5.3.1, `Instance/Rel.v:45` (relational composition).

## Definition of Done

- [ ] Exercises 5.82 and 5.83 proved as equalities of relations, in the book's
      set-builder form.
- [ ] Exercise 5.84 parts (1) and (2) proved over a field, with the field
      hypothesis used only where needed.
- [ ] Exercise 5.84 part (3) proved for every morphism of the non-simplified
      prop, by induction on the generators, over an arbitrary rig.
- [ ] The rig-versus-field split recorded in the header.
- [ ] Statement fidelity to the book (§5.4.3, Exercises 5.82, 5.83, 5.84), with
      the setoid `≈` discipline on morphisms and on rig elements.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for each of the four results.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index update not expected unless the linearity
      result is cited by the sub-prop of linear relations.

## Verification

```
coqc -R . Category Instance/SignalFlow/Solutions.v
#   Print Assumptions exercise_5_82.
#   Print Assumptions exercise_5_83.
#   Print Assumptions exercise_5_84_kernel.
#   Print Assumptions behavior_is_linear.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: each behavior is computed from the definitions of §5.4.3 rather
than assumed, and the four statements match Seven Sketches §5.4.3 Exercises
5.82–5.84.

## Dependencies

Depends on: 7sketches:5.4.3:def-sfg-plus (the non-simplified prop and its
behavior functor).
Depends on: 7sketches:5.3.4:thm5.53 (the matrix semantics appearing in every
statement).

<!-- catalog: {"ids":["7sketches:5.4.3:ex5.82","7sketches:5.4.3:ex5.83","7sketches:5.4.3:ex5.84"],"deps":["7sketches:5.4.3:def-sfg-plus","7sketches:5.3.4:thm5.53"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.3: LinRel_R — linear relations form a sub-prop of Rel_R"
labels: [book:seven-sketches, kind:exercise, coverage-gap]
projects: [6]
covers: [7sketches:5.4.3:ex5.85]
deps_item_ids: [7sketches:5.4.3:def5.79, 7sketches:5.4.3:ex5.84]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.3 (Exercise 5.85 and
the surrounding prose, which states the converse and the existence of a sound
and complete presentation without proof). Printed p. 177; PDF p. 189. Item ID:
`7sketches:5.4.3:ex5.85`.

## Background

A relation is linear when it is closed under scalar multiplication and under
addition; the linear relations form a sub-prop of all relations, and — over a
field — they are exactly the behaviors of signal flow graphs. See
[Wikipedia: linear subspace](https://en.wikipedia.org/wiki/Linear_subspace) and
[nLab: Rel](https://ncatlab.org/nlab/show/Rel).

## Current state in the library

Absent. `LinRel`, "linear relation" and `Rel_R` return no hits anywhere; the
ambient prop of relations over a rig does not exist (see §5.4.3), and no
closure property of any relation class is stated in the tree. The library has
wide-subcategory machinery (`Construction/Subcategory.v`) that is the right
donor once the ambient exists, but it is never used on relations.

## Work to be done

- In a new `Instance/Rel/Linear.v`, define linearity for a morphism of the
  rig-indexed relations prop: closed under scaling (`(x,y) ∈ B` and `r ∈ R`
  imply `(r·x, r·y) ∈ B`) and under addition (`(x,y), (x',y') ∈ B` imply
  `(x+x', y+y') ∈ B`). Add the zero condition if the intended notion is
  "sub-semimodule" — record explicitly which of the two the file adopts and why
  (the book states only the two closure clauses).
- Discharge the exercise's key step: the relational composite of two linear
  relations is linear. Then complete the sub-prop: the identity/diagonal is
  linear, the braid is linear, and the monoidal product of two linear relations
  is linear; assemble `LinRel R` as a wide sub-prop of the relations prop via
  `Construction/Subcategory.v`, with the inclusion a faithful prop functor.
- Record the two claims the surrounding prose makes without proof, as scoped
  statements rather than silently omitting them:
  - the converse of the kernel/image results of §5.4.3 — over a field, every
    linear relation is the behavior of some signal flow graph. If proving it is
    out of scope for this PR, state it as a named `Definition`-level conjecture
    in the header with a pointer, and file it separately; do not leave it
    unmentioned.
  - the existence of a sound and complete presentation of the linear relations
    by the mirrored signal-flow generators. Likewise record the statement and
    its literature pointer; it is the natural sequel to the presentation of
    §5.4.1.
- Prove the consequence of the linearity result of §5.4.3 that makes the
  sub-prop non-trivial: the behavior functor factors through `LinRel R`.

In-tree donors: the relations prop of §5.4.3, the linearity result of §5.4.3,
`Construction/Subcategory.v`, `Instance/Rel.v:45`, the rig class of §5.3.1.

## Definition of Done

- [ ] Linearity defined, with the adopted convention on the zero condition
      disclosed.
- [ ] Composition, identity, braid and monoidal product each proved to preserve
      linearity.
- [ ] `LinRel R` assembled as a wide sub-prop with a faithful inclusion.
- [ ] The behavior functor is shown to factor through `LinRel R`.
- [ ] The two unproved claims of the surrounding prose are recorded explicitly
      (with pointers), not silently dropped.
- [ ] Statement fidelity to the book (§5.4.3, Exercise 5.85), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the closure lemmas and
      `LinRel R`.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated alongside the relations entry, and
      `docs/INHABITATION.md` amended if the converse is left conditional.

## Verification

```
coqc -R . Category Instance/Rel/Linear.v
#   Print Assumptions linear_compose.
#   Print Assumptions LinRel.
#   Print Assumptions behavior_factors_through_LinRel.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the closure conditions are the two Seven Sketches §5.4.3 Exercise
5.85 lists, and the exercise's actual demand — that composites of linear
relations are linear — is proved rather than assumed.

## Dependencies

Depends on: 7sketches:5.4.3:def5.79 (the ambient relations prop).
Depends on: 7sketches:5.4.3:ex5.84 (linearity of behaviors, which makes the
factorization statement available).

<!-- catalog: {"ids":["7sketches:5.4.3:ex5.85"],"deps":["7sketches:5.4.3:def5.79","7sketches:5.4.3:ex5.84"]} -->

---8<---

```yaml
title: "Seven Sketches 5.4.3: Rel_R is compact closed with every object self-dual"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.4.3:thm5.87]
deps_item_ids: [7sketches:5.4.3:def5.79, 7sketches:5.4.3:def-sfg-plus]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.4.3 (Theorem 5.87, with
the cup and cap of the display (5.86) and the graphical snake check preceding
it). Printed p. 178; PDF p. 190. Item ID: `7sketches:5.4.3:thm5.87`.

## Background

Every object of the prop of relations over a rig is its own dual: the cup and
cap relations serve as unit and counit, and the snake equations hold. Matrices,
by contrast, are not compact closed — the cup and cap are not graphs of linear
maps. See [nLab: compact closed category](https://ncatlab.org/nlab/show/compact+closed+category),
[nLab: dualizable object](https://ncatlab.org/nlab/show/dual+object) and
[nLab: hypergraph category](https://ncatlab.org/nlab/show/hypergraph+category).

## Current state in the library

The general theorem is in tree at full strength and inhabited, but is never
applied here. `Hypergraph_CompactClosed`
(`Structure/Monoidal/CompactClosed.v:303`) yields compact closure with every
object self-dual for any hypergraph category, with the snake laws proved
(`hypergraph_snake_left`, `:241`), and `Cospan_Hypergraph`
(`Construction/Cospan/HypergraphInstance.v:703`) inhabits the hypothesis. The
gap is one of models rather than of statement. Concretely missing:

1. the relations prop itself — no rig, no `R^n`, no relations over a rig, no
   prop of them (see §5.3.1 and §5.4.3);
2. even *ordinary* `Rel` is not compact closed in tree: `Instance/Rel.v` builds
   only the bare category, and its header (`:35-39`) explicitly declares the
   dagger, the local posetal order and dagger-compactness as "not built here";
   `Instance/Rel.v` has no `Monoidal` instance at all, so `CompactClosed`
   cannot even be stated for it;
3. the cup and cap of the display (5.86) as behaviors, and the graphical snake
   check, since behaviors and signal flow graphs do not exist (see §5.4.3);
4. the theorem's negative half — that matrices are *not* compact closed,
   the cup and cap failing to be graphs of linear maps — for which the tree has
   no notion of a morphism failing to be dualizable.

Note a genuine hypothesis difference to disclose: the in-tree route *derives*
self-duality from a special commutative Frobenius structure on each object,
whereas the book exhibits the cup and cap directly.

## Work to be done

- In a new `Instance/Rel/CompactClosed.v`, prove Theorem 5.87 by the route the
  library makes cheapest: exhibit each object of the relations prop as carrying
  a special commutative Frobenius algebra (copy/discard and add/zero *as
  relations*, where copy and its converse are the Frobenius pair), obtain
  `Hypergraph` structure, and conclude compact closure with `n* = n` from
  `Hypergraph_CompactClosed` (`Structure/Monoidal/CompactClosed.v:303`).
- Independently exhibit the cup and cap of the display (5.86) — the relations
  `{(0, (x,x))} ⊆ R^0 × R^2` and `{((x,x), 0)} ⊆ R^2 × R^0` — and prove they
  are the unit and counit produced by that route, so the book's concrete
  witnesses and the library's abstract ones are identified rather than merely
  coexisting. Verify the snake equations both ways at every object, not only at
  `1`.
- Prove the negative half: the cup is not the graph of any linear map, hence
  the matrix prop is not compact closed with these witnesses. Formalize it as
  a concrete non-existence statement over a rig with at least two elements
  (there is no matrix whose graph is the cup, by a cardinality/point argument),
  which is the honest scope — a full "no compact closed structure whatsoever"
  claim is stronger than the book argues.
- Connect to the behavior functor of §5.4.3: the cup and cap are the behaviors
  of the corresponding mixed diagrams, which is why the graphical snake check
  in the book is a computation with signal flow graphs.

In-tree donors: `Structure/Monoidal/CompactClosed.v:139`/`:241`/`:303`,
`Construction/Cospan/HypergraphInstance.v:703`,
`Theory/Algebra/SpecialCommutativeFrobenius.v`, the relations prop of §5.4.3,
the behavior functor of §5.4.3.

## Definition of Done

- [ ] Each object of the relations prop carries a special commutative Frobenius
      structure, giving a hypergraph category.
- [ ] Compact closure with `n* = n` concluded, and the snake equations verified
      at every object.
- [ ] The book's cup and cap are exhibited and identified with the derived unit
      and counit.
- [ ] The negative half — the cup is not a graph of a linear map — proved in
      its stated scope.
- [ ] The cup and cap are identified as behaviors of the corresponding mixed
      diagrams.
- [ ] The hypothesis difference (derived versus exhibited self-duality) is
      disclosed in the header.
- [ ] Statement fidelity to the book (§5.4.3, Theorem 5.87), with the setoid
      `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom`.
- [ ] `Print Assumptions` reported closed for the compact closure and for the
      negative result.
- [ ] New file registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated, and `docs/INHABITATION.md` amended —
      `Hypergraph_CompactClosed` gains a second concrete model.

## Verification

```
coqc -R . Category Instance/Rel/CompactClosed.v
#   Print Assumptions RelR_CompactClosed.
#   Print Assumptions RelR_cup_is_not_a_graph.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: every object is self-dual, the unit and counit are the cup and cap
of the display (5.86), and the snake equations are proved — matching Seven
Sketches §5.4.3 Theorem 5.87.

## Dependencies

Depends on: #823 (consequences of compact closure — monoidal closedness,
uniqueness of duals, and the double dual — the compact-closed vocabulary).
Depends on: 7sketches:5.4.3:def5.79 (the relations prop).
Depends on: 7sketches:5.4.3:def-sfg-plus (the behavior functor, for the
identification of the cup and cap as behaviors).

<!-- catalog: {"ids":["7sketches:5.4.3:thm5.87"],"deps":["#823","7sketches:5.4.3:def5.79","7sketches:5.4.3:def-sfg-plus"]} -->

---8<---

```yaml
title: "Seven Sketches 5.3.2/5.4.3: Signal flow graphs over rigs of differential operators — a linear ODE system and cruise control"
labels: [book:seven-sketches, kind:theory, coverage-gap]
projects: [6]
covers: [7sketches:5.3.2:example5.44, 7sketches:5.4.3:example-control-theory-cruise-control]
deps_item_ids: [7sketches:5.3.1:def5.36, 7sketches:5.3.2:def5.45, 7sketches:5.4.3:def-sfg-plus]
deps_pending: []
```

## Source

Fong & Spivak, *Seven Sketches in Compositionality*, §5.3.2 (Example 5.44) and
§5.4.3 (the unnumbered closing worked example, "Back to control theory").
Printed pp. 162 and 178; PDF pp. 174 and 190. Item IDs:
`7sketches:5.3.2:example5.44`,
`7sketches:5.4.3:example-control-theory-cruise-control`.

## Background

Taking the scalars of a signal flow graph from a rig of formal differential
operators — polynomials in a symbol standing for differentiation, or Laurent
polynomials when integration is also wanted — turns linear systems of
differential equations and feedback controllers into diagrams. See
[Wikipedia: control theory](https://en.wikipedia.org/wiki/Control_theory),
[Wikipedia: Laurent polynomial](https://en.wikipedia.org/wiki/Laurent_polynomial)
and [Wikipedia: signal-flow graph](https://en.wikipedia.org/wiki/Signal-flow_graph).

## Current state in the library

Absent on both sides. The scalar side: `rg -ni 'differential'` returns exactly
two hits, both prose (`Construction/Groupoid.v:65` on differential geometry,
`Comonad/Coalgebra.v:105` on PDEs); there is no Laplace transform, no formal
differentiation operator, and no polynomial rig — indeed no rig at all (see
§5.3.1). Searches for "Laurent", "cruise" and "control theory" return nothing.
The diagram side is equally absent (see §5.3.2 and §5.4.3), and feedback
requires the mirrored generators, which do not exist.

## Work to be done

- In a new `Theory/Algebra/Rig/Polynomial.v`, construct the polynomial rig
  `R[D]` over a rig `R` — finitely supported sequences of coefficients with
  convolution product — and the Laurent extension `R[s, s⁻¹]` with the relation
  `s · s⁻¹ = s⁻¹ · s = 1`, as the book's rig of integration/differentiation
  symbols. Prove both are rigs; note that `R[s, s⁻¹]` is the group-rig of ℤ
  over `R` and construct it that way if it is cheaper.
- In `Instance/SignalFlow/Examples/ODE.v`, discharge Example 5.44: encode the
  book's two-equation linear system over `R[D]` — the amplifier labels being
  the operators the book lists — and build the corresponding morphism of the
  signal-flow prop, checking by computation that its matrix is the coefficient
  matrix of the rewritten system. The mathematical content being formalized is
  the *representation*: a linear system over a rig of differential operators is
  a signal flow graph whose matrix is its coefficient matrix.
- In `Instance/SignalFlow/Examples/CruiseControl.v`, discharge the closing
  example over `R[s, s⁻¹]`: build the cruise-control diagram with its explicit
  feedback loop (which needs the mirrored generators of §5.4.3, since the
  output speed is fed back into the controller), and compute its behavior.
  State the integral equation the diagram denotes as a relation between the
  external force, the desired speed and the actual speed, and prove the diagram
  and the equation determine the same relation — that identity is the
  formalizable content of the example.
- Record honestly in the header what is and is not being claimed: the
  formalization is symbolic (the rig of operators is formal, no analysis is
  involved), so nothing here asserts a theorem about actual solutions of
  differential equations.

In-tree donors: the rig class of §5.3.1, the signal-flow signature of §5.3.2,
the behavior functor of §5.4.3, `Instance/Coq/Lists.v` (finitely supported
sequences), `Theory/Algebra/Monoid.v:44`.

## Definition of Done

- [ ] `R[D]` and `R[s, s⁻¹]` constructed and proved to be rigs.
- [ ] Example 5.44's system encoded as a signal flow graph, with its matrix
      checked against the coefficient matrix by computation.
- [ ] The cruise-control diagram built with feedback, its behavior computed,
      and proved equal to the relation the integral equation denotes.
- [ ] The symbolic-only scope disclosed in the header.
- [ ] Statement fidelity to the book (§5.3.2 Example 5.44 and the §5.4.3
      closing example), with the setoid `≈` discipline on morphisms.
- [ ] No `Admitted`, `admit`, or new `Axiom` — and no dependence on Coq's
      stdlib `Reals` unless disclosed per `docs/AXIOMS.md` (the examples can be
      run over any rig of coefficients, so prefer a parametric base and
      instantiate at the naturals or a decidable field for the computations).
- [ ] `Print Assumptions` reported closed for the two rigs and both worked
      examples.
- [ ] New files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1.
- [ ] Builds on Coq 8.19 / 8.20 via the nix targets.
- [ ] `make todo` adds no new hits.
- [ ] `CLAUDE.md` Key Files index updated alongside the rig and signal-flow
      entries.

## Verification

```
coqc -R . Category Theory/Algebra/Rig/Polynomial.v \
                   Instance/SignalFlow/Examples/ODE.v \
                   Instance/SignalFlow/Examples/CruiseControl.v
#   Print Assumptions Polynomial_Rig.
#   Print Assumptions Laurent_Rig.
#   Print Assumptions example_5_44.
#   Print Assumptions cruise_control_behavior.
nix build .#category-theory_9_1
nix build .#category-theory_8_20
make todo
```

Review item: the amplifier labels are the operators Seven Sketches §5.3.2
Example 5.44 lists, and the cruise-control diagram has the feedback loop in
which the actual speed occurs twice, as the §5.4.3 closing example draws it.

## Dependencies

Depends on: 7sketches:5.3.1:def5.36 (the rig class, extended here by the
polynomial and Laurent constructions).
Depends on: 7sketches:5.3.2:def5.45 (the signal-flow signature).
Depends on: 7sketches:5.4.3:def-sfg-plus (the mirrored generators, needed for
the feedback loop).

<!-- catalog: {"ids":["7sketches:5.3.2:example5.44","7sketches:5.4.3:example-control-theory-cruise-control"],"deps":["7sketches:5.3.1:def5.36","7sketches:5.3.2:def5.45","7sketches:5.4.3:def-sfg-plus"]} -->
