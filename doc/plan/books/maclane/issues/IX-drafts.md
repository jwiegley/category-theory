title: "MacLane IX.1: Filtered categories and filtered colimits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.1:def1, maclane:IX.1:def2, maclane:IX.1:remark1, maclane:IX.1:def3]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *Categories for the Working Mathematician* (2nd ed.), §IX.1 "Filtered Limits", book p. 211–212 (PDF p. 218–219). Items: `maclane:IX.1:def1` (directed preorder), `maclane:IX.1:def2` (filtered category), `maclane:IX.1:remark1` (finite diagrams admit cocones), `maclane:IX.1:def3` (filtered colimit).

## Background
A category `J` is *filtered* when it is nonempty, any two objects admit arrows to a common target, and any parallel pair is coequalized by some further arrow; this categorifies the notion of a *directed preorder* (every finite subset has an upper bound). A *filtered colimit* is a colimit over a filtered index category, and these are exactly the colimits that commute with finite limits in `Set`. See nLab [filtered category](https://ncatlab.org/nlab/show/filtered+category) and [filtered colimit](https://ncatlab.org/nlab/show/filtered+colimit), and Wikipedia [Filtered category](https://en.wikipedia.org/wiki/Filtered_category).

## Current state in the library
No in-tree counterpart exists. A blind whole-tree search found `filtered` only in unrelated prose (`Comonad/CoKleisli.v:81`, "the filtered stream"), and `cofiltered` with zero hits. The order substrate is present — `Instance/Proset.v` gives the thin category of a preorder and `Instance/Poset.v` adds antisymmetry — but neither carries a directedness (common-upper-bound) predicate. The general colimit theory (`Structure/Limit.v`, `Colimit F := Limit (F^op)` at `Structure/Limit.v:158`) is stated over an arbitrary shape category and never carves out the filtered subclass. There is no directedness predicate on an order and no `Ind`-completion.

## Work to be done
- Define a directedness predicate on a preorder/poset (nonempty; every pair, hence every finite subset, has a common upper bound), building on `Instance/Proset.v`/`Instance/Poset.v`.
- Define a `Filtered` (and dually `Cofiltered`) predicate/class on a `Category`: nonempty; for objects `j`, `j'` there is `k` with `j ~> k` and `j' ~> k`; for parallel `u v : i ~> j` there is `w : j ~> k` with `w ∘ u ≈ w ∘ v`. Show a poset is filtered (as a thin category) iff it is directed.
- Prove the cocone lemma (`maclane:IX.1:remark1`): in a filtered `J`, every finite diagram is the base of a cocone (two-object and parallel-pair cases assemble to the finite case).
- Define `filtered colimit` as `Colimit F` with `Filtered J` (a thin wrapper over the existing `Colimit`).
- Suggested module: `Structure/Filtered.v` (category-level notions + directed preorder) and a re-export near `Structure/Limit.v` for the filtered-colimit notion. In-tree donors: `Instance/Proset.v`, `Instance/Poset.v`, `Structure/Limit.v`, `Structure/Cone.v` (`Cocone`).

## Definition of Done
- [ ] `Filtered`/`Cofiltered` and the directed-preorder predicate defined; poset-directed ⟺ thin-category-filtered proved; the finite-cocone lemma proved.
- [ ] All morphism (in)equalities use setoid `≈`, never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `Filtered` and the cocone lemma.
- [ ] New file(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; nix builds for Coq 8.19/8.20 pass; `make todo` adds no new hits.
- [ ] If treated as flagship, add a line to the CLAUDE.md Key Files index.

## Verification
- `coqc -R . Category Structure/Filtered.v` compiles.
- `Print Assumptions Filtered.` and `Print Assumptions <cocone-lemma>.` show no new axioms.
- `nix build .#category-theory_8_20` and `.#category-theory_9_1` succeed.
- Reviewer checks the definitions match Mac Lane §IX.1 (nonempty + the two filtering axioms; directed = finite subsets bounded).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.1:def1","maclane:IX.1:def2","maclane:IX.1:remark1","maclane:IX.1:def3"],"deps":[]} -->

---8<---

title: "MacLane IX.1: Small coproducts from finite coproducts and directed colimits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.1:thm1]
deps_item_ids: [maclane:IX.1:def1, maclane:IX.1:def3]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.1 Theorem 1, book p. 212 (PDF p. 219). Item: `maclane:IX.1:thm1`.

## Background
A category with finite coproducts and all colimits over small directed preorders has all small coproducts: the coproduct of an `I`-indexed family is realized as the directed colimit, over the poset of finite subsets of `I`, of the finite coproducts of the sub-families. See nLab [filtered colimit](https://ncatlab.org/nlab/show/filtered+colimit) and [cocomplete category](https://ncatlab.org/nlab/show/cocomplete+category).

## Current state in the library
Absent. Finite coproducts exist (`Structure/Cocartesian.v`, the `Cocartesian` class with `x + y`, `inl`/`inr`, initial `0`), but the reduction "finite coproducts + all small directed colimits ⟹ all small coproducts" is not present, and neither is the finite-subsets index poset nor its directed-colimit assembly (a blind search for `directed` returned only unrelated hits). Indexed coproducts obtained by other routes do not formalize this specific reduction.

## Work to be done
- Construct the poset `J₊` of finite subsets of a small index set `I`, ordered by inclusion, and prove it is directed (union of two finite subsets is a common upper bound).
- Define the diagram `J₊ ⟶ C` sending a finite subset to the finite coproduct of that sub-family, with the inclusion-induced coprojections.
- Prove its directed colimit is a coproduct of the whole family, giving the theorem "finite coproducts + directed colimits ⟹ all small coproducts".
- Suggested module: `Structure/Filtered/Coproducts.v`. In-tree donors: `Structure/Cocartesian.v`, `Structure/Limit.v` (`Colimit`), and the filtered/directed machinery from the IX.1 definitions issue.

## Definition of Done
- [ ] The `J₊` poset, the finite-coproduct diagram, and the theorem proved.
- [ ] Setoid `≈` throughout; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the principal theorem.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/Filtered/Coproducts.v` compiles.
- `Print Assumptions <coproducts_from_directed>.` closed.
- nix build targets `.#category-theory_8_20` / `.#category-theory_9_1` pass.
- Reviewer confirms the statement matches Mac Lane §IX.1 Theorem 1 (index poset of finite subsets; colimit is the full coproduct).

## Dependencies
Depends on: maclane:IX.1:def1
Depends on: maclane:IX.1:def3

<!-- catalog: {"ids":["maclane:IX.1:thm1"],"deps":["maclane:IX.1:def1","maclane:IX.1:def3"]} -->

---8<---

title: "MacLane IX.1: Algebraic forgetful functors create filtered colimits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.1:prop2, maclane:IX.1:remark2]
deps_item_ids: [maclane:IX.1:def3]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.1 Proposition 2 and the following remark, book p. 212–213 (PDF p. 219–220). Items: `maclane:IX.1:prop2` (the forgetful functor `Grp ⟶ Set` creates filtered colimits), `maclane:IX.1:remark2` (the same for `Alg_τ`, the algebras of a fixed operator/identity type).

## Background
For a filtered diagram of groups, the colimit of the underlying sets carries a unique group structure making the coprojections homomorphisms, and this is the colimit in `Grp`; the argument uses only that the index category is filtered, and it applies verbatim to the algebras of any equational type. This is the prototype of "algebraic (finitary monadic) forgetful functors create filtered colimits". See nLab [algebraic category](https://ncatlab.org/nlab/show/algebraic+category) and [filtered colimit](https://ncatlab.org/nlab/show/filtered+colimit).

## Current state in the library
Absent. There is no concrete category of groups with homomorphisms — `Structure/Group.v:109` provides only the internal `GroupObject` in a monoidal category — hence no forgetful `Grp ⟶ Set`; the concrete `Grp` is the subject of a separate filed issue (#255). Filtered colimits are themselves absent (see the IX.1 definitions issue). The `creates` vocabulary in-tree covers only limit creation (comma categories in `Construction/Comma/Limit.v`, equivalences in `Theory/Equivalence/Limit.v`) and Beck's `U`-split coequalizer creation (`Monad/Monadicity/Beck.v:164`); nothing states that an algebraic forgetful functor creates filtered colimits. On the `Alg_τ` side, `Theory/Lawvere/Model.v:77` (`Models T C`) supplies the modern counterpart of "algebras of a type", but a whole-tree search of `Theory/Lawvere/` for `colimit`/`cocomplete` returned zero hits.

## Work to be done
- State and prove "the forgetful functor of an algebraic category creates filtered colimits": given a filtered diagram, lift the underlying-set colimit to a unique algebra structure and show the lifted cocone is a colimit and is created. Do this once at the level of `Alg_τ`/Lawvere models (`Theory/Lawvere/Model.v`, `Theory/Lawvere/Sets.v`, underlying-set functor `ev1`), so that `Grp` is an instance.
- Instantiate for `Grp` once the concrete group category (#255) is available.
- Suggested module: `Theory/Lawvere/FilteredColimit.v` (general creation) with the `Grp` instance near `Instance/Grp.v`. In-tree donors: `Theory/Lawvere/Model.v`, `Theory/Lawvere/Sets.v`, `Structure/Coequalizer/Reflexive.v` (the reflexive-coequalizer workhorse for algebra colimits), and the filtered machinery of IX.1.

## Definition of Done
- [ ] A general "algebraic forgetful functor creates filtered colimits" theorem, with `Grp ⟶ Set` as a corollary.
- [ ] Uses a proper `Creates`-of-filtered-colimits formulation (lift-and-unique), setoid `≈` throughout; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the creation theorem.
- [ ] File(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Theory/Lawvere/FilteredColimit.v` compiles.
- `Print Assumptions <algebraic_creates_filtered_colimits>.` closed (instance-layer stdlib axioms of `Instance/`, if any, are the ones documented in docs/AXIOMS.md).
- nix build targets pass.
- Reviewer confirms the statement matches Mac Lane §IX.1 Proposition 2 + remark (creation uses only filteredness; generalizes from `Grp` to `Alg_τ`).

## Dependencies
Depends on: maclane:IX.1:def3
Depends on: #255
Depends on: #440

<!-- catalog: {"ids":["maclane:IX.1:prop2","maclane:IX.1:remark2"],"deps":["maclane:IX.1:def3","#255","#440"]} -->

---8<---

title: "MacLane IX.1: Grp is cocomplete"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.1:cor3]
deps_item_ids: [maclane:IX.1:thm1, maclane:IX.1:prop2]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.1 Corollary 3, book p. 213–214 (PDF p. 220–221). Item: `maclane:IX.1:cor3`.

## Background
The category of groups has all small colimits: the trivial group is initial, the coproduct of two groups is their free product `G ∗ H`, coequalizers are quotient groups `H ↠ H/N`, filtered colimits are created from `Set` (§IX.1 Proposition 2), and small coproducts then follow from finite coproducts plus directed colimits (§IX.1 Theorem 1). See nLab [cocomplete category](https://ncatlab.org/nlab/show/cocomplete+category) and Wikipedia [Free product](https://en.wikipedia.org/wiki/Free_product).

## Current state in the library
Absent. There is no concrete `Grp` category in-tree (only the internal `GroupObject`, `Structure/Group.v:109`), so `Grp` cocomplete is not even statable yet; the concrete group category is filed as #255. The abstract `Cocomplete` predicate exists (`Structure/Complete.v:119`) but is never instantiated for groups, and there is no free product of groups, no quotient-group coequalizer, and no cocompleteness witness for any concrete algebraic category.

## Work to be done
- Over the concrete `Grp` (#255): construct the free product `G ∗ H` as the binary coproduct and quotient groups `H/N` as coequalizers; supply the trivial group as initial object.
- Assemble all small colimits: finite coproducts + created filtered colimits ⟹ all small coproducts (via the IX.1 Theorem 1 issue and the filtered-creation issue), then coproducts + coequalizers ⟹ all colimits; conclude `Cocomplete Grp` (`Structure/Complete.v`).
- Suggested module: `Instance/Grp/Cocomplete.v`. In-tree donors: `Structure/Complete.v`, `Structure/Cocartesian.v`, `Structure/Coequalizer.v`, and the IX.1 filtered-creation and finite-coproduct-to-coproduct results.

## Definition of Done
- [ ] `Cocomplete Grp` proved, with the free product (coproduct), quotient-group coequalizers, and initial object supplied.
- [ ] Setoid `≈` throughout; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `Grp_Cocomplete` (any stdlib axioms are the documented instance-layer ones in docs/AXIOMS.md).
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Instance/Grp/Cocomplete.v` compiles.
- `Print Assumptions Grp_Cocomplete.` closed (modulo documented instance-layer axioms).
- nix build targets pass.
- Reviewer confirms the construction matches Mac Lane §IX.1 Corollary 3 (free product = coproduct; quotient = coequalizer; colimits assembled via Prop 2 + Thm 1).

## Dependencies
Depends on: maclane:IX.1:thm1
Depends on: maclane:IX.1:prop2
Depends on: #255

<!-- catalog: {"ids":["maclane:IX.1:cor3"],"deps":["maclane:IX.1:thm1","maclane:IX.1:prop2","#255"]} -->

---8<---

title: "MacLane IX.2: Finite limits commute with filtered colimits in Set"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.2:construction1, maclane:IX.2:thm1, maclane:IX.2:ex1]
deps_item_ids: [maclane:IX.1:def2]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.2 "Interchange of Limits", the canonical map (eq. 3, diagram 4), Theorem 1, and Exercise 1, book p. 215–216 (PDF p. 222–223). Items: `maclane:IX.2:construction1` (the interchange arrow `κ`), `maclane:IX.2:thm1` (finite limits commute with filtered colimits in `Set`), `maclane:IX.2:ex1` (naturality of `κ`).

## Background
For a bifunctor `F : P × J ⟶ X` there is a canonical comparison `κ : Colim_j Lim_p F(p,j) ⟶ Lim_p Colim_j F(p,j)` built from the limiting and colimiting universal properties; it is natural in `F`, and when `P` is finite and `J` is filtered it is an isomorphism in `Set` — finite limits commute with filtered colimits. See nLab [commutativity of limits and colimits](https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits) and [filtered colimit](https://ncatlab.org/nlab/show/filtered+colimit).

## Current state in the library
Absent. There is no `Lim`/`Colim` functor of a parameter with which to form the iterated `(co)limit`s, so `κ` cannot even be written; a blind search for `iterated`, `interchange`, `colim…lim`, and `commute` found no comparison map (the only `κ`/`kappa` hits are Freyd `κ`-categories in `Structure/Premonoidal/Freyd.v` and a bound cone variable in `Structure/Limit/Weighted.v`). `Structure/Limit/Preservation.v` gives `PreservesLimit`/`PreservesColimit`, but those compare `F(lim G)` with `lim(F∘G)` for a target functor — a postcomposition comparison, not Mac Lane's `κ`. Filtered categories are themselves absent (the IX.1 definitions issue). Colimits in `Set` are not developed as a construction (`Instance/Sets` carries no `Colimit`), so the theorem's ambient filtered colimits in `Set` must be supplied.

## Work to be done
- Using parametrized limits/colimits in a functor category (filed #425), build `Lim_p F(p,-)` functorial in `j` and `Colim_j F(-,j)` functorial in `p`, then define `κ` from the two universal properties; prove `κ` is natural in `F` (`maclane:IX.2:ex1`).
- Prove the theorem in `Set`: for `P` finite and `J` filtered, construct a two-sided inverse of `κ` using the finite-diagram-has-a-cocone property of filtered `J` (from the IX.1 cocone lemma).
- Suggested module: `Instance/Sets/FilteredColimit.v` (filtered colimits in `Set`) and `Structure/Limit/Interchange.v` (the `κ` map + theorem). In-tree donors: `Structure/Limit.v`, `Structure/Limit/Preservation.v` (mediating maps), `Instance/Sets.v`, and the IX.1 filtered machinery.

## Definition of Done
- [ ] `κ` defined and proved natural; the `Set` theorem (P finite, J filtered ⟹ `κ` iso) proved with an explicit inverse.
- [ ] Iso via `≅`/two-sided inverse in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the interchange theorem.
- [ ] File(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/Limit/Interchange.v` compiles.
- `Print Assumptions <finite_limits_commute_filtered_colimits>.` closed.
- nix build targets pass.
- Reviewer confirms the statement matches Mac Lane §IX.2 Theorem 1 and the definition of `κ` (diagram 4), and that naturality matches Exercise 1.

## Dependencies
Depends on: maclane:IX.1:def2
Depends on: #425

<!-- catalog: {"ids":["maclane:IX.2:construction1","maclane:IX.2:thm1","maclane:IX.2:ex1"],"deps":["maclane:IX.1:def2","#425"]} -->

---8<---

title: "MacLane IX.2: Interchange of iterated limits and of iterated colimits"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.2:remark1, maclane:IX.8:remark1]
deps_item_ids: [maclane:IX.8:cor1, maclane:IX.5:prop3]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.2 (the interchange remark, book p. 214–215, PDF p. 221–222) and §IX.8 (the limit/colimit specialization of the Fubini corollary, book p. 231, PDF p. 238). Items: `maclane:IX.2:remark1`, `maclane:IX.8:remark1`.

## Background
Iterated limits commute — for `F : P × C ⟶ X` with `P`, `C` small and `X` complete, `Lim_p Lim_c F ≅ Lim_{(p,c)} F ≅ Lim_c Lim_p F` — and dually iterated colimits commute; this is the limit/colimit shadow of the Fubini theorem for ends. Note limits do *not* in general commute with colimits. See nLab [commutativity of limits and colimits](https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits).

## Current state in the library
Absent. No `Lim`/`Colim` functor on a diagram category exists, so an iterated limit cannot be formed; a blind search for `iterated limit`, `iterated colimit`, and `limits commute` returned zero relevant hits. The nearest in-tree machinery is `coend_fubini` (`Theory/Coend/Fubini.v`), which is the `Sets`-only double-vs-iterated *coend* isomorphism (the §IX.8 mechanism), never specialized to plain limit/colimit interchange because neither a `Lim` functor nor the "every limit is an end" reduction is present.

## Work to be done
- Derive iterated-limit interchange from the Fubini corollary for ends (the §IX.8 corollary issue) via "every limit is an end" (the §IX.5 correspondence issue) and the `Lim` functor (filed #420); dualize for colimits.
- Alternatively supply a direct proof through the product index category `P × C` and the universal properties.
- Suggested module: `Structure/Limit/Interchange.v` (alongside the mixed-interchange results). In-tree donors: `Theory/Coend/Fubini.v`, `Structure/Limit.v`, `Structure/Complete.v`.

## Definition of Done
- [ ] `Lim_p Lim_c F ≅ Lim_{(p,c)} F ≅ Lim_c Lim_p F` (and the colimit dual) proved for small `P`, `C` and complete/cocomplete `X`.
- [ ] Isomorphisms via `≅` in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the interchange isos.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/Limit/Interchange.v` compiles.
- `Print Assumptions <iterated_limits_commute>.` closed.
- nix build targets pass.
- Reviewer confirms the statement matches Mac Lane §IX.2 remark / §IX.8 remark (both iteration orders isomorphic to the joint (co)limit).

## Dependencies
Depends on: maclane:IX.8:cor1
Depends on: maclane:IX.5:prop3
Depends on: #420

<!-- catalog: {"ids":["maclane:IX.2:remark1","maclane:IX.8:remark1"],"deps":["maclane:IX.8:cor1","maclane:IX.5:prop3","#420"]} -->

---8<---

title: "MacLane IX.2: Pseudo-filtered categories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.2:ex2]
deps_item_ids: [maclane:IX.1:def2]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.2 Exercise 2 (Verdier), book p. 216 (PDF p. 223). Item: `maclane:IX.2:ex2`.

## Background
A category is *pseudo-filtered* (Verdier) when it satisfies the filtering condition on parallel pairs together with the weaker condition that any two arrows out of a common source embed in a commutative diamond; a category is filtered iff it is connected and pseudo-filtered, and pseudo-filtered iff each connected component is filtered. See nLab [filtered category](https://ncatlab.org/nlab/show/filtered+category) (pseudo-filtered is the Verdier weakening discussed there and in SGA4).

## Current state in the library
Absent. A blind search for `pseudo-filtered`/`pseudofiltered` returned zero hits; `filtered` appears only as unrelated prose (`Comonad/CoKleisli.v:81`); the six `Verdier` hits are all derived-category / Verdier-quotient history. There is also no category-level connectedness predicate in-tree (searches for `Connected` category classes returned nothing) — that predicate is filed as #352.

## Work to be done
- Define `PseudoFiltered` on a `Category` (parallel-pair filtering + the common-source diamond condition), reusing the `Filtered` class from the IX.1 definitions issue.
- Prove the two characterizations: `Filtered J ⟺ Connected J ∧ PseudoFiltered J` (connectedness via filed #352), and `PseudoFiltered J ⟺` each connected component of `J` is filtered.
- Suggested module: `Structure/Filtered/Pseudo.v`. In-tree donors: the IX.1 `Filtered` class, `Construction/Subcategory.v` (components), and the connected-category predicate (#352).

## Definition of Done
- [ ] `PseudoFiltered` defined and both characterizations proved.
- [ ] Setoid `≈` for all arrow equalities; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `PseudoFiltered` and the two characterizations.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/Filtered/Pseudo.v` compiles.
- `Print Assumptions <filtered_iff_connected_pseudofiltered>.` closed.
- nix build targets pass.
- Reviewer confirms the definition and characterizations match Mac Lane §IX.2 Exercise 2.

## Dependencies
Depends on: maclane:IX.1:def2
Depends on: #352

<!-- catalog: {"ids":["maclane:IX.2:ex2"],"deps":["maclane:IX.1:def2","#352"]} -->

---8<---

title: "MacLane IX.2: Coproducts commute with pullbacks, and pseudo-filtered colimits commute with pullbacks, in Set"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IX.2:ex3, maclane:IX.2:ex4]
deps_item_ids: [maclane:IX.2:ex2]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.2 Exercises 3 and 4, book p. 216 (PDF p. 223). Items: `maclane:IX.2:ex3` (coproducts commute with pullback in `Set`), `maclane:IX.2:ex4` (pseudo-filtered colimits commute with pullbacks in `Set`).

## Background
In `Set`, pulling a coproduct back along any map gives the coproduct of the pullbacks — coproducts are stable under pullback (the extensivity/universality property) — and, combining this with the component structure of pseudo-filtered categories, pseudo-filtered colimits commute with pullbacks. See nLab [extensive category](https://ncatlab.org/nlab/show/extensive+category).

## Current state in the library
Absent. A blind search for `extensive`, `coproduct…pullback`, and `stable…coproduct` returned only bibliographic citations (`Structure/Cocartesian.v`, `Structure/Initial.v`); no extensivity or coproduct/pullback commutation is formalized. `Structure/Distributive.v` gives distributivity of `×` over `+` (the product functor preserving finite coproducts) — a genuinely different and weaker condition — and it is not instantiated for `Set`/`FinSet`. `Set` is not even given a general `HasPullbacks` instance (`Structure/Pullback.v:215` is a class with only `FinSet_Pullbacks` in-tree), so pullbacks in `Set` are a prerequisite.

## Work to be done
- Supply (or assume, and discharge) pullbacks in `Set`; prove coproducts commute with pullback in `Set` (Exercise 3): the canonical map from the coproduct of the fibre pullbacks to the pullback of the coproduct is an isomorphism.
- Using Exercise 3 and the pseudo-filtered machinery (the IX.2 pseudo-filtered issue), prove pseudo-filtered colimits commute with pullbacks in `Set` (Exercise 4).
- Suggested module: `Instance/Sets/Extensive.v`. In-tree donors: `Instance/Sets.v`, `Structure/Pullback.v`, `Structure/Cocartesian.v`, and the pseudo-filtered issue.

## Definition of Done
- [ ] Coproducts-commute-with-pullback in `Set` proved; pseudo-filtered-colimits-commute-with-pullbacks in `Set` proved.
- [ ] Isos via `≅`/two-sided inverse in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for both principal results.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Instance/Sets/Extensive.v` compiles.
- `Print Assumptions <coproducts_commute_pullback_Sets>.` and `<pseudofiltered_colimits_commute_pullback_Sets>.` closed.
- nix build targets pass.
- Reviewer confirms the statements match Mac Lane §IX.2 Exercises 3–4.

## Dependencies
Depends on: maclane:IX.2:ex2

<!-- catalog: {"ids":["maclane:IX.2:ex3","maclane:IX.2:ex4"],"deps":["maclane:IX.2:ex2"]} -->

---8<---

title: "MacLane IX.3: Final (cofinal) functors and final subcategories"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.3:def1, maclane:IX.3:def2]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.3 "Final Functors", the final-functor and final-subcategory definitions, book p. 217 (PDF p. 224). Items: `maclane:IX.3:def1` (final functor), `maclane:IX.3:def2` (final subcategory).

## Background
A functor `L : J' ⟶ J` is *final* (classically *cofinal*) when for every object `k` of `J` the comma category `(k ↓ L)` is nonempty and connected; a subcategory is final when its inclusion is. Finality is exactly the condition under which a colimit may be computed by restricting the diagram along `L`. See nLab [final functor](https://ncatlab.org/nlab/show/final+functor).

## Current state in the library
Absent. A blind search for `cofinal`, `final functor`, and `final subcategory` returned zero hits; every `final` hit is `final coalgebra` / `final object` (terminal) / Lambek / streams. `Functor/Structure/Terminal.v:53` defines `InitialFunctor` as a functor *preserving* the initial object — a different concept. The comma category exists (`Construction/Comma.v`) but carries no nonemptiness or connectedness API, and there is no category-level connectedness predicate in-tree (filed as #352).

## Work to be done
- Define `Final` for a functor `L : J' ⟶ J`: for each `k : J`, the comma `(k ↓ L)` is nonempty and connected (connectedness via filed #352). Dually define `Initial` (coinitial) by `Final` on the opposites.
- Define `FinalSubcategory` as finality of the inclusion; record the linear-order characterization (for `J` a linear order, `J' ⊆ J` is final iff every `k` has some `j' ∈ J'` with `k ≤ j'`) as a lemma.
- Suggested module: `Structure/Final.v` (or `Theory/Functor/Final.v`). In-tree donors: `Construction/Comma.v`, `Construction/Subcategory.v`, and the connected-category predicate (#352).

## Definition of Done
- [ ] `Final`/`Initial` functor predicates and `FinalSubcategory` defined; the linear-order characterization proved.
- [ ] All arrow relations in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `Final`.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/Final.v` compiles.
- `Print Assumptions Final.` closed.
- nix build targets pass.
- Reviewer confirms the definition matches Mac Lane §IX.3 (comma `(k ↓ L)` nonempty and connected).

## Dependencies
Depends on: #352

<!-- catalog: {"ids":["maclane:IX.3:def1","maclane:IX.3:def2"],"deps":["#352"]} -->

---8<---

title: "MacLane IX.3: Final functors preserve colimits (and initial functors, limits)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.3:construction1, maclane:IX.3:thm1, maclane:IX.3:remark1]
deps_item_ids: [maclane:IX.3:def1]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.3 Theorem 1 (with the comparison map, eq. 1) and the dual remark, book p. 217–218 (PDF p. 224–225). Items: `maclane:IX.3:construction1` (the comparison `h : Colim FL ⟶ Colim F`), `maclane:IX.3:thm1` (final functors preserve and detect colimits), `maclane:IX.3:remark1` (dual: initial functors and limits).

## Background
For a final `L : J' ⟶ J` and `F : J ⟶ X`, the canonical comparison `h : Colim FL ⟶ Colim F` is an isomorphism whenever `Colim FL` exists — so colimits may be computed over a final subcategory — and dually limits may be computed over an initial subcategory. See nLab [final functor](https://ncatlab.org/nlab/show/final+functor).

## Current state in the library
Absent. No comparison map `Colim(F∘L) ⟶ Colim F` induced by an index functor `L` is built; the reusable ingredients exist but are unassembled — the restriction functor `Induced := (−∘F)` (`Theory/Kan/Extension.v:127`), cone whiskering (`Theory/Equivalence/Limit.v:271`, postcomposition by a target functor, not precomposition of the index), and mediating maps `colimit_med` (`Structure/Limit/Preservation.v:152`). `PreservesColimit` (`Structure/Limit/Preservation.v:206`) is the distinct postcomposition comparison. Finality itself is absent (the IX.3 definitions issue).

## Work to be done
- Define the comparison `h : Colim(F∘L) ⟶ Colim F` as the unique arrow with `h ∘ μ'_{j'} ≈ μ_{L j'}` (μ, μ' the colimiting cocones), when both colimits exist.
- Prove Theorem 1: if `L` is final and `Colim(F∘L)` exists, then `Colim F` exists and `h` is an isomorphism (use nonemptiness + connectedness of `(k ↓ L)` to invert `h`).
- State and prove the dual for initial functors and limits.
- Suggested module: `Structure/Limit/Final.v`. In-tree donors: `Structure/Limit.v`, `Structure/Limit/Preservation.v`, `Structure/Cone.v`, and the `Final` predicate from the IX.3 definitions issue.

## Definition of Done
- [ ] `h` defined; Theorem 1 (final ⟹ `h` iso) and its dual proved.
- [ ] Iso via `≅`/two-sided inverse in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the preservation theorem.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/Limit/Final.v` compiles.
- `Print Assumptions <final_functor_preserves_colimit>.` closed.
- nix build targets pass.
- Reviewer confirms the statement matches Mac Lane §IX.3 Theorem 1 and its dual.

## Dependencies
Depends on: maclane:IX.3:def1

<!-- catalog: {"ids":["maclane:IX.3:construction1","maclane:IX.3:thm1","maclane:IX.3:remark1"],"deps":["maclane:IX.3:def1"]} -->

---8<---

title: "MacLane IX.3: Properties of final functors and colimits of representables"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IX.3:ex1, maclane:IX.3:ex2, maclane:IX.3:ex3, maclane:IX.3:ex4, maclane:IX.3:ex5]
deps_item_ids: [maclane:IX.3:def1, maclane:IX.3:thm1, maclane:IX.1:def2]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.3 Exercises 1–5, book p. 218 (PDF p. 225). Items: `maclane:IX.3:ex1` (one-object inclusion final iff terminal), `maclane:IX.3:ex2` (composite of final functors is final), `maclane:IX.3:ex3` (full functor into a filtered category with nonempty commas is final), `maclane:IX.3:ex4` (colimit of a covariant hom-functor is a point), `maclane:IX.3:ex5` (converse of Theorem 1).

## Background
These exercises exercise the finality notion: the inclusion of `{j}` is final iff `j` is terminal; finality is closed under composition; a full functor into a filtered category with all commas nonempty is final; `Colim_J J(k,-) ≅ 1` in `Set` by the Yoneda lemma (the category of elements of a representable has an initial object); and, conversely, if the comparison map is an isomorphism for every cocomplete `X` and every `F`, then `L` is final. See nLab [final functor](https://ncatlab.org/nlab/show/final+functor).

## Current state in the library
Absent. All five presuppose the finality notion, which does not exist in-tree (the IX.3 definitions issue). For Exercise 4, the co-Yoneda density iso `∫^x C(x,c) × F x ≅ F c` is present (`Theory/Coend/Yoneda.v:174`) but it is a coend statement and does not specialize to `Colim_J J(k,-) ≅ 1`; `Instance/Sets` carries no colimit construction. Exercise 3 additionally needs filtered categories (the IX.1 definitions issue).

## Work to be done
- Prove Exercise 1 (`{j} ↪ J` final ⟺ `j` terminal), Exercise 2 (composition), Exercise 3 (full + filtered target + nonempty commas ⟹ final), all over the `Final` predicate.
- Prove Exercise 4 (`Colim_J J(k,-) ≅ 1` in `Set`) via the Yoneda lemma / initiality of `(k, id)` in the category of elements; then Exercise 5 (the converse of Theorem 1) using Exercise 4 with `F = J(k,-)`, `X = Set`.
- Suggested module: `Structure/Limit/Final.v` (exercises alongside the theorem) or `Structure/Limit/Final/Exercises.v`. In-tree donors: `Functor/Hom/Yoneda.v`, `Structure/Terminal.v`, the `Final` predicate (IX.3 defs) and the final-functor theorem (IX.3 theorem issue), and filtered categories (IX.1 defs).

## Definition of Done
- [ ] All five exercises proved.
- [ ] Setoid `≈` / `≅` throughout; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the principal lemmas (`final_iff_terminal`, `final_compose`, `colim_representable_terminal`, `final_converse`).
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/Limit/Final/Exercises.v` compiles.
- `Print Assumptions colim_representable_terminal.` closed.
- nix build targets pass.
- Reviewer confirms each result matches Mac Lane §IX.3 Exercises 1–5.

## Dependencies
Depends on: maclane:IX.3:def1
Depends on: maclane:IX.3:thm1
Depends on: maclane:IX.1:def2

<!-- catalog: {"ids":["maclane:IX.3:ex1","maclane:IX.3:ex2","maclane:IX.3:ex3","maclane:IX.3:ex4","maclane:IX.3:ex5"],"deps":["maclane:IX.3:def1","maclane:IX.3:thm1","maclane:IX.1:def2"]} -->

---8<---

title: "MacLane IX.4: Canonical wedges — evaluation and the identity family"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.4:construction2, maclane:IX.4:construction4]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.4 "Diagonal Naturality", the evaluation and identity examples, book p. 220 (PDF p. 227–228). Items: `maclane:IX.4:construction2` (evaluation is an extranatural transformation), `maclane:IX.4:construction4` (the identity arrows form a dinatural/extranatural transformation).

## Background
Two canonical extranatural (wedge) transformations: evaluation `⟨h,x⟩ ↦ h x` is a wedge `hom(-,A) × (-) ⟹ A` (natural in the parameter `A`), and the identities `1_c`, viewed as arrows `1 ⟶ hom(c,c)` from the one-point set, form an extranatural transformation `1 ⟹ hom(-,-)`, the wedge condition being exactly `f ∘ 1_c = 1_{c'} ∘ f`. See nLab [extranatural transformation](https://ncatlab.org/nlab/show/extranatural+transformation) and [end](https://ncatlab.org/nlab/show/end).

## Current state in the library
Partial. The `Wedge`/`Cowedge` classes exist (`Structure/Wedge.v:38,61`) and the `Dinatural` class (`Theory/Dinatural.v:51`), but they have zero instances tree-wide. For evaluation, `eval := uncurry id` (`Structure/Cartesian/Closed.v:75`, the exponential counit; in `Set`, `y^x ≅ hom(x,y)`, so this is Mac Lane's `V_X`) exists but is never assembled as a wedge; the bifunctor `hom(-,A) × (-)` and the extranaturality law are not set up. For the identity family, the exact target bifunctor `Hom : C^op ∏ C ⟶ Sets` (`Functor/Hom.v:49`) and the identity legs exist, but the wedge `1 ⟹ Hom` with terminal apex and identity legs is never built.

## Work to be done
- Construct the mixed-variance bifunctor `S(X,Y) = hom(X,A) × Y : Set^op ∏ Set ⟶ Set` and prove `eval` is a `Wedge`/`Cowedge` for it (extranatural in the running variable), with naturality in the parameter `A`.
- Construct the wedge `1 ⟹ Hom` over `Functor/Hom.v`'s `Hom : C^op ∏ C ⟶ Sets`, apex the terminal setoid, legs the identities, and discharge the (trivial) extranaturality `f ∘ 1_c ≈ 1_{c'} ∘ f`.
- These become the library's first concrete `Wedge`/`Dinatural` instances. Suggested module: `Structure/Wedge/Examples.v`. In-tree donors: `Structure/Wedge.v`, `Theory/Dinatural.v`, `Functor/Hom.v`, `Structure/Cartesian/Closed.v`, `Instance/Sets.v`.

## Definition of Done
- [ ] Evaluation-wedge and identity-wedge instances built and their extranaturality proved; parameter-naturality of evaluation proved.
- [ ] Wedge conditions in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for both wedge instances.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/Wedge/Examples.v` compiles.
- `Print Assumptions <eval_wedge>.` and `<identity_wedge>.` closed.
- nix build targets pass.
- Reviewer confirms the two wedges match Mac Lane §IX.4 (evaluation, square 3; identities, square 4/dual).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.4:construction2","maclane:IX.4:construction4"],"deps":[]} -->

---8<---

title: "MacLane IX.4: The unit and counit of a parametrized adjunction are (di)natural in the parameter"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.4:construction3, maclane:IX.4:ex1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.4, the parametrized-adjunction counit example and Exercise 1, book p. 220, 222 (PDF p. 227, 229). Items: `maclane:IX.4:construction3` (the counit is extranatural in the parameter), `maclane:IX.4:ex1` (the unit is dinatural in the parameter).

## Background
For an adjunction with a parameter — a natural bijection `A(F(x,p), a) ≅ X(x, G(p,a))` in `x, p, a`, with `F : X × P ⟶ A`, `G : P^op × A ⟶ X` — the counit `ε_{⟨p,a⟩} : F(G(p,a),p) ⟶ a` is natural in `a` and extranatural (dinatural) in the parameter `p`, and dually the unit `η_x : x ⟶ G(p, F(x,p))` is dinatural in `p`; this dinaturality is equivalent to naturality of the parametrized adjunction in `p`. Evaluation is the special case. See nLab [dinatural transformation](https://ncatlab.org/nlab/show/dinatural+transformation) and Wikipedia [Adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors).

## Current state in the library
Absent. Ordinary adjunctions exist (`Theory/Adjunction.v`, with `unit`/`counit` and the triangle identities), but there is no parameter category `P`, no family of adjunctions, and no extranaturality-in-`p` statement; a blind search found no "adjunction with a parameter" (only Reynolds parametricity). Parametrized adjunctions themselves are filed as #396. The `Dinatural` class (`Theory/Dinatural.v:51`) is never instantiated by any adjunction (co)unit.

## Work to be done
- Building on the parametrized-adjunction structure (filed #396), exhibit the counit components as a `Wedge`/`Dinatural` instance in the parameter `p` and prove naturality in `a` (`maclane:IX.4:construction3`).
- Exhibit the unit as dinatural in `p` and prove the equivalence "unit dinatural ⟺ the parametrized adjunction is natural in `p`", then dualize (`maclane:IX.4:ex1`).
- Suggested module: `Theory/Dinatural/ParametrizedAdjunction.v`. In-tree donors: the parametrized-adjunction development (#396), `Theory/Dinatural.v`, `Structure/Wedge.v`, `Theory/Adjunction.v`.

## Definition of Done
- [ ] Counit-extranatural-in-`p` and unit-dinatural-in-`p` proved, with the naturality equivalence and its dual.
- [ ] Dinaturality laws in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the principal results.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Theory/Dinatural/ParametrizedAdjunction.v` compiles.
- `Print Assumptions <parametrized_counit_extranatural>.` closed.
- nix build targets pass.
- Reviewer confirms the statements match Mac Lane §IX.4 (counit example; Exercise 1), with evaluation recovered as the special case.

## Dependencies
Depends on: #396

<!-- catalog: {"ids":["maclane:IX.4:construction3","maclane:IX.4:ex1"],"deps":["#396"]} -->

---8<---

title: "MacLane IX.4: Multi-variable (di)natural transformations and dummy variables"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.4:def2, maclane:IX.4:def4]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.4, the dummy-variable and combined-transformation definitions, book p. 219, 221 (PDF p. 226, 228). Items: `maclane:IX.4:def2` (dummy / constant-in-a-variable functor), `maclane:IX.4:def4` (combined multi-variable natural/dinatural transformation).

## Background
A bifunctor is *dummy* in a variable when it factors through the projection deleting that variable (dummy in both variables = constant at an object). The combined notion unifies naturality and dinaturality: for `S : C^op × C × A ⟶ B` and `T : A × D^op × D ⟶ B`, a transformation `γ` assigns to `(c,a,d)` an arrow `S(c,c,a) ⟶ T(a,d,d)` that is natural in `a` and dinatural in `c` and `d` — the framework in which ordinary, covariant-contravariant, and extranatural transformations are all "natural transformations". See nLab [dinatural transformation](https://ncatlab.org/nlab/show/dinatural+transformation) and [extranatural transformation](https://ncatlab.org/nlab/show/extranatural+transformation).

## Current state in the library
Partial/absent. The both-variables-dummy case is the constant/diagonal functor `Δ` (`Functor/Diagonal.v:33`, actively used as `Δw` in `Structure/Wedge.v`); the projections `Fst`/`Snd` (`Construction/Product.v:149`) let one express "dummy in one variable" as `F ∘ Snd`, but no named predicate captures a bifunctor being independent of one argument (a search for `dummy` returned zero hits; `Functor/Structure/Constant.v`'s `ConstantFunctor` is the unrelated embedded-constants notion). The combined multi-variable transformation is entirely absent: `Theory/Dinatural.v` gives only the strictly two-variable, single-slot `Dinatural` for `F,G : C^op ∏ C ⟶ D`, and `Theory/Natural/Transformation.v` the ordinary notion; nothing mixes per-slot naturality and dinaturality over three-or-more-variable functors.

## Work to be done
- Define a `Dummy`-in-a-variable predicate for a bifunctor (factoring through `Fst`/`Snd`), with the both-variables case recovering `Δ`.
- Define the combined multi-variable transformation class (natural in the designated slots, dinatural in the mixed-variance pairs), specializing to `Transform` and `Dinatural`; prove that naturality in a product argument reduces to separate naturality in each factor.
- Suggested module: `Theory/Dinatural/MultiVariable.v`. In-tree donors: `Theory/Dinatural.v`, `Theory/Natural/Transformation.v`, `Functor/Diagonal.v`, `Construction/Product.v`.

## Definition of Done
- [ ] `Dummy` predicate and the combined multi-variable transformation class defined; specialization to `Transform`/`Dinatural` and the product-argument reduction proved.
- [ ] All laws in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the combined class and the reduction lemma.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Theory/Dinatural/MultiVariable.v` compiles.
- `Print Assumptions <MultiNatural>.` closed.
- nix build targets pass.
- Reviewer confirms the definitions match Mac Lane §IX.4 (dummy variables; the three types unified).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.4:def2","maclane:IX.4:def4"],"deps":[]} -->

---8<---

title: "MacLane IX.4: Composition calculus for dinatural transformations"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.4:remark1, maclane:IX.4:prop1, maclane:IX.4:ex3, maclane:IX.4:ex4, maclane:IX.4:ex5, maclane:IX.4:ex6]
deps_item_ids: [maclane:IX.4:def4]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.4, the composition remark, Proposition 1, and Exercises 3–6, book p. 221–222 (PDF p. 228–229). Items: `maclane:IX.4:remark1` (whiskering a dinatural by naturals), `maclane:IX.4:prop1` (the diagonal composite is natural), `maclane:IX.4:ex3` (dinaturality by separation of arguments), `maclane:IX.4:ex4` (composition for more factors), `maclane:IX.4:ex5` (dinaturals do not compose), `maclane:IX.4:ex6` (general many-variable composition rule).

## Background
Dinatural transformations do not compose in general, but they may be whiskered on either side by genuinely natural transformations to give a dinatural composite; more generally the diagonal composite of families natural-in-one-variable and dinatural-in-another is natural, and joint dinaturality in a product variable factors into separate dinaturality in each factor. See nLab [dinatural transformation](https://ncatlab.org/nlab/show/dinatural+transformation).

## Current state in the library
Absent. `Theory/Dinatural.v` deliberately supplies only the `Dinatural` data and its component setoid, with its header noting in prose that dinaturals do not compose in general — but there is no lemma that whiskering by naturals preserves dinaturality (remark 1), no diagonal-composite theorem (Proposition 1), no separation-of-arguments equivalence (Exercise 3), no many-factor composition (Exercise 4), no exhibited counterexample to composition (Exercise 5), and no general many-variable rule (Exercise 6). The class is never instantiated, and there is no three-variable functor `C × C^op × C ⟶ B` in-tree.

## Work to be done
- Prove remark 1: for dinatural `α : S ⟹ T` and natural (in both arguments) `σ : S' ⟹ S`, `τ : T ⟹ T'`, the componentwise `τ ∘ α ∘ σ` is dinatural.
- Prove Proposition 1 (the diagonal composite of a natural-in-`c`/dinatural-in-`d` family with another is natural) over a three-variable functor, and extend to an odd number of factors (Exercise 4).
- Prove Exercise 3 (joint dinaturality ⟺ separate dinaturality per factor) and exhibit Exercise 5 (a concrete pair `b ⟹ S`, `S ⟹ b'` with no well-defined composite). Record the general many-variable rule (Exercise 6) generalizing 3 and 4.
- Suggested module: `Theory/Dinatural/Composition.v`. In-tree donors: `Theory/Dinatural.v`, `Theory/Natural/Transformation.v`, and the multi-variable framework (the IX.4 multi-variable issue).

## Definition of Done
- [ ] Remark 1, Proposition 1, Exercises 3–6 all formalized (Exercise 5 as an explicit counterexample).
- [ ] All (non-)composition laws in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the diagonal-composite theorem and the whiskering lemma.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Theory/Dinatural/Composition.v` compiles.
- `Print Assumptions <diagonal_composite_natural>.` and `<dinatural_whisker_natural>.` closed.
- nix build targets pass.
- Reviewer confirms each result matches Mac Lane §IX.4 (remark, Proposition 1, Exercises 3–6).

## Dependencies
Depends on: maclane:IX.4:def4

<!-- catalog: {"ids":["maclane:IX.4:remark1","maclane:IX.4:prop1","maclane:IX.4:ex3","maclane:IX.4:ex4","maclane:IX.4:ex5","maclane:IX.4:ex6"],"deps":["maclane:IX.4:def4"]} -->

---8<---

title: "MacLane IX.4: Euclidean self-duality as a dinatural transformation"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.4:construction1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.4, the Euclidean-space example, book p. 220 (PDF p. 227). Item: `maclane:IX.4:construction1`.

## Background
Let `Euclid` be the category of real inner-product spaces and inner-product-preserving linear maps, with forgetful `U : Euclid ⟶ Vect_ℝ` and dual `* : Euclid^op ⟶ Vect_ℝ`; the Riesz isomorphisms `κ_E : E ⟶ E*` are the components of a dinatural transformation `κ : U ⟹ *`, expressing that each Euclidean space is naturally isomorphic to its dual (a type-2 dinatural example). See nLab [dinatural transformation](https://ncatlab.org/nlab/show/dinatural+transformation) and Wikipedia [Riesz representation theorem](https://en.wikipedia.org/wiki/Riesz_representation_theorem).

## Current state in the library
Absent. There is no category of Euclidean/inner-product spaces in-tree (no bilinear/symmetric/positive-definite form anywhere in `Instance/`), and the `Dinatural` class (`Theory/Dinatural.v:51`) has no instances. A search for `euclid`/`inner product`/`dual space` returned only unrelated prose about the natural double-dual of a vector space (`Theory/Natural/Transformation.v:46`, `Construction/Opposite.v:51`).

## Work to be done
- Build (or assume, in the `Instance/` layer over Coq's real numbers) the category `Euclid` of finite-dimensional real inner-product spaces and inner-product-preserving maps, the forgetful `U : Euclid ⟶ Vect_ℝ`, and the dual `* : Euclid^op ⟶ Vect_ℝ`.
- Construct the Riesz component maps `κ_E` and assemble them as a `Dinatural` instance `κ : U ⟹ *`, discharging the dinaturality hexagon.
- Suggested module: `Instance/Euclid.v` (and `Instance/Euclid/Dinatural.v`). In-tree donors: `Theory/Dinatural.v`; a real vector-space category is a prerequisite and may itself require new `Instance/` code.

## Definition of Done
- [ ] `Euclid`, `U`, `*`, and the dinatural `κ : U ⟹ *` constructed with the hexagon proved.
- [ ] Dinaturality in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom` introduced; `Print Assumptions` inspected — any axioms are the documented `Instance/`-layer stdlib ones (e.g. real-number axioms) per docs/AXIOMS.md, and no new axioms are added.
- [ ] File(s) registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Instance/Euclid/Dinatural.v` compiles.
- `Print Assumptions <euclid_riesz_dinatural>.` shows only documented instance-layer axioms.
- nix build targets pass.
- Reviewer confirms the construction matches Mac Lane §IX.4 (Euclidean self-duality as a dinatural `U ⟹ *`).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.4:construction1"],"deps":[]} -->

---8<---

title: "MacLane IX.5: The end–limit correspondence (subdivision and twisted-arrow categories)"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.5:construction1, maclane:IX.5:prop1, maclane:IX.5:prop3, maclane:IX.6:ex3]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.5 "Ends" (the subdivision category and Propositions 1 and 3, book p. 224–225, PDF p. 231–232) and §IX.6 Exercise 3 (the twisted arrow category, book p. 227, PDF p. 234). Items: `maclane:IX.5:construction1` (subdivision category and `S`-section functor), `maclane:IX.5:prop1` (end = limit of the `S`-section), `maclane:IX.5:prop3` (every limit is an end), `maclane:IX.6:ex3` (the twisted arrow category gives the same reduction).

## Background
Every end reduces to an ordinary limit: cones over the `S`-section functor on the subdivision category of `C` correspond exactly to wedges over `S`, so `∫_c S(c,c) ≅ Lim(S§)`; the twisted arrow category `Tw(C)` (objects the arrows of `C`, morphisms the twisted commuting squares) gives an alternative diagram achieving the same. Conversely, every limit is an end: `Lim T = ∫_c T(c)` for `S = T ∘ Q` the second projection. See nLab [end](https://ncatlab.org/nlab/show/end) and [twisted arrow category](https://ncatlab.org/nlab/show/twisted+arrow+category).

## Current state in the library
Absent. No subdivision (section) category is built — `Instance/Fact.v` is the factorization category `Fact(f)` of a *single* morphism, not Mac Lane's `C§` whose objects are all `c§` and `f§` — and no twisted-arrow category exists (the only `twisted` hits are a Wikipedia cross-reference in `Instance/Fact.v:10` and an unrelated Grothendieck hit). The end/coend files (`Structure/End.v`, `Structure/Coend.v`, `Theory/Coend/Yoneda.v`, `Theory/Coend/Fubini.v`) require no `Limit` machinery and state no `∫_c S(c,c) ≅ Lim` isomorphism, nor the "every limit is an end" (second-projection) reduction.

## Work to be done
- Construct the subdivision category `C§` (objects `c§` and `f§`; for each `f : b ⟶ c`, arrows `b§ ⟶ f§ ⟵ c§`) and the functor `S§` (`c§ ↦ S(c,c)`, `f§ ↦ S(b,c)`, legs `S(b,f)`, `S(f,c)`); prove cones over `S§` = wedges over `S`, giving `∫_c S(c,c) ≅ Lim(S§)` (Proposition 1) with the comparison an isomorphism.
- Construct the twisted arrow category `Tw(C)` and the functor to `C^op ∏ C`, and prove cones over `S∘K` = wedges over `S`, re-establishing the reduction (Exercise 3).
- Prove Proposition 3 (`Lim T = ∫_c T(c)` for `S = T ∘ Q`, `Q` the second projection).
- Suggested modules: `Construction/Subdivision.v`, `Construction/TwistedArrow.v`, `Structure/End/Limit.v`. In-tree donors: `Structure/End.v`, `Structure/Wedge.v`, `Structure/Limit.v`, `Structure/Cone.v`, `Instance/Fact.v`.

## Definition of Done
- [ ] `C§`, `S§`, `Tw(C)` built; `∫_c S(c,c) ≅ Lim(S§)` and the twisted-arrow variant proved; every-limit-is-an-end proved.
- [ ] Isomorphisms via `≅` in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `end_is_limit` and `limit_is_end`.
- [ ] Files registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/End/Limit.v` compiles.
- `Print Assumptions end_is_limit.` and `Print Assumptions limit_is_end.` closed.
- nix build targets pass.
- Reviewer confirms the statements match Mac Lane §IX.5 Propositions 1 and 3 and §IX.6 Exercise 3.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.5:construction1","maclane:IX.5:prop1","maclane:IX.5:prop3","maclane:IX.6:ex3"],"deps":[]} -->

---8<---

title: "MacLane IX.5: Existence of ends from completeness and from products and equalizers"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.5:cor2, maclane:IX.6:ex2]
deps_item_ids: [maclane:IX.5:prop1]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.5 Corollary 2 (book p. 224, PDF p. 231) and §IX.6 Exercise 2 (book p. 227, PDF p. 234). Items: `maclane:IX.5:cor2` (a small-complete category has all small ends), `maclane:IX.6:ex2` (ends built directly from products and equalizers).

## Background
If `X` is small-complete and `C` is small then every `S : C^op × C ⟶ X` has an end (the limit of its `S`-section); and, mirroring the products-plus-equalizers construction of limits, a category with all small products and all equalizers has all small ends directly. See nLab [end](https://ncatlab.org/nlab/show/end).

## Current state in the library
Partial. Ends exist unconditionally in `Set` by direct construction (`Instance/Sets/End.v:144`, `Sets_End`, the setoid of compatible families) — the corollary's conclusion at `X = Set` — but there is no general theorem "`X` small-complete ⟹ every `S` has an end"; `Structure/Complete.v` carries completeness only as a hypothesis and derives no end existence. A blind search found no "products + equalizers ⟹ ends" construction over an abstract `X`; the only concrete end is the bespoke `Set` subsetoid, and the "end = limit" reduction it would rest on is the subject of the §IX.5 end–limit correspondence issue.

## Work to be done
- Prove `X` small-complete ∧ `C` small ⟹ every `S : C^op ∏ C ⟶ X` has an end, via the end-as-limit-of-`S§` correspondence (the §IX.5 correspondence issue) plus completeness.
- Prove directly (Exercise 2) that a category with all small products and all equalizers has all small ends, mirroring the limit construction — i.e. the end as an equalizer of two maps between products.
- Suggested module: `Structure/End/Existence.v`. In-tree donors: `Structure/End.v`, `Structure/Complete.v`, `Structure/Limit/Product.v`, `Structure/Equalizer.v`, and the end–limit correspondence issue.

## Definition of Done
- [ ] Both existence theorems proved (via completeness; via products + equalizers).
- [ ] Statements in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `complete_has_ends` and `products_equalizers_has_ends`.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/End/Existence.v` compiles.
- `Print Assumptions complete_has_ends.` closed.
- nix build targets pass.
- Reviewer confirms the statements match Mac Lane §IX.5 Corollary 2 and §IX.6 Exercise 2.

## Dependencies
Depends on: maclane:IX.5:prop1

<!-- catalog: {"ids":["maclane:IX.5:cor2","maclane:IX.6:ex2"],"deps":["maclane:IX.5:prop1"]} -->

---8<---

title: "MacLane IX.5: The set of natural transformations is an end of the hom-functor"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.5:remark1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.5 (the `Nat = ∫ hom` identity, eq. 2), book p. 223 (PDF p. 230). Item: `maclane:IX.5:remark1`.

## Background
For functors `U, V : C ⟶ X`, the bifunctor `hom_X(U-, V-) : C^op × C ⟶ Set` has a wedge from a set `Y` exactly a `Y`-indexed natural family, so the set of natural transformations is an end: `Nat(U,V) = ∫_c hom_X(Uc, Vc)`. See nLab [end](https://ncatlab.org/nlab/show/end) and Wikipedia [End (category theory)](https://en.wikipedia.org/wiki/End_(category_theory)).

## Current state in the library
Partial. `Theory/Coend/Yoneda.v` formalizes the special case `U = C(c,-)` a representable and `X = Set`: the integrand `YoE (x,y) = [C(c,x), F y]` (`Theory/Coend/Yoneda.v:186`) is the hom-bifunctor, and its `Set`-end is `≅ F c` (`yoneda_reduction`, `Theory/Coend/Yoneda.v:297`), with end-elements identified as natural families `C(c,-) ⟹ F`. But there is no standalone hom-bifunctor `hom(U-, V-)` for two arbitrary functors `U, V : C ⟶ X`, and no general theorem `Nat(U,V) ≅ ∫_c hom(Uc, Vc)`.

## Work to be done
- Construct the hom-bifunctor `hom_X(U-, V-) : C^op ∏ C ⟶ Set` for arbitrary `U, V : C ⟶ X`.
- Prove `Nat(U,V) ≅ ∫_c hom_X(Uc, Vc)` (a wedge to `hom(U-,V-)` is exactly an indexed natural family), recovering the representable/`Set` case of `Theory/Coend/Yoneda.v` as an instance.
- Suggested module: `Structure/End/Nat.v`. In-tree donors: `Functor/Hom.v`, `Structure/End.v`, `Structure/Wedge.v`, `Theory/Natural/Transformation.v`, `Theory/Coend/Yoneda.v`.

## Definition of Done
- [ ] The hom-bifunctor for arbitrary `U,V` and the `Nat(U,V) ≅ ∫_c hom(Uc,Vc)` isomorphism proved.
- [ ] Isomorphism via `≅` in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `Nat_is_end`.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/End/Nat.v` compiles.
- `Print Assumptions Nat_is_end.` closed.
- nix build targets pass.
- Reviewer confirms the statement matches Mac Lane §IX.5 eq. (2).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.5:remark1"],"deps":[]} -->

---8<---

title: "MacLane IX.5: Preservation and creation of ends; hom-functors are continuous for ends"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.5:def2, maclane:IX.5:remark2]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.5, the preserve/create-an-end definition and the hom-continuity remark (eqs. 4–5), book p. 225 (PDF p. 232). Items: `maclane:IX.5:def2` (preservation and creation of an end), `maclane:IX.5:remark2` (hom-functors preserve/reverse ends).

## Background
A functor `H : X ⟶ Y` *preserves* the end of `S` when `H` carries an ending wedge to an ending wedge (`H ∫_c S(c,c) ≅ ∫_c H S(c,c)`) and *creates* it when every wedge into `HS` lifts uniquely to an end of `S`; in particular covariant hom-functors preserve ends, `X(x, ∫_c S) ≅ ∫_c X(x, S)`, and contravariant hom sends a coend to an end, `X(∫^c S, x) ≅ ∫_c X(S, x)`. See nLab [end](https://ncatlab.org/nlab/show/end).

## Current state in the library
Absent. A blind search for `PreservesEnd`/`CreatesEnd`/end-preservation returned no such predicate; `Structure/Limit/Preservation.v` provides `PreservesLimit`/`CreatesLimit` for ordinary limits only, with no wedge/end analogue. The end/coend files (`Structure/End.v`, `Structure/Coend.v`, `Theory/Coend/Yoneda.v`, `Theory/Coend/Fubini.v`) prove no `hom(x, ∫S) ≅ ∫ hom(x, Sc)` isomorphism; representable-continuity exists in-tree only for ordinary limits.

## Work to be done
- Define `PreservesEnd` and `CreatesEnd` (the wedge-lifting formulation) for a functor `H : X ⟶ Y`, mirroring `Structure/Limit/Preservation.v`; dualize for coends.
- Prove hom-continuity: covariant `X(x,-)` preserves ends (`X(x, ∫_c S) ≅ ∫_c X(x, S(c,c))`) and contravariant `X(-,x)` sends a coend to an end (`X(∫^c S, x) ≅ ∫_c X(S(c,c), x)`).
- Suggested module: `Structure/End/Preservation.v`. In-tree donors: `Structure/End.v`, `Structure/Coend.v`, `Structure/Wedge.v`, `Structure/Limit/Preservation.v`, `Functor/Hom.v`.

## Definition of Done
- [ ] `PreservesEnd`/`CreatesEnd` defined; both hom-continuity isomorphisms proved.
- [ ] Isomorphisms via `≅` in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `hom_preserves_end` and `hom_coend_to_end`.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/End/Preservation.v` compiles.
- `Print Assumptions hom_preserves_end.` closed.
- nix build targets pass.
- Reviewer confirms the definitions and continuity isos match Mac Lane §IX.5 (eqs. 4–5).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.5:def2","maclane:IX.5:remark2"],"deps":[]} -->

---8<---

title: "MacLane IX.6: The tensor product of functors as a coend"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.6:def2, maclane:IX.6:ex5]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.6, the tensor product of functors (book p. 226–227, PDF p. 233–234) and Exercise 5 (book p. 227, PDF p. 234). Items: `maclane:IX.6:def2` (`T □_P S = ∫^P Tp □ Sp` over a monoidal base), `maclane:IX.6:ex5` (`∫^c Sc · Tc` over a cocomplete category).

## Background
For a monoidal category `(B, □)` and functors `T : P^op ⟶ B`, `S : P ⟶ B`, the tensor product of functors is the coend `T □_P S = ∫^P Tp □ Sp`; the copower variant `∫^c Sc · Tc`, for `S : C^op ⟶ Set` and `T : C ⟶ D` with `D` cocomplete, is a functor `Set^{C^op} × D^C ⟶ D`. See nLab [tensor product of functors](https://ncatlab.org/nlab/show/tensor+product+of+functors).

## Current state in the library
Partial. The coend shape appears only specialized to `B = Set` with `□ = ×`, embedded inside profunctor composition (`Construction/Profunctor/Compose.v:95`, `∫^d P(c,d) × Q(d,e)`) and, differently, Day convolution (`Construction/Day.v:315`); `Functor/Product.v:30` explicitly flags that the general coend tensor of functors is *not* the pointwise construction there. There is no standalone `T □_P S = ∫^P Tp □ Sp` over an arbitrary monoidal base, and no copower `∫^c Sc · Tc` over a cocomplete `D` (copowers/tensoring by a set are themselves undeveloped).

## Work to be done
- Define the functor tensor product `T □_P S := ∫^P Tp □ Sp` over an arbitrary monoidal base `(B, □)`, using the existing `Coend`.
- Develop copowers `S · A` (a `Set`-indexed coproduct of copies) and define `∫^c Sc · Tc` for `S : C^op ⟶ Set`, `T : C ⟶ D` with `D` cocomplete; prove it is a bifunctor `Set^{C^op} ∏ D^C ⟶ D`.
- Suggested module: `Construction/FunctorTensor.v`. In-tree donors: `Structure/Coend.v`, `Structure/Monoidal.v`, `Construction/Profunctor/Compose.v`, `Construction/Day.v`, `Structure/Limit.v` (for copowers).

## Definition of Done
- [ ] `T □_P S` over a monoidal base and the copower `∫^c Sc · Tc` over a cocomplete `D` defined; bifunctoriality of the copower version proved.
- [ ] All coend UMP uses in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the functor tensor product.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Construction/FunctorTensor.v` compiles.
- `Print Assumptions <functor_tensor>.` closed.
- nix build targets pass.
- Reviewer confirms the definitions match Mac Lane §IX.6 (`T □_P S`; Exercise 5).

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.6:def2","maclane:IX.6:ex5"],"deps":[]} -->

---8<---

title: "MacLane IX.6: Module tensor products and free modules as coends"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.6:remark1, maclane:IX.6:ex4]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.6, the module-tensor coend (book p. 226, PDF p. 233) and Exercise 4 (book p. 227, PDF p. 234). Items: `maclane:IX.6:remark1` (`A ⊗_R B = ∫^R A ⊗ B`), `maclane:IX.6:ex4` (the free `R`-module on a set as `∫^n X^n · R_{(n)}`).

## Background
Viewing a ring `R` as a one-object `Ab`-category, a left module is an additive functor `R ⟶ Ab` and a right module an additive functor `R^op ⟶ Ab`; the coend `∫^R A ⊗ B` is the usual tensor product `A ⊗_R B`. Over the skeletal category of finite ordinals, the free `R`-module on a set `X` is the coend `∫^n X^n · R_{(n)}`, recovering elements as finite formal sums. See nLab [end](https://ncatlab.org/nlab/show/end) (coend) and Wikipedia [Tensor product of modules](https://en.wikipedia.org/wiki/Tensor_product_of_modules).

## Current state in the library
Absent. There is no category of modules in-tree — `R-Mod` is the subject of filed issue #258, and a blind search found only prose mentions (`Structure/Coend.v:94` gives the analogy `F ⊗_C G ≅ ∫^c Fc ⊗ Gc` in a background essay; `Structure/Abelian.v`/`Structure/Monoid.v` cite `R-Mod` as motivation) — and no ring-as-`Ab`-category, no `A ⊗_R B`, and no free-module construction. The coend machinery itself exists (`Structure/Coend.v`, `Instance/Sets/Coend.v`), and copowers/tensoring-by-a-set (needed for Exercise 4) are undeveloped. The module tensor product built via the adjoint functor theorem is filed separately (#449); this issue supplies the alternative coend characterization.

## Work to be done
- Over the `R-Mod` category (#258): present a ring as a one-object `Ab`-category and modules as additive functors, and prove `∫^R A ⊗ B ≅ A ⊗_R B` (the coend is `A ⊗ B` modulo the `ar ⊗ b − a ⊗ rb` relations).
- Prove the free `R`-module on `X` is the coend `∫^n X^n · R_{(n)}` over the skeletal finite-ordinal category, with `R_{(n)} = R^n` and the fibre-sum action, recovering finite formal sums (uses copowers, cf. the IX.6 functor-tensor issue).
- Suggested module: `Instance/Module/Coend.v`. In-tree donors: `Structure/Coend.v`, `Instance/Sets/Coend.v`, `Instance/FinSet.v`, the `R-Mod` category (#258).

## Definition of Done
- [ ] `A ⊗_R B ≅ ∫^R A ⊗ B` and the free-module coend proved.
- [ ] Isomorphisms via `≅` in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed (any stdlib axioms are the documented instance-layer ones per docs/AXIOMS.md).
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Instance/Module/Coend.v` compiles.
- `Print Assumptions <module_tensor_coend>.` closed (modulo documented instance-layer axioms).
- nix build targets pass.
- Reviewer confirms the statements match Mac Lane §IX.6 (module tensor coend; Exercise 4).

## Dependencies
Depends on: #258

<!-- catalog: {"ids":["maclane:IX.6:remark1","maclane:IX.6:ex4"],"deps":["#258"]} -->

---8<---

title: "MacLane IX.7: Functoriality of ends in the integrand"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.7:prop1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.7 "Ends with Parameters", Proposition 1 (eqs. 1–2), book p. 228 (PDF p. 235). Item: `maclane:IX.7:prop1`.

## Background
A transformation `γ : S ⟹ S'` between functors with ends induces a unique arrow `∫_c γ_{c,c} : ∫ S ⟶ ∫ S'` with `ω'_c ∘ ∫γ = γ_{c,c} ∘ ω_c`, and `∫(γ' ∘ γ) = (∫γ') ∘ (∫γ)` — taking ends is functorial in the integrand. See nLab [end](https://ncatlab.org/nlab/show/end).

## Current state in the library
Partial. The general coend UMP `coend_med` (`Structure/Coend.v:190`, with `coend_med_inj` at `:196` giving the commuting law) is the tool that makes an induced map well-defined, and it is used ad hoc to build induced coend maps with identity and composition laws in `Construction/Day.v` (`DFG_c` via `DFG_theta`, with `DFG_theta_id`/`DFG_theta_comp` at `:780`, assembled into the bifunctor `Day_Tensor`). But there is no general lemma packaging `(S ⟹ S') ↦ (End S ⟶ End S')` / `(Coend S ⟶ Coend S')` with the commuting equation and functor laws; the instances are coend-only and `Set`-only, and the end-native form is absent.

## Work to be done
- Prove the general "functoriality of ends": for `γ : S ⟹ S'` with `⟨e,ω⟩`, `⟨e',ω'⟩` ends, a unique `∫γ : e ⟶ e'` with `ω'_c ∘ ∫γ ≈ γ_{c,c} ∘ ω_c`, and the identity/composition laws; dualize for coends, subsuming the `Construction/Day.v` ad hoc instances.
- Package `∫ : [C^op ∏ C, X] ⟶ X` as a functor where ends exist.
- Suggested module: `Structure/End/Functorial.v`. In-tree donors: `Structure/End.v`, `Structure/Coend.v` (`coend_med`), `Construction/Day.v`.

## Definition of Done
- [ ] `∫γ` and the functor laws proved in general (end-native), with the coend dual.
- [ ] Commuting equations in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `end_fmap` and its functor laws.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/End/Functorial.v` compiles.
- `Print Assumptions end_fmap.` closed.
- nix build targets pass.
- Reviewer confirms the statement matches Mac Lane §IX.7 Proposition 1.

## Dependencies
None.

<!-- catalog: {"ids":["maclane:IX.7:prop1"],"deps":[]} -->

---8<---

title: "MacLane IX.7: The Parameter Theorem for ends and coends"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.7:thm2, maclane:IX.7:thm3, maclane:IX.7:ex2, maclane:IX.7:ex4]
deps_item_ids: [maclane:IX.7:prop1]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.7 Theorems 2 and 3 and Exercises 2 and 4, book p. 228–229 (PDF p. 235–236). Items: `maclane:IX.7:thm2` (parametrized end assembles into a functor), `maclane:IX.7:thm3` (it is the end computed in `X^P`), `maclane:IX.7:ex2` (the coend dual), `maclane:IX.7:ex4` (the discrete-subcategory inclusion creates ends and coends).

## Background
If `T : P × C^op × C ⟶ X` has an end `∫_c T(p,c,c)` for each `p`, these assemble into a unique functor `U : P ⟶ X` with the wedge components natural in `p` (Theorem 2), and `U` is the end of the transpose `T̂ : C^op × C ⟶ X^P` computed in the functor category (Theorem 3); dually for coends (Exercise 2), and the inclusion `X^P ⟶ X^{|P|}` of the discrete subcategory creates ends and coends (Exercise 4). See nLab [end](https://ncatlab.org/nlab/show/end).

## Current state in the library
Partial. The "parametrized coend is a functor" conclusion is realized concretely in `Set` by three hand-built integrands — `Inner` (`Theory/Coend/Fubini.v:226`), `Day` (`Construction/Day.v:315`), `prof_compose` (`Construction/Profunctor/Compose.v:267`) — each a functor whose value is a coend and whose `fmap` is the coend mediator (so the coinjections are natural in the parameter). But there is no general theorem hypothesizing pointwise fibre-end existence over an arbitrary `P` and `X`; Theorem 3's "is an end in `X^P`" refinement is entirely absent (no ends valued in functor categories exist), and hence Exercise 4's creation statement is unformable in-tree.

## Work to be done
- Prove Theorem 2: from pointwise ends of `T(p,-,-)`, assemble the unique functor `U : P ⟶ X` with `U p = ∫_c T(p,c,c)` and the wedge natural in `p` (using functoriality of ends, the §IX.7 functoriality issue).
- Prove Theorem 3: `U` is the end of the transpose `T̂` in `X^P`, with `(ω̂_c)_p = (ω_p)_c`; state and prove the coend dual (Exercise 2).
- Prove Exercise 4: `X^P ⟶ X^{|P|}` creates ends and coends.
- Suggested module: `Structure/End/Parameter.v`. In-tree donors: `Structure/End.v`, `Structure/Coend.v`, `Instance/Fun.v`, the §IX.7 functoriality issue, and the concrete `Set` witnesses (`Theory/Coend/Fubini.v`, `Construction/Day.v`).

## Definition of Done
- [ ] Theorems 2 and 3, the coend dual, and the creation exercise proved (end-native, arbitrary `X`).
- [ ] Naturality/end conditions in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `end_parameter_functor` and `end_in_functor_category`.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Structure/End/Parameter.v` compiles.
- `Print Assumptions end_parameter_functor.` closed.
- nix build targets pass.
- Reviewer confirms the statements match Mac Lane §IX.7 Theorems 2–3 and Exercises 2, 4.

## Dependencies
Depends on: maclane:IX.7:prop1

<!-- catalog: {"ids":["maclane:IX.7:thm2","maclane:IX.7:thm3","maclane:IX.7:ex2","maclane:IX.7:ex4"],"deps":["maclane:IX.7:prop1"]} -->

---8<---

title: "MacLane IX.7: A limit in a functor category that is not pointwise (Dubuc)"
labels: [book:maclane, kind:exercise, coverage-gap]
projects: [4]
covers: [maclane:IX.7:ex1]
deps_item_ids: []
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.7 Exercise 1 (Dubuc), book p. 229 (PDF p. 236). Item: `maclane:IX.7:ex1`.

## Background
Not every limit in a functor category `X^P` is computed pointwise: there is a functor `T : C ⟶ X^P` (suggestion `C = 2`) whose limit is not the pointwise limit — a counterexample delimiting the pointwise-limit theorems. See nLab [functor category](https://ncatlab.org/nlab/show/functor+category).

## Current state in the library
Absent. There is no functor-category pointwise-limit counterexample in-tree; `Structure/Cartesian/Product.v` remarks in prose that product categories inherit limits pointwise, and pointwise limits in functor categories are filed as #425, but no Dubuc-style non-pointwise example is constructed.

## Work to be done
- Construct the specific `X`, `P`, and functor `T : 2 ⟶ X^P` and exhibit a limit of `T` in `X^P` that differs from the pointwise limit (or show the pointwise limit fails to exist while the limit exists).
- Suggested module: `Instance/Fun/NonPointwiseLimit.v`. In-tree donors: `Instance/Fun.v`, `Structure/Limit.v`, and the pointwise-limit development (#425) for contrast.

## Definition of Done
- [ ] The counterexample constructed and the non-pointwiseness proved.
- [ ] Statements in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the counterexample witness.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.

## Verification
- `coqc -R . Category Instance/Fun/NonPointwiseLimit.v` compiles.
- `Print Assumptions <dubuc_non_pointwise_limit>.` closed.
- nix build targets pass.
- Reviewer confirms the example matches Mac Lane §IX.7 Exercise 1 (a functor-category limit that is not pointwise).

## Dependencies
Depends on: #425

<!-- catalog: {"ids":["maclane:IX.7:ex1"],"deps":["#425"]} -->

---8<---

title: "MacLane IX.8: The Fubini theorem and interchange of iterated ends"
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:IX.8:prop1, maclane:IX.8:cor1]
deps_item_ids: [maclane:IX.7:thm2]
deps_pending: []

## Source
Mac Lane, *CWM* (2nd ed.), §IX.8 "Iterated Ends and Limits", the unnumbered Proposition (Fubini) and Corollary, book p. 230–231 (PDF p. 237–238). Items: `maclane:IX.8:prop1` (double end = iterated end), `maclane:IX.8:cor1` (interchange of iterated ends).

## Background
For `S : P^op × P × C^op × C ⟶ X` whose inner end exists for all parameter pairs, the double end equals the iterated end, `∫_{⟨p,c⟩} S(p,p,c,c) ≅ ∫_p ∫_c S(p,p,c,c)` (Fubini), and consequently the two iteration orders agree, `∫_p ∫_c ≅ ∫_c ∫_p` (the corollary). See nLab [end](https://ncatlab.org/nlab/show/end) (the Fubini section) and the nLab [Fubini theorem](https://ncatlab.org/nlab/show/Fubini+theorem) disambiguation.

## Current state in the library
Partial. `Theory/Coend/Fubini.v:449` proves `coend_fubini : ∫^{(c,d)} H ≅ ∫^c ∫^d H` in `Set` with both round trips (`fubini_to_from`/`fubini_from_to`), where the outer functor `Inner` (`Theory/Coend/Fubini.v:226`) is defined for all parameter pairs — faithfully matching the book's for-all-pairs hypothesis — but the file's own SCOPE note defers the abstract statement over an arbitrary cocomplete `X` (ledger 6), and there is no end-native witness (only the `Coend := End^op` duality). The interchange corollary `∫^c ∫^d ≅ ∫^d ∫^c` is absent: it requires composing `coend_fubini` with a product-swap `C ∏ D ≅ D ∏ C`, which is not performed anywhere.

## Work to be done
- Prove the Fubini theorem end-natively and over an arbitrary complete `X` (lifting the `Set`-coend `coend_fubini` scope restriction): `∫_{⟨p,c⟩} S ≅ ∫_p ∫_c S`, with the comparison an isomorphism, under the inner-end-for-all-pairs hypothesis (using the Parameter Theorem, the §IX.7 parameter issue).
- Derive the interchange corollary `∫_p ∫_c ≅ ∫_c ∫_p` by composing Fubini with the product-swap isomorphism; dualize for coends.
- Suggested module: `Structure/End/Fubini.v` (end-native) extending `Theory/Coend/Fubini.v`. In-tree donors: `Theory/Coend/Fubini.v`, `Structure/End.v`, `Construction/Product.v` (the swap), and the Parameter Theorem issue.

## Definition of Done
- [ ] Fubini (double = iterated) and the interchange corollary proved, end-native and over general complete `X`; the `Set`-coend result recovered.
- [ ] Isomorphisms via `≅` in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for `end_fubini` and `end_interchange`.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.
- [ ] If flagship-level, update the CLAUDE.md Key Files coend-calculus note to record the end-native Fubini/interchange.

## Verification
- `coqc -R . Category Structure/End/Fubini.v` compiles.
- `Print Assumptions end_fubini.` and `Print Assumptions end_interchange.` closed.
- nix build targets pass.
- Reviewer confirms the statements match Mac Lane §IX.8 Proposition and Corollary (for-all-pairs hypothesis; both iteration orders isomorphic).

## Dependencies
Depends on: maclane:IX.7:thm2

<!-- catalog: {"ids":["maclane:IX.8:prop1","maclane:IX.8:cor1"],"deps":["maclane:IX.7:thm2"]} -->
