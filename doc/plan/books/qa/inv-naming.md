# Naming investigation — decisions 3.2, 3.3, 4.3

Read-only investigation. No issue bodies or repo files were edited. Line numbers
cited as `Ln` are 1-indexed lines of the **issue body as returned by the GitHub
API** (`gh issue view N --json body`), not of any file. File line numbers are
cited as `path:NN` and were verified against the working tree at
`8e199145` (branch `johnw/rocq-dev-ci`).

Corpus: 845 issues (`gh issue list --state all --limit 2000`), all OPEN among
the hits below.

---

## (a) Decision 3.3 — the `Graph` clash

### The question

DECISIONS.md row 3.3 reads verbatim:

> | 3.3 `Graph` clash | **[+] Rename #705's** directed-graph category (to `Quiver` if no clash with the existing in-tree quiver notion, else `DiGraph`); #926 keeps `Graph` |

So the gate is: *does `Quiver` clash?*

### Answer: `Quiver` clashes, three ways. Recommend **`DiGraph`**.

**Clash 1 — `Quiver` is already a Coq identifier in the tree.**
`Construction/Free/Quiver.v:54`:

```coq
  Class Quiver@{o h p} := {
      nodes : Type@{o};                          (* vertices / objects *)
      uedges := Type@{h} : Type@{h+1};           (* universe of edge sets *)
      edges : nodes → nodes → uedges;            (* arrows, indexed by source and target *)
      edgeset : ∀ X Y, Setoid@{h p} (edges X Y)  (* each edge set is a setoid (≈) *)
    }.
```

The file is registered (`_CoqProject:72`, `Construction/Free/Quiver.v`) and the
identifier is global — the class is declared inside `Section Quiver`, which ends
at `:192`, so `Quiver` escapes the section. A second global `Quiver`, whether a
`Class` or a `Category` instance, would shadow or conflict on import.

**Clash 2 — the *category* of quivers already exists under a name of that
family.** `Construction/Free/Quiver.v:358`:

```coq
#[export] Instance QuiverCategory : Category.
```

with `Class QuiverHomomorphism` at `:205`. The file header
(`Construction/Free/Quiver.v:31-32`) says verbatim:

> `Quivers and their homomorphisms form the category`
> `[QuiverCategory] (the Quiv of the literature); morphism equivalence is`

and two in-tree comments already use the short name `Quiv` for it —
`Instance/StrictCat.v:51`:

> `[Category.Construction.Free.Quiver.Forgetful : StrictCat ⟶ Quiv], the`

and `Instance/StrictCat/ToCat.v:29`:

> `[Construction.Free.Quiver.Forgetful : StrictCat ⟶ Quiv] — therefore cannot`

**Clash 3 — the issue corpus already uses bare `Quiver` to mean
`QuiverCategory`, in two issue *titles*.**

- #962 title: `Riehl 3.6: Completeness and cocompleteness of Quiver and rQuiver, and the failure for Graph`
- #993 title: `Riehl 5.1/5.5: The free-category monad on quivers, and the monadicity of Cat over Quiver`

and inside those bodies, e.g. #962 L54:

> `- [ ] \`Quiver\` is identified with a presheaf category and its (co)completeness derived, not assumed`

Assigning `Quiver` to #705's *new* category would make these two titles mean the
wrong object.

### Is #705's category "literally the category of quivers"?

**Yes, mathematically — which is exactly why the name is unavailable rather than
available.** #705 L46-48 asks for:

> `1. Define the "two sets plus source/target" presentation of a graph as a`
> `   category \`Graph\` in \`Sets\` (objects: \`G₁, G₀\` with \`s, t : G₁ → G₀\`;`
> `   morphisms: pairs making both squares commute, with \`≈\` for the commutation).`

That is the standard (G₀, G₁, s, t) presentation of a **directed multigraph =
quiver**. #705's own body says so at L26-30:

> `A directed graph — the nLab's [quiver](https://ncatlab.org/nlab/show/quiver) —`
> `is a pair of sets with source and target maps`

and #705 L53-55 requires a comparison *to* the existing one:

> `3. Relate the indexed-family presentation to the source/target presentation:`
> `   build the comparison functor between \`Construction/Free/Quiver.v:358\`'s`
> `   \`QuiverCategory\` and \`Graph\` and prove it full and faithful`

So the two are two **presentations of the same notion**. Naming the new one
`Quiver` would render that DoD line as "the comparison functor between
`QuiverCategory` and `Quiver`", which is unreadable, and would put two objects
called `Quiver`/`QuiverCategory` in the same file's import closure.

`DiGraph` has **zero** hits in the tree (`grep -rnE '\b(DiGraph|Digraph|digraph)\b' --include='*.v' .` → no output) and **zero** hits across all 845 issue bodies and titles (case-insensitive). It is free.

### Recommendation

**`DiGraph`** for #705's source/target-presentation category, in
`Instance/Parallel/Graphs.v` (the module path #705 already proposes; it does not
collide with anything).

Secondary suggestion, for the coordinator to weigh: `Grph` is *also* free as an
identifier, but is already in use in the corpus for a **different** object —
Mac Lane's O-graphs. #294 L18 verbatim:

> `1. Define O-quivers (edge family over a fixed node type O) and their identity-on-nodes morphisms; the category O-Grph; the trivial O-graph (one edge per node, endpoints that node).`

and #328's title is `MacLane III.3: Coproducts in Mon and Grph`. So `Grph` would
import the same kind of ambiguity that `Quiver` does. `DiGraph` is the clean
choice.

### Blast radius — issues whose bodies would need updating

**Must change (the identifier is #705's own):**

| Issue | Body lines | Verbatim occurrence of the name being renamed |
|---|---|---|
| #705 | L47 | `   category \`Graph\` in \`Sets\` (objects: \`G₁, G₀\` with \`s, t : G₁ → G₀\`;` |
| #705 | L49 | `2. Prove \`Graph ≅ [Parallel^op, Sets]\` — ideally an isomorphism of categories,` |
| #705 | L54 | `   \`QuiverCategory\` and \`Graph\` and prove it full and faithful (state honestly` |
| #705 | L69 | `- [ ] \`Graph ≅ [Parallel^op, Sets]\` (or \`≃\`, with the weaker conclusion stated` |

Also in #705's Verification block (unnumbered above because it is inside a fenced
code block): `Print Assumptions Graph_Presheaf_iso.`,
`Print Assumptions Quiver_Graph_comparison.`, `Print Assumptions Graph_Closed.`
— three lemma names carrying the `Graph` prefix. Renaming the category should
rename these consistently (`DiGraph_Presheaf_iso`, `Quiver_DiGraph_comparison`,
`DiGraph_Closed`).

**Must change (they name #705's category from outside):**

| Issue | Body line | Verbatim | Why |
|---|---|---|---|
| #357 | L107 | `\`Quiver\` and \`Graph\`) is a different substrate and is filed separately.` | The full clause is `Clause (ii) of the same exercise (the vertex functors of \`Quiver\` and \`Graph\`)`. Here `Graph` is Riehl's *undirected* graph (that clause is #988's), and `Quiver` means `QuiverCategory`. **Ambiguous today and ambiguous after the rename** — worth disambiguating in the same pass, but it is *not* a reference to #705. |

**Must be re-checked but probably NOT changed** (these say `Graph`, meaning
#926's simple-graph category, which keeps the name):

| Issue | Body line | Verbatim |
|---|---|---|
| #926 | L27 | `1. Define the category \`Graph\` of **simple** graphs: … State in the header how this relates to the directed-graph presentation of #705 and to \`Construction/Free/Quiver.v\`'s \`Quiver\` — the two are different objects` |
| #926 | L38 | `- [ ] \`Graph\` is defined for **simple** graphs, and the header states precisely how it differs from \`Quiver\`/\`QuiverCategory\` and from #705's directed graphs` |
| #962 | L46 | `   deliverable; if the argument turns on loops, disclose the exact definition of \`Graph\` adopted in` |
| #962 | L57 | `- [ ] The \`Graph\` failure is a proved statement …, stated against the category of graphs of #926 rather than a second, rival one` |
| #988 | L18 | `- There is no category of undirected graphs in the tree at all (the \`Graph\` occurrences under \`Instance/Parallel.v\` and \`Structure/Monoidal/*\` are the parallel-pair shape and hypergraph vocabulary, not a graph category).` |

#926 L27 and L38 mention "#705's directed graphs" in prose without naming the
identifier; after the rename these read better if they say `DiGraph` explicitly,
but nothing is *wrong* today.

**No change (module paths only, `Graph` is a path component not a category):**
#788 L50 (`Instance/Cost/Graph.v`), #874 L22 (`Construction/Graph/Labelled.v`),
#926 L25/L54/L55 (`Instance/Graph.v`, `Instance/Graph/Colouring.v` — #926's own,
which it keeps).

### Adjacent finding the coordinator should see before acting

**#705's headline theorem is claimed by two other issues.** #705 L49 asks for
`Graph ≅ [Parallel^op, Sets]`. But:

- #962 L34: `   \`QuiverCategory ≃ [Parallel^op, Sets]\` (or an isomorphism if the encodings line up), and conclude`
- #979 L25: `1. Identify \`QuiverCategory\` with \`[Parallel^op, Sets]\` as an equivalence (or an isomorphism) of categories, using the identification already sketched in prose at \`Instance/Parallel.v:155-166\`.`
- #979 L70 (a QA correction already applied to that body): `> 1. Reuse the \`QuiverCategory ≃ [Parallel^op, Sets]\` equivalence built by #962 in \`Construction/Free/Quiver/Complete.v\`; do not rebuild it.`
- #895 L~ (Work item 1): `1. Build the topos of graphs as \`[Parallel^op, Sets]\`, or obtain it from the general presheaf-topos theorem (#404) once that lands`

So #962 is already designated the creator of `QuiverCategory ≃ [Parallel^op,
Sets]`. If #705 introduces `DiGraph` and separately proves
`DiGraph ≅ [Parallel^op, Sets]`, the corpus will contain two near-identical
theorems and *three* objects (`QuiverCategory`, `DiGraph`, `[Parallel^op,
Sets]`) pairwise compared. #988 L69 warns against exactly this:

> `If the presheaf presentation is introduced, relate it to the existing \`QuiverCategory\` rather than adding a third notion of quiver.`

The rename is still correct and should proceed; but the coordinator may want a
companion note on #705 pointing at #962/#979 as the owners of the presheaf
identification. **I am flagging, not deciding** — collapsing #705 into #962
would be a scope decision beyond this investigation's remit.

---

## (b) Decisions 3.2 + 4.3 — `Rng` / `Rig` / `Ring`

### The decisions, verbatim

> | 3.2 `Rng` clash | **Rig/Rng split**: the NON-unital category takes `Rng`; #257's unital one is renamed **`Ring`**. Header must disclose the clash |

> | 4.3 #221 rig | **[+] Re-home the rig class to #257** — combines with the `Rng`→`Ring` rename into one #257 edit |

### Tree baseline

**Zero** occurrences of any of these as identifiers in the tree:
`grep -rnE '\b(Rng|CRng|Rig|CRig|Ring|CRing|SemiRing|Semiring)\b' --include='*.v' .`
→ no output. The entire blast radius is in issue bodies. (The `Ring`-ish grep
noise in a naive search is all from `Right`/`RightKan`/`RightStrongFunctor`.)

### Blast radius — every issue body mentioning `Rng` or `CRng`

32 issues, 127 lines. All OPEN. Meaning column: **U** = the unital category
(#257's, → `Ring`); **NU** = the non-unital category (→ keeps/takes `Rng`);
**PATH** = a module path component, not a category name; **SEARCH** = a grep
string quoted inside an audit note.

**Verdict up front: every single identifier occurrence in the corpus means the
UNITAL category, except one line in #362.** The rename is therefore a
near-global find-and-replace, with #362 the sole site where the identifier is
*reassigned* rather than renamed.

| # | Line | Verbatim clause | Meaning |
|---|---|---|---|
| 221 | L71 | `Note in the header that #257 supplies only \`Rng\`/\`CRng\`, so the rig/semiring vocabulary is built here.` | U |
| 226 | L7 | `Set, Set*, Ens, Cat, Mon, Grp, Ab, Rng, CRng, R-Mod, Mod-R, K-Mod, Top, Toph, Top*` | U (Mac Lane's roster; his `Rng` is unital) |
| 226 | L10 | `Verified missing: Grp, Ab, Rng, CRng, all module categories, Top, Toph, Top* (zero definitional hits tree-wide).` | U |
| 226 | L14 | `- \`CRng\` as the full subcategory of commutative rings (if not already delivered by the Rng issue).` | U (both) |
| 226 | L32 | `# Print Assumptions on each residual construction (CRng, Mod-R, K-Mod, Mon@Sets)` | U |
| 226 | L50 | `cf. the dedicated issues #255 Grp, #256 Ab, #257 Rng, #258 R-Mod/Vect, #259 Top` | U |
| 228 | L7 | `is a functor \`CRng ⟶ Grp\`` | U |
| 228 | L11 | `neither the domain \`CRng\` nor the codomain \`Grp\` exists in-tree` | U |
| 228 | L13 | `Once the dependencies land (\`CRng\` from the Rng issue, \`Grp\`, and matrix algebra from \`Matr\`)` | U (both) |
| 228 | L14 | `the functor \`GL_n : CRng ⟶ Grp\`.` | U |
| 228 | L15 | `- The units functor \`(−)^* : CRng ⟶ Grp\`.` | U |
| 232 | L13 | `Once \`Rng\`/\`CRng\` land:` | U (both) |
| 232 | L14 | `Integral domains as a (full sub)category of \`CRng\`` | U |
| 232 | L31 | `coqc -R . Category Instance/Rng/Frac.v` | PATH |
| 244 | L14 | `Fields as a class over \`CRng\` (nonzero, inverses for nonzero elements)` | U |
| 251 | L7 | `unlike in Rng, where \`ℤ → ℚ\` is epi without being onto` | U |
| 257 | TITLE | `MacLane I.7: Rng, the category of rings` | U |
| 257 | L7 | `Rng has all small unital rings as objects and unit-preserving ring homomorphisms as arrows` | U (explicit) |
| 257 | L10 | `Ring/Rng/CRng/RingObject/semiring: prose-only hits` | SEARCH |
| 257 | L13 | `In \`Instance/Rng.v\` (new): … the category \`Rng\`; the full subcategory \`CRng\` of commutative rings (needed downstream by \`Matr\`/GL_n).` | U (both) + PATH |
| 257 | L16 | `\`ℤ → ℚ\` (stdlib \`QArith\`) is epi in \`Rng\` although not surjective` | U |
| 257 | L17 | `- The forgetful functors \`Rng ⟶ Ab\` (additive part) and \`Rng ⟶ Sets\`.` | U (both) |
| 257 | L22 | `- [ ] \`Print Assumptions\` closed (or documented) for \`Rng\`, \`CRng\`, the initial/terminal witnesses, and the ℤ → ℚ theorem` | U (both) |
| 257 | L31 | `coqc -R . Category Instance/Rng.v` | PATH |
| 257 | L32 | `# Print Assumptions Rng CRng Rng_Initial_Z Rng_Terminal_zero ZtoQ_epi_not_surjective` | U — **also renames the lemma names `Rng_Initial_Z`, `Rng_Terminal_zero`** |
| 258 | L10 | `no ring exists to index modules over (see the Rng issue)` | U |
| 258 | L13 | `Once \`Ab\` and \`Rng\` land:` | U |
| 258 | L16 | `the notation \`Vct_F\` for \`F-Mod\` (fields as a class over \`CRng\` …)` | U |
| 258 | L43 | `The parenthetical *(fields as a class over \`CRng\` — deliver the class here or in the FdVect` | U |
| 258 | L46 | `> (the \`Field\` class over \`CRng\` is owned by #244, which declares it unconditionally` | U |
| 269 | L12 | `searches for \`Ring\`/\`Rng\`/\`R-Mod\`/\`restriction of scalars\` return prose` | SEARCH |
| 269 | L16 | `Suggested module: \`Instance/Rng/Mod.v\` (over the Rng and R-Mod infrastructure of the referenced issues).` | PATH + U |
| 269 | L19 | `Package the assignment R to Mod-R, rho to restriction, as a coherent \`IndexedCat\` over Rng^op` | U |
| 269 | L39 | `coqc -R . Category Instance/Rng/Mod.v` | PATH |
| 269 | L40 | `echo 'Require Import Category.Instance.Rng.Mod. …'` | PATH |
| 275 | L11 | `no category Top and no category Rng exist in-tree` | U |
| 275 | L15 | `Suggested module: \`Instance/Top/ContinuousRing.v\` (over the Top and Rng infrastructure …)` | U |
| 275 | L17 | `as an object of the Rng category from #257` | U |
| 275 | L19 | `Package as a functor \`Top^op ⟶ Rng\`` | U |
| 275 | L21 | `Donors: … the Top and Rng issues' infrastructure.` | U |
| 293 | L12 | `searches for \`Rng\`/\`CRng\`/\`K-algebra\`: prose-only hits` | SEARCH |
| 293 | L16 | `Suggested module: \`Instance/Rng/Algebras.v\` (over the Rng infrastructure of #257).` | PATH + U |
| 293 | L18 | `1. Define CRng, the full subcategory of commutative rings (over #257's ring category; donor \`Construction/Subcategory.v\`).` | U — **note: duplicates #257 L13's claim on `CRng`; ownership overlap, flagged below** |
| 293 | L20 | `Prove the isomorphism (in Cat) between K-Alg and the coslice \`K ̸co CRng\`` | U |
| 293 | L22 | `Donors: … the Rng issue's infrastructure.` | U |
| 293 | L38 | `coqc -R . Category Instance/Rng/Algebras.v` | PATH |
| 293 | L39 | `echo 'Require Import Category.Instance.Rng.Algebras. …'` | PATH |
| 304 | L5 | `a packaging that also covers categories like Rng where zero morphisms are unavailable` | U — **decisive discriminator**: zero morphisms *do* exist between non-unital rngs; Mac Lane's remark is only true of the unital category |
| 304 | L8 | `none of the remark's concrete algebraic categories (Ab, Grp, Rng, R-Mod) exists in-tree` | U |
| 304 | L12 | `documenting the Rng-shaped motivation in the header` | U |
| 309 | L15 | `Suggested paths: \`Instance/Mod/Free.v\`, \`Instance/Rng/Polynomial.v\` (aligned with #257/#258's layout).` | PATH |
| 310 | L14 | `Suggested paths: \`Instance/Rng/MonoidRing.v\`, \`Instance/Vect/TensorAlgebra.v\`.` | PATH |
| 312 | L5 | `Rng ⟶ Ab (forgetting multiplication; free ring)` | U |
| 312 | L8 | `No Grp/Ab/Rng/Top/Set∗ categories exist in \`Instance/\`` | U |
| 312 | L13 | `Suggested paths: … \`Instance/Rng/Free.v\`, \`Instance/Top/Discrete.v\`` | PATH |
| 312 | L38 | `#400 — creates \`Instance/Rng/Free.v\` and supplies the free-ring-on-an-abelian-group functor with its adjunction to the forgetful \`Rng ⟶ Ab\`` | PATH + U |
| 312 | L100 | `**#473** *"The polynomial-ring monad from CRng"*` | U (quotes #473's title) |
| 314 | L12 | `- Over #257's Rng: define two-sided ideals and quotient rings R/I` | U |
| 314 | L13 | `Suggested paths: \`Instance/Mod/Quotient.v\`, \`Instance/Rng/Quotient.v\`.` | PATH |
| 324 | L8 | `(no Ab, R-Mod, Grp, CRng, Top, Top∗ in-tree)` | U |
| 324 | L14 | `(Exercise 1; needs a CRng full subcategory of #257's rings)` | U |
| 324 | L17 | `Suggested paths: … \`Instance/Rng/Tensor.v\`, \`Instance/Top/Coproduct.v\`` | PATH |
| 362 | L11 | `there is no category of rings, unital or otherwise … not about \`Rng\`.` | generic (no rename needed, but the sentence should survive) |
| 362 | L15 | `Suggested module: \`Instance/Rng.v\` plus \`Adjunction/Unitalization.v\`.` | PATH |
| 362 | L37 | `coqc -R . Category Instance/Rng.v` | PATH |
| 362 | L68 | `Consume #257's \`Instance/Rng.v\` unital-ring category. The increment here is the category of RNGS (rings without an assumed identity) — add it to the same file alongside #257's \`Rng\`, together with the forgetful functor \`Rng ⟶ Rng_nonunital\`.` | **MIXED — the one line where both senses occur.** First `Rng` = U; `Rng_nonunital` = NU. Under 3.2 this becomes `Ring ⟶ Rng` |
| 362 | L70-71 | `#257 is the filed obligation that creates \`Instance/Rng.v\` with the unital category and \`CRng\`; this issue extends that file.` | U + PATH |
| 362 | L73 | `**Naming:** the \`Rng\` identifier is #257's, used in Mac Lane's *unital* sense. The non-unital category built here must take a different name, disclosed in the file header, so the direction of the forgetful functor is unambiguous.` | **This whole paragraph is INVERTED by decision 3.2 and must be rewritten, not find-and-replaced** |
| 370 | L98 | `#257/#226 create \`CRng\`` | U |
| 400 | L17 | `Suggested module: \`Instance/Rng/Free.v\`.` | PATH |
| 400 | L40 | `coqc -R . Category Instance/Rng/Free.v` | PATH |
| 409 | L16 | `(\`rg -w 'Rng\|CRing\|RingObject'\` → 0 hits` | SEARCH — **note the spelling `CRing`, not `CRng`: a pre-existing inconsistency in the corpus** |
| 409 | L24 | `Suggested modules: \`Instance/Rng/Zp.v\` and \`Instance/Rng/PowerSeries.v\`` | PATH |
| 409 | L54 | `coqc -R . Category Instance/Rng/Zp.v Instance/Rng/PowerSeries.v` | PATH |
| 443 | L17 | `The ring cases are entirely absent: \`Rng\` and \`Ab\` do not exist (#257, #256)` | U |
| 443 | L22 | `Suggested module: \`Instance/Rng/Free.v\`` | PATH |
| 443 | L24 | `Over #257's \`Rng\` and #256's \`Ab\`, define the forgetful functors \`Rng ⟶ Sets\` and \`Rng ⟶ Ab\`` | U (×3) |
| 443 | L34 | `In-tree donors: #257's \`Rng\`, #256's \`Ab\`` | U |
| 443 | L49 | `coqc -R . Category Instance/Rng/Free.v` | PATH |
| 443 | L65 | `#400 — owns the new module \`Instance/Rng/Free.v\`` | PATH |
| 450 | L14 | `there is no \`Grp\` (#255) and no \`Rng\` (#257)` | U |
| 450 | L22 | `Suggested module: \`Instance/Grp/Coproduct.v\`, \`Instance/Rng/Coproduct.v\`` | PATH |
| 450 | L28 | `- Coproduct of rings (Exercise 2): the analogous construction in \`Rng\` (#257).` | U |
| 450 | L32 | `In-tree donors: #255's \`Grp\`, #257's \`Rng\`` | U |
| 450 | L47 | `coqc -R . Category Instance/Grp/Coproduct.v Instance/Rng/Coproduct.v` | PATH |
| 473 | TITLE | `MacLane VI.4: The polynomial-ring monad from CRng` | U |
| 473 | L5 | `The forgetful functor \`CRng → Set\` from commutative rings has a left adjoint` | U |
| 473 | L8 | `There is no category \`CRng\` (or \`Ring\`) of commutative rings` | U — **already treats `Ring` as the natural synonym** |
| 473 | L11 | `Build the category of commutative rings (\`CRng\`) and the forgetful functor to \`Set\`` | U |
| 473 | L32 | `Depends on: #257 (the category \`Rng\`/\`CRng\` of rings)` | U (both) |
| 474 | L5 | `The forgetful functor \`Rng → Ab\` (forgetting ring multiplication)` | U |
| 474 | L8 | `no \`Rng\`, no tensor-algebra endofunctor …, and no \`Rng → T-Alg\` comparison` | U (both) |
| 474 | L11 | `On top of \`Ab\` (#256) and \`Rng\` (#257)` | U |
| 474 | L12 | `Prove the algebra characterization and the isomorphism/equivalence \`EilenbergMoore T ≅ Rng\`.` | U |
| 474 | L13 | `donors: the \`Ab\`/\`Rng\` instances of #256/#257` | U |
| 474 | L18 | `- [ ] \`Print Assumptions\` clean for the tensor-algebra monad and the \`Rng ≅ EM\` comparison.` | U |
| 474 | L33 | `Depends on: #257 (the category \`Rng\` of rings)` | U |
| 479 | L5 | `exhibits a quotient ring \`R/A\` (by an ideal \`A\`) as a coequalizer in \`Rng\` split under \`Rng → Set\`` | U (both) |
| 479 | L8 | `no category \`Rng\` of rings … #255 (\`Grp\`) and #257 (\`Rng\`)` | U (both) |
| 479 | L12 | `exhibit \`R/A\` as the coequalizer of the analogous pair in \`Rng\`, split under \`Rng → Set\` (Ex. 1).` | U (both) |
| 479 | L13 | `Suggested modules: \`Instance/Grp/Coequalizer.v\`, \`Instance/Rng/Coequalizer.v\` (donors: the \`Grp\`/\`Rng\` instances of #255/#257 …)` | PATH + U |
| 479 | L26 | `\`coqc -R . Category Instance/Grp/Coequalizer.v\` and \`Instance/Rng/Coequalizer.v\`` | PATH |
| 479 | L33 | `Depends on: #257 (the category \`Rng\` of rings)` | U |
| 518 | L7 | `The forgetful functor \`U : Rng → Mon\` (forget addition) has a left adjoint \`ℤ : Mon → Rng\`` | U (both) |
| 518 | L11 | `(tracked as #257; \`grep '\bRng\b\|category of rings'\` → only comments)` | SEARCH |
| 518 | L15 | `Once the category of rings \`Rng\` (#257) is available, construct the monoid-ring functor \`ℤ : Mon → Rng\` and the adjunction \`ℤ ⊣ U\` (with \`U : Rng → Mon\` …) … In-tree donors: #257 (\`Rng\`)` | U (×4) |
| 518 | L19 | `- [ ] \`ℤ : Mon → Rng\` defined; the adjunction \`ℤ ⊣ U\` proved.` | U |
| 518 | L42 | `The adjunction this issue builds has \`U : Rng ⟶ Mon\` forgetting addition` | U |
| 518 | L44 | `The units functor \`(−)ˣ : Rng ⟶ Grp\` is constructed, and \`Ring(ℤ[G], R) ≅ Grp(G, Rˣ)\` is proved` | U — **already writes the hom-set as `Ring(−,−)`; the rename makes this line self-consistent** |
| 518 | L51 | `Change the suggested module and the Verification line from \`Instance/GroupRing.v\` to \`Instance/Rng/MonoidRing.v\`.` | PATH |
| 518 | L55 | `#310 … also constructs the monoid ring ℤ[M]/R[M] at Instance/Rng/MonoidRing.v` | PATH |
| 927 | L60 | `clause (viii) with \`Rng\`, clauses (ix)–(xii) with \`Cat\`` | U |
| 933 | TITLE | `Riehl 2.1/2.4: Representable functors on Grp and Rng — free and cyclic groups, tuples, units, and their universal elements` | U |
| 933 | L23 | `Suggested modules: \`Instance/Grp/Representables.v\` and \`Instance/Rng/Representables.v\` (new)` | PATH |
| 933 | L29 | `over #257's \`Rng\`, define the units functor \`(−)ˣ : Rng ⟶ Sets\`` | U (both) |
| 933 | L30 | `instantiate the category of elements (#345) at \`Uⁿ : Grp ⟶ Sets\` and at \`U : Rng ⟶ Sets\` … because \`End(U) ≅ Rng(ℤ[x], ℤ[x]) ≅ U(ℤ[x])\`` | U (×3) |
| 933 | L42 | `the integer-polynomial description of \`End(U : Rng ⟶ Sets)\` is derived` | U |
| 933 | L55 | `coqc -R . Category Instance/Rng/Representables.v` | PATH |
| 933 | L68 | `- Depends on: #257 (Rng, the category of rings)` | U |
| 937 | L29 | `once the Grp/Rng representability issue lands` | U (refers to #933) |
| 941 | L61 | `- Depends on: #257 (Rng, the category of rings)` | U |
| 1038 | L64 | `#257 delivers \`CRng\` as a full subcategory inside \`Instance/Rng.v\`` | U + PATH |
| 1038 | L65 | `it is #257's \`CRng\` in \`Instance/Rng.v\`` | U + PATH |
| 1038 | L66 | `Over #971's \`Instance/Field.v\` and #257's \`CRng\` (\`Instance/Rng.v\`), construct only the inclusion functor \`Field ⟶ CRng\`` | U (×3) + PATH |
| 1038 | L69 | `- [ ] The inclusion \`Field ⟶ CRng\` constructed over #257's existing \`CRng\`` | U (both) |

**Roll-up:** 32 issues — #221, #226, #228, #232, #244, #251, #257, #258, #269,
#275, #293, #304, #309, #310, #312, #314, #324, #362, #370, #400, #409, #443,
#450, #473, #474, #479, #518, #927, #933, #937, #941, #1038.

- Of these, **4 mention `Rng` only as a module path or a quoted grep string**
  and need no semantic rename: #309, #310, #400, #409. Every other issue has at
  least one line where `Rng`/`CRng` names a category. Module-path lines occur in
  a further 14 issues alongside semantic lines (#232, #257, #269, #275, #293,
  #312, #314, #324, #362, #443, #450, #479, #518, #933, #1038).
- **#362 is the only issue where the identifier's referent changes.** Its L68
  and L73 must be *rewritten*, not substituted.

### Four things decision 3.2 does not say, and must

**(1) `CRng` is unresolved.** The decision covers `Rng` → `Ring`. It is silent
on `CRng`, which appears in 12 issues (#221, #226, #228, #232, #244, #258, #293,
#324, #370, #473, #1038, and #257 itself). Consistency demands `CRng` → `CRing`.
Note that #409 L16 already spells it `CRing`, so one issue is already on the
target spelling. **Missing evidence: I cannot settle this from the corpus — the
operator has to choose.** Leaving `CRng` while `Rng` becomes `Ring` would be the
worst outcome (`Ring` and `CRng` implying an unrelated pair).

**(2) The module path `Instance/Rng.v` is unresolved.** Under 3.2 that one file
would contain **both** `Ring` (unital, #257) and `Rng` (non-unital, #362) — see
#362 L68: `add it to the same file alongside #257's \`Rng\``. Keeping the path
`Instance/Rng.v` is defensible (it is the *rng* file only in the loosest sense),
but 20+ downstream path references (`Instance/Rng/Free.v`,
`Instance/Rng/Mod.v`, `Instance/Rng/Zp.v`, …) hang off it. Renaming the path is a
second, larger blast radius; **not renaming it** is the cheaper choice and costs
only a header note. **The decision must state which.**

**(3) `Rng_Initial_Z` / `Rng_Terminal_zero` are lemma names, not just prose.**
#257 L32 verbatim:
`# Print Assumptions Rng CRng Rng_Initial_Z Rng_Terminal_zero ZtoQ_epi_not_surjective`

**(4) `CRng` has two claimants.** #257 L13 says it builds `CRng`
(`the full subcategory \`CRng\` of commutative rings`); #293 L18 also says
`1. Define CRng, the full subcategory of commutative rings (over #257's ring category …)`.
#1038 L64 already treats #257 as the owner
(`#257 delivers \`CRng\` as a full subcategory inside \`Instance/Rng.v\``).
If the coordinator is editing #257 anyway, this is the moment to make #293
consume rather than define. **Not a naming decision — flagging as adjacent.**

### Decision 4.3 — re-homing #221's rig class to #257: **STOP, this collides**

This is the finding I would most want the coordinator to see before applying
anything.

**#839 already owns the rig class, and already defines a `Ring`.**

#839's title is `Seven Sketches 5.3.1: Rigs — the class, the naturals and the booleans, and rings as rigs`. Its Work section says verbatim:

> `- In a new \`Theory/Algebra/Rig.v\`, define \`Class Rig\` over a setoid carrier —`
> `  \`rig_zero\`, \`rig_add\`, \`rig_one\`, \`rig_mul\` with \`Proper\` instances for the`
> `  setoid equivalence, and the four clauses of Definition 5.36 stated with \`≈\`.`
> `  Add \`RigHom\` and the category \`Rig\` (mirroring`
> `  \`Theory/Algebra/Monoid/Hom.v\`'s \`Mon\`/\`Mon_Forget\` shape), plus the`
> `  forgetful functors to \`CMon\` and \`Mon\`.`

and, critically:

> `  - the ring-to-rig forgetting of Example 5.42: define \`Class Ring\` as \`Rig\``
> `    plus additive inverses (mirroring how \`Structure/Additive.v:34\` extends`
> `    \`Structure/Preadditive.v:34\`), give the forgetful \`Ring -> Rig\`, and record`
> `    the mnemonic in the header.`

with the DoD line:

> `- [ ] \`Ring\` defined as \`Rig\` + negatives, with the forgetful functor; the ℝ`
> `      witness either supplied (with its stdlib axioms disclosed) or explicitly`
> `      recorded as absent.`

**Consequences:**

1. **Decision 4.3 re-homes to the wrong issue.** #221 L71 says
   `Note in the header that #257 supplies only \`Rng\`/\`CRng\`, so the rig/semiring vocabulary is built here.`
   Re-homing that to #257 would give #257 a rig class that #839 already builds
   in `Theory/Algebra/Rig.v`. The correct target is **#839**, not #257. #843 L119
   already records the ownership verbatim:
   `Depends on: #839 (\`7sketches:5.3.1:def5.36\`) (the rig class).`
   and #843's own audit correction says
   `> **SCOPE (added on audit).** The BASE matrix category is **#221's** obligation` — so
   the corpus already routes matrices→#221 and rigs→#839.

2. **Decision 3.2 creates a *new* `Ring` collision.** After 3.2, #257 names a
   *category* `Ring` (`Instance/Rng.v`); #839 names a *class* `Ring`
   (`Theory/Algebra/Rig.v`). They will co-occur: #221 (matrices over a
   rig/semiring, depends on #257), #473/#474 (rings as monad algebras), #841
   (`Square matrices over a rig form a rig`) all pull in both layers. In Coq
   these are two global identifiers in one import closure. Mac Lane's `Ring` is
   a category of set-level rings; Seven Sketches' `Ring` is the set-level ring
   *structure*. **The clash is real and 3.2 as written does not resolve it.**

   Two clean escapes, for the operator:
   - #257's category takes `Ring`; #839's class is renamed (e.g. `RingStruct`,
     or `Rig`+`Rig_neg`) — mirrors how the tree already distinguishes
     `Structure/Monoid.v`'s monoid *objects* from `Theory/Algebra/Monoid.v`'s
     monoid *structures*; or
   - #839 keeps `Class Ring` and #257's category takes `Ring` only as a
     `Category` instance in a distinct module, with an explicit header note and
     a qualified-name convention.

   I am **not** recommending one — this is a scope call, and the evidence
   supports either. What I can say without hedging is that decision 3.2's
   "Header must disclose the clash" was written about the `Rng` unital/non-unital
   clash and does not cover this second one.

3. **#839's own body has an internal collision already**, independent of any
   decision: it says `Add \`RigHom\` and the category \`Rig\`` while also
   defining `Class Rig`. Two global `Rig`s in one file. Worth folding into the
   same edit pass.

**Rig/semiring blast radius** (for whichever re-homing target is chosen): 24
issues mention `rig`/`semiring` — #221, #257, #309, #340, #790, #800, **#839**,
#840, #841, #842, #843, #845, #846, #847, #848, #849, #850, #852, #854, #855,
#856, #857, #858, #859. Of these, 17 Seven-Sketches issues consume "the rig class
of §5.3.1" by that phrase (#840 L20, #842 L30/L59, #843 L32, #849 L61, #854 L60,
#856 L57, #857 L52, #858 L26, #859 L24, …), i.e. they are already wired to #839.
Only **#221 L14/L45/L66/L71** and **#340 L11** (`Define \`RingObject\` (semiring
first if that stages better …)`) sit outside that spine.

---

## Summary of recommendations

| Decision | Recommendation | Confidence |
|---|---|---|
| 3.3 | **`DiGraph`** for #705. `Quiver` is taken three ways (`Class Quiver` at `Construction/Free/Quiver.v:54`; `QuiverCategory` at `:358` = the same mathematical object; two issue *titles* already use bare `Quiver` for it). `DiGraph` has zero hits in tree and zero in the 845-issue corpus. | High — direct evidence |
| 3.3 blast radius | #705 (L47, L49, L54, L69 + 3 lemma names in the Verification block). Disambiguate #357 L107 in the same pass. #926/#962/#988's `Graph` mentions are #926's category and stay. | High |
| 3.2 | Proceed with `Rng`→`Ring`, but **resolve `CRng`, the `Instance/Rng.v` path, and the `Rng_*` lemma prefixes explicitly** — the decision text covers none of them. Every corpus occurrence means UNITAL except #362 L68's `Rng_nonunital`; #362 L73's Naming paragraph must be rewritten, not substituted. | High for the meaning classification; the three open sub-questions are genuinely unsettled |
| 4.3 | **Do not apply as written.** #839 (`Seven Sketches 5.3.1: Rigs — the class …`) already owns the rig class in `Theory/Algebra/Rig.v`, is already cited as its owner by #843 L119, and is already consumed by 17 issues. Re-home #221's rig line to **#839**, not #257. | High — direct evidence |
| 3.2 ↔ #839 | **New, unrecorded clash:** #839 defines `Class Ring` as `Rig` + negatives. Renaming #257's category to `Ring` puts two global `Ring`s in the same import closure. Needs a decision. | High that the clash exists; no recommendation on which side yields |
