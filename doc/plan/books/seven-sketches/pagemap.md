# Pagemap — Fong & Spivak, *Seven Sketches in Compositionality*

Calibration status: **CONFIRMED**. Two agents calibrated independently; a third pass
applied the offset to all ten reported chapter starts, opened every page, re-derived the
offset three independent ways, and diffed all 146 sections against the printed table of
contents. 10/10 chapter starts land correctly. 146/146 sections match. Zero folio
mismatches across all 341 body pages.

---

## EDITION

| Field | Value |
|---|---|
| Title (title page) | Seven Sketches in Compositionality: An Invitation to Applied Category Theory |
| Authors | Brendan Fong, David I. Spivak |
| Version | **arXiv:1803.05316v3 [math.CT]**, stamped "12 Oct 2018" rotated in the left margin of PDF page 1 |
| Title page states | "(Last updated: October 16, 2018)" |
| Preface signed | "Brendan Fong and David I. Spivak / Cambridge MA, October 2018" |
| PDF | `/Users/johnw/Desktop/Spivak_Fong_Seven_Sketches.pdf` |
| Pages | 353 PDF pages, 612 × 792 pt (US Letter) |
| Creator / Producer | LaTeX with hyperref package / pdfTeX-1.40.17 (PDF 1.5) |
| Created | Mon Oct 15 17:30:07 2018 PDT |
| Copyright page | **None.** No publisher imprint. This is the free author/arXiv version. |

**This is NOT the 2019 Cambridge University Press hardback**, which was retitled *An
Invitation to Applied Category Theory: Seven Sketches in Compositionality*, reset, and
repaginated (approx. xii+338). Every printed page number in this pagemap is valid for the
arXiv PDF only and must never be cited as a CUP page.

Structure: front matter i–xii (PDF 1–12), body 1–341 (PDF 13–353). Seven chapters,
Appendix A, Bibliography, Index. No list of figures, no list of tables, no glossary, no
notation table, no Part divisions.

---

## OFFSET

```
printed = pdf - 12          pdf = printed + 12
```

**Uniform over the entire arabic body: PDF 13–353 = printed 1–341.** No drift anywhere.
No per-range blocks. One mapping serves all seven chapters, the appendix, the bibliography
and the index.

Front matter is a **separate sequence with a different offset**:

```
front matter:  roman value = pdf index      (offset 0, PDF 1-12 = i-xii)
```

Applying `printed = pdf - 12` below PDF 13 yields a nonsense zero or negative number.

### Probe evidence

Ten pages opened as rendered images, one per chapter/appendix/back-matter start:

| PDF | printed | what is on the page |
|---:|---:|---|
| 13 | 1 | "Chapter 1 / Generative effects: Orders and Galois connections", §1.1, folio bottom-centre |
| 51 | 39 | "Chapter 2 / Resource theories: Monoidal preorders and enrichment", §2.1 |
| 89 | 77 | "Chapter 3 / Databases: Categories, functors, and universal constructions", §3.1, display **(3.1)** |
| 129 | 117 | "Chapter 4 / Collaborative design: Profunctors, categorification, and monoidal categories", §4.1, cites [Cen15] |
| 159 | 147 | "Chapter 5 / Signal flow graphs: Props, presentations, and proofs", §5.1 |
| 193 | 181 | "Chapter 6 / Electric circuits: Hypergraph categories and operads", §6.1, flip-flop figure |
| 233 | 221 | "Chapter 7 / Logic of behavior: Sheaves, toposes, and internal languages", §7.1, footnote 1 |
| 271 | 259 | "Appendix A / Exercise solutions", §A.1, "Solution to Exercise 1.1." |
| 335 | 323 | "Bibliography", entries [Ada17]… |
| 343 | 331 | "Index", two-column |

### Three independent derivations

1. **Exhaustive folio scan, all 341 body pages (PDF 13–353).** Required the token
   `pdf − 12` to appear as a standalone folio at the start or end of the running head, or
   alone in the footer. Result: **335/335 non-blank pages matched, 0 mismatches**, 6 blank
   pages. There is no page anywhere in the body at which any other offset holds.
2. **Embedded `/PageLabels`** (`qpdf --json --json-key=pagelabels`):
   `index 0 → {/S /r, /St 1}`, `index 12 → {/S /D, /St 1}`. The file itself declares
   roman-from-1 at PDF 1 and decimal-from-1 at PDF 13.
3. **Front-matter folios read one by one.** PDF 1 title (no folio, = i), PDF 2 blank (no
   folio, = ii), PDF 3 "iii" (Preface opens), PDF 4–7 iv/v/vi/vii, PDF 8 "Contents" viii,
   PDF 9–12 ix/x/xi/xii. Confirms the transition at PDF 13 from the other side.

### Why this book cannot drift

Born-digital pdfTeX output, not a scan — there was no rescanning step in which a blank
verso could be dropped. The six blank versos are original `\cleardoublepage` blanks and
**are fully counted** in the printed numbering, proved directly at the boundary:
PDF 49 = 37, PDF 50 blank (= 38), PDF 51 = 39.

### Blank versos (counted, no folio printed, do not adjust the offset)

| PDF | 50 | 128 | 192 | 232 | 270 | 334 |
|---|---:|---:|---:|---:|---:|---:|
| printed | 38 | 116 | 180 | 220 | 258 | 322 |

---

## NUMBERING

**ONE SINGLE SHARED COUNTER PER CHAPTER — AND DISPLAYED EQUATIONS DRAW FROM THAT SAME
COUNTER.** There is no per-kind counter, no per-section counter, and no separate equation
counter anywhere in the book. Numbers are always exactly two levels, `CHAPTER.ITEM` (never
`SECTION.ITEM` — item 1.125 exists although Chapter 1 has only sections 1.1–1.5).

### The proving example — printed page 32 (PDF 44), read consecutively off the image

| # | what it is | appearance |
|---:|---|---|
| 1.114 | `Exercise 1.114.` "To be sure that g really is right adjoint to f in Example 1.113…" | unshaded, italic header, hollow-diamond terminator |
| 1.115 | `Theorem 1.115 (Adjoint functor theorem for preorders).` | pale **lavender** box, bold header |
| **1.116** | **displayed equation** `f(p) := ⋀{q ∈ Q | p ≤ g(q)};` labelled **(1.116)** | right-flush in the margin |
| 1.117 | `Example 1.117.` "Let f : A → B be a function between sets." | pale **green** box, italic header |

Exercise → Theorem → **EQUATION** → Example, running 114, 115, 116, 117 without a break.
Corroborating runs: `Exercise 1.1` (p.2) then equations (1.2), (1.3) then `Exercise 1.4`
(p.4) — the exercise counter jumps 1.1 → 1.4 precisely because the two displays consumed
2 and 3. Chapter 3's very first numbered thing is the equation **(3.1)**, on the
chapter-opening page. Chapter 2's first is **(2.1)**; its first named item is
`Definition 2.2`.

### Verified per-chapter tallies

Every gap in the item sequence was individually located as a parenthesised numbered
display in that chapter's text — **119/119 confirmed**.

| ch | max number | named items | equations | gaps confirmed |
|---:|---:|---:|---:|---:|
| 1 | 1.125 | 117 | 8 | 8/8 |
| 2 | 2.105 | 79 | **26** | 26/26 |
| 3 | 3.102 | 87 | 15 | 15/15 |
| 4 | 4.66 | 51 | 15 | 15/15 |
| 5 | 5.87 | 72 | 15 | 15/15 |
| 6 | 6.101 | 79 | 22 | 22/22 |
| 7 | 7.81 | 63 | 18 | 18/18 |
| **total** | | **548** | **119** | **119/119** |

Chapter 1's equation numbers are exactly **{2, 3, 5, 8, 15, 96, 108, 116}**.
Chapter 2's are exactly **{1, 7, 10, 11, 12, 13, 15, 16, 17, 18, 22, 23, 24, 25, 26, 28,
48, 56, 57, 59, 66, 77, 80, 88, 99, 101}** — 26 of them, all verified right-flush.

### Kinds sharing the counter

`Exercise`, `Example`, `Definition`, **`Rough Definition`**, `Remark`, `Proposition`,
`Theorem`, `Lemma`, `Corollary`, `Construction`. Unnumbered: `Proof.` blocks (italic
header, right-aligned hollow square terminator).

`Rough Definition N.M` occurs six times — **4.45, 4.51, 5.33, 6.68, 6.91, 6.98** — and an
extractor keyed on `^Definition` will miss all six.

### Visual discriminators when scanning page images

| kind | box | header |
|---|---|---|
| Example | pale **green** | italic `Example N.M.` |
| Definition / Rough Definition | pale **pink/rose** | bold `Definition N.M.` |
| Theorem / Proposition / Lemma / Corollary | pale **lavender** | bold, often with a parenthetical name |
| Exercise | **none** | italic `Exercise N.M.`, right-aligned hollow diamond |
| Remark | none | bold/italic run-in |

Shaded boxes may span a page break: an item's number can sit on page *N* with its body
continuing on *N+1*.

### Exercises

243 distinct exercise numbers, inline within sections (never collected at chapter end).
Per chapter: 50 / 36 / 38 / 24 / 28 / 30 / 37. Sub-parts are local `(a)/(b)/(c)` or
`1./2./3.` with no global numbers. Solutions are gathered in Appendix A under the
unnumbered italic header `Solution to Exercise N.M.` — **242** of them.
**Exercise 3.98 has no printed solution.** Appendix A runs a separate equation counter,
**(A.1)–(A.4)**, exactly four, and contains no named numbered environments of its own.

---

## TABLE OF CONTENTS

All 146 entries below were extracted from the printed TOC (PDF 8–12) and diffed against
both agents' reports: **zero number mismatches, zero page mismatches, zero omissions.**

### Front matter (PDF 1–12 = i–xii, offset 0)

| PDF | printed | content |
|---:|---:|---|
| 1 | i | Title page (folio not printed); arXiv identifier rotated in left margin |
| 2 | ii | Blank (folio not printed) |
| 3–7 | iii–vii | Preface — unnumbered subsections: Purpose and audience; How to read this book; Acknowledgments; Personal note |
| 8–12 | viii–xii | Contents |

### Chapter 1 — Generative effects: Orders and adjunctions — printed 1

| § | name | printed |
|---|---|---:|
| 1.1 | More than the sum of their parts | 1 |
| 1.1.1 | A first look at generative effects | 2 |
| 1.1.2 | Ordering systems | 5 |
| 1.2 | What is order? | 7 |
| 1.2.1 | Review of sets, relations, and functions | 7 |
| 1.2.2 | Preorders | 12 |
| 1.2.3 | Monotone maps | 18 |
| 1.3 | Meets and joins | 23 |
| 1.3.1 | Definition and basic examples | 23 |
| 1.3.2 | Back to observations and generative effects | 26 |
| 1.4 | Galois connections | 26 |
| 1.4.1 | Definition and examples of Galois connections | 27 |
| 1.4.2 | Back to partitions | 28 |
| 1.4.3 | Basic theory of Galois connections | 30 |
| 1.4.4 | Closure operators | 33 |
| 1.4.5 | Level shifting | 35 |
| 1.5 | Summary and further reading | 36 |

### Chapter 2 — Resources: monoidal preorders and enrichment — printed 39

| § | name | printed |
|---|---|---:|
| 2.1 | Getting from a to b | 39 |
| 2.2 | Symmetric monoidal preorders | 41 |
| 2.2.1 | Definition and first examples | 41 |
| 2.2.2 | Introducing wiring diagrams | 43 |
| 2.2.3 | Applied examples | 48 |
| 2.2.4 | Abstract examples | 52 |
| 2.2.5 | Monoidal monotone maps | 55 |
| 2.3 | Enrichment | 57 |
| 2.3.1 | V-categories | 57 |
| 2.3.2 | Preorders as Bool-categories | 58 |
| 2.3.3 | Lawvere metric spaces | 59 |
| 2.3.4 | V-variations on preorders and metric spaces | 63 |
| 2.4 | Constructions on V-categories | 64 |
| 2.4.1 | Changing the base of enrichment | 64 |
| 2.4.2 | Enriched functors | 65 |
| 2.4.3 | Product V-categories | 66 |
| 2.5 | Computing presented V-categories with matrix mult. | 68 |
| 2.5.1 | Monoidal closed preorders | 69 |
| 2.5.2 | Quantales | 71 |
| 2.5.3 | Matrix multiplication in a quantale | 73 |
| 2.6 | Summary and further reading | 75 |

### Chapter 3 — Databases: Categories, functors, and (co)limits — printed 77

| § | name | printed |
|---|---|---:|
| 3.1 | What is a database? | 77 |
| 3.2 | Categories | 81 |
| 3.2.1 | Free categories | 82 |
| 3.2.2 | Presenting categories via path equations | 84 |
| 3.2.3 | Preorders and free categories: two ends of a spectrum | 85 |
| 3.2.4 | Important categories in mathematics | 86 |
| 3.2.5 | Isomorphisms in a category | 88 |
| 3.3 | Functors, natural transformations, and databases | 89 |
| 3.3.1 | Sets and functions as databases | 89 |
| 3.3.2 | Functors | 91 |
| 3.3.3 | Database instances as Set-valued functors | 93 |
| 3.3.4 | Natural transformations | 95 |
| 3.3.5 | The category of instances on a schema | 97 |
| 3.4 | Adjunctions and data migration | 99 |
| 3.4.1 | Pulling back data along a functor | 100 |
| 3.4.2 | Adjunctions | 102 |
| 3.4.3 | Left and right pushforward functors, Σ and Π | 104 |
| 3.4.4 | Single set summaries of databases | 106 |
| 3.5 | Bonus: An introduction to limits and colimits | 107 |
| 3.5.1 | Terminal objects and products | 107 |
| 3.5.2 | Limits | 110 |
| 3.5.3 | Finite limits in Set | 111 |
| 3.5.4 | A brief note on colimits | 113 |
| 3.6 | Summary and further reading | 114 |

### Chapter 4 — Co-design: profunctors and monoidal categories — printed 117

| § | name | printed |
|---|---|---:|
| 4.1 | Can we build it? | 117 |
| 4.2 | Enriched profunctors | 119 |
| 4.2.1 | Feasibility relationships as Bool-profunctors | 119 |
| 4.2.2 | V-profunctors | 121 |
| 4.2.3 | Back to co-design diagrams | 124 |
| 4.3 | Categories of profunctors | 125 |
| 4.3.1 | Composing profunctors | 125 |
| 4.3.2 | The categories V-Prof and Feas | 127 |
| 4.3.3 | Fun profunctor facts: companions, conjoints, collages | 130 |
| 4.4 | Categorification | 132 |
| 4.4.1 | The basic idea of categorification | 133 |
| 4.4.2 | A reflection on wiring diagrams | 134 |
| 4.4.3 | Monoidal categories | 136 |
| 4.4.4 | Categories enriched in a symmetric monoidal category | 138 |
| 4.5 | Profunctors form a compact closed category | 139 |
| 4.5.1 | Compact closed categories | 141 |
| 4.5.2 | Feas as a compact closed category | 143 |
| 4.6 | Summary and further reading | 145 |

### Chapter 5 — Signal flow graphs: Props, presentations, & proofs — printed 147

| § | name | printed |
|---|---|---:|
| 5.1 | Comparing systems as interacting signal processors | 147 |
| 5.2 | Props and presentations | 149 |
| 5.2.1 | Props: definition and first examples | 149 |
| 5.2.2 | The prop of port graphs | 151 |
| 5.2.3 | Free constructions and universal properties | 153 |
| 5.2.4 | The free prop on a signature | 155 |
| 5.2.5 | Props via presentations | 158 |
| 5.3 | Simplified signal flow graphs | 159 |
| 5.3.1 | Rigs | 159 |
| 5.3.2 | The iconography of signal flow graphs | 160 |
| 5.3.3 | The prop of matrices over a rig | 164 |
| 5.3.4 | Turning signal flow graphs into matrices | 165 |
| 5.3.5 | The idea of functorial semantics | 168 |
| 5.4 | Graphical linear algebra | 168 |
| 5.4.1 | A presentation of Mat(R) | 168 |
| 5.4.2 | Aside: monoid objects in a monoidal category | 172 |
| 5.4.3 | Signal flow graphs: feedback and more | 174 |
| 5.5 | Summary and further reading | 178 |

### Chapter 6 — Circuits: hypergraph categories and operads — printed 181

| § | name | printed |
|---|---|---:|
| 6.1 | The ubiquity of network languages | 181 |
| 6.2 | Colimits and connection | 184 |
| 6.2.1 | Initial objects | 184 |
| 6.2.2 | Coproducts | 186 |
| 6.2.3 | Pushouts | 188 |
| 6.2.4 | Finite colimits | 191 |
| 6.2.5 | Cospans | 194 |
| 6.3 | Hypergraph categories | 197 |
| 6.3.1 | Frobenius monoids | 197 |
| 6.3.2 | Wiring diagrams for hypergraph categories | 200 |
| 6.3.3 | Definition of hypergraph category | 201 |
| 6.4 | Decorated cospans | 203 |
| 6.4.1 | Symmetric monoidal functors | 204 |
| 6.4.2 | Decorated cospans | 204 |
| 6.4.3 | Electric circuits | 207 |
| 6.5 | Operads and their algebras | 211 |
| 6.5.1 | Operads design wiring diagrams | 211 |
| 6.5.2 | Operads from symmetric monoidal categories | 214 |
| 6.5.3 | The operad for hypergraph props | 216 |
| 6.6 | Summary and further reading | 218 |

### Chapter 7 — Logic of behavior: Sheaves, toposes, languages — printed 221

| § | name | printed |
|---|---|---:|
| 7.1 | How can we prove our machine is safe? | 221 |
| 7.2 | The category Set as an exemplar topos | 224 |
| 7.2.1 | Set-like properties enjoyed by any topos | 225 |
| 7.2.2 | The subobject classifier | 228 |
| 7.2.3 | Logic in the topos Set | 230 |
| 7.3 | Sheaves | 232 |
| 7.3.1 | Presheaves | 232 |
| 7.3.2 | Topological spaces | 234 |
| 7.3.3 | Sheaves on topological spaces | 236 |
| 7.4 | Toposes | 242 |
| 7.4.1 | The subobject classifier Ω in a sheaf topos | 243 |
| 7.4.2 | Logic in a sheaf topos | 245 |
| 7.4.3 | Predicates | 247 |
| 7.4.4 | Quantification | 248 |
| 7.4.5 | Modalities | 250 |
| 7.4.6 | Type theories and semantics | 251 |
| 7.5 | A topos of behavior types | 252 |
| 7.5.1 | The interval domain | 252 |
| 7.5.2 | Sheaves on IR | 253 |
| 7.5.3 | Safety proofs in temporal logic | 255 |
| 7.6 | Summary and further reading | 256 |

*§7.5.2 "Sheaves on IR" — "IR" is the blackboard-bold interval domain 𝕀ℝ.*

### Appendix A — Exercise solutions — printed 259

| § | name | printed |
|---|---|---:|
| A.1 | Solutions for Chapter 1 | 259 |
| A.2 | Solutions for Chapter 2 | 270 |
| A.3 | Solutions for Chapter 3 | 277 |
| A.4 | Solutions for Chapter 4 | 286 |
| A.5 | Solutions for Chapter 5 | 293 |
| A.6 | Solutions for Chapter 6 | 303 |
| A.7 | Solutions for Chapter 7 | 312 |

### Back matter (unnumbered; NOT chapters)

| entry | printed | PDF |
|---|---:|---:|
| Bibliography | 323–330 | 335–342 |
| Index | 331–341 | 343–353 |

---

## PER-CHAPTER PDF RANGES

`offset = 12` for every range. `printed = pdf - 12`.
The eight ranges **tile PDF 13–334 exactly** — no gaps, no overlaps.

| roman | title (TOC / running-head form) | printed | PDF start | PDF end | offset | splitAt | pages |
|---|---|---|---:|---:|---:|---:|---:|
| 1 | Generative effects: Orders and adjunctions | 1–38 | 13 | 50 | 12 | 30 | 38 |
| 2 | Resources: monoidal preorders and enrichment | 39–76 | 51 | 88 | 12 | 69 | 38 |
| 3 | Databases: Categories, functors, and (co)limits | 77–116 | 89 | 128 | 12 | 109 | 40 |
| 4 | Co-design: profunctors and monoidal categories | 117–146 | 129 | 158 | 12 | 144 | 30 |
| 5 | Signal flow graphs: Props, presentations, & proofs | 147–180 | 159 | 192 | 12 | 176 | 34 |
| 6 | Circuits: hypergraph categories and operads | 181–220 | 193 | 232 | 12 | 213 | 40 |
| 7 | Logic of behavior: Sheaves, toposes, languages | 221–258 | 233 | 270 | 12 | 254 | 38 |
| A | Exercise solutions | 259–322 | 271 | 334 | 12 | 305 | 64 |

Back matter, outside the chapter tiling: Bibliography PDF 335–342, Index PDF 343–353.
`38+38+40+30+34+40+38+64 = 322` (PDF 13–334) `+ 8 + 11 = 341` = the full printed body.

### Content extent vs. range extent

Six ranges end on a blank verso (the trailing `\cleardoublepage` blank, which consumes a
printed number and is assigned to the preceding chapter so the tiling has no holes):

| roman | last CONTENT page | trailing blank | range ends |
|---|---|---|---|
| 1 | printed 37 = PDF 49 | PDF 50 | 50 |
| 2 | printed 76 = PDF 88 | *(none)* | 88 |
| 3 | printed 115 = PDF 127 | PDF 128 | 128 |
| 4 | printed 146 = PDF 158 | *(none)* | 158 |
| 5 | printed 179 = PDF 191 | PDF 192 | 192 |
| 6 | printed 219 = PDF 231 | PDF 232 | 232 |
| 7 | printed 257 = PDF 269 | PDF 270 | 270 |
| A | printed 321 = PDF 333 | PDF 334 | 334 |

### Split points

Each `splitAt` was chosen near the range midpoint **and verified by extraction to carry a
section header**, so no split falls mid-proof:

| roman | splitAt (PDF) | printed | section beginning on that page |
|---|---:|---:|---|
| 1 | 30 | 18 | 1.2.3 Monotone maps |
| 2 | 69 | 57 | 2.3 Enrichment / 2.3.1 V-categories |
| 3 | 109 | 97 | 3.3.5 The category of instances on a schema |
| 4 | 144 | 132 | 4.4 Categorification |
| 5 | 176 | 164 | 5.3.3 The prop of matrices over a rig |
| 6 | 213 | 201 | 6.3.3 Definition of hypergraph category |
| 7 | 254 | 242 | 7.4 Toposes |
| A | 305 | 293 | A.5 Solutions for Chapter 5 |

---

## WARNINGS

### Trap 1 — equations share the item counter (the campaign's known failure mode, live here)

Displayed equations are **not** on a separate counter. A bare number like `1.116`, `2.1`,
`3.1` or `7.14` is an **equation**, not a missing item. Any inventory that assumes
contiguous item numbering, or back-fills unseen numbers as undiscovered items, **will
hallucinate**. 119 of the 667 numbers in chapters 1–7 are equations; see the NUMBERING
table for the per-chapter split and Chapter 1's and Chapter 2's exact equation sets.

Disambiguator: equations are cited as `Eq. (1.96)` **with** parentheses and sit right-flush
in the margin; items are cited as `Definition 1.95` **without** parentheses and head a
shaded box.

Treat the per-chapter equation tallies as **high-confidence cross-checks, not hard
targets.** They were derived by text harvesting, then every one of the 119 gaps was
individually confirmed as a parenthesised display — but a header split across a page break
in a pathological way could still shift a count by one. The offset, ranges, section list
and the shared-counter fact are certainties; the tallies are very good estimates.

### Trap 2 — TOC title ≠ chapter-opening title, for all seven chapters

| ch | TOC / running-head form (used above) | chapter-opening page form |
|---|---|---|
| 1 | Generative effects: Orders and **adjunctions** | Generative effects: Orders and **Galois connections** |
| 2 | **Resources**: monoidal preorders and enrichment | **Resource theories**: Monoidal preorders and enrichment |
| 3 | Databases: Categories, functors, and **(co)limits** | Databases: Categories, functors, and **universal constructions** |
| 4 | **Co-design**: profunctors and monoidal categories | **Collaborative design**: Profunctors, **categorification**, and monoidal categories |
| 5 | Signal flow graphs: Props, presentations, **&** proofs | Signal flow graphs: Props, presentations, **and** proofs |
| 6 | **Circuits**: hypergraph categories and operads | **Electric circuits**: Hypergraph categories and operads |
| 7 | Logic of behavior: Sheaves, toposes, languages | Logic of behavior: Sheaves, toposes, **and internal** languages |

All seven **verso running heads use the TOC form verbatim** (verified by extraction), so a
downstream agent reading page images will see the TOC form on nearly every page and the
title-page form only on the chapter opener. **Accept either form; never fail a chapter on a
title mismatch alone.**

### Trap 3 — blank versos

PDF 50, 128, 192, 232, 270, 334 (= printed 38, 116, 180, 220, 258, 322) render as genuinely
empty pages (~4 KB PNG, zero extractable text) with no folio and no running head. They
**are counted** in the printed numbering. Do not treat one as a dropped page and do not
adjust the offset on hitting one. Each is the **last page** of the ch1, ch3, ch5, ch6, ch7
and Appendix A ranges — expect and ignore it.

### Trap 4 — `Rough Definition`

Six real headers of this kind: **4.45, 4.51, 5.33, 6.68, 6.91, 6.98**. An extractor keyed
on `^Definition` at line start misses all six and then wrongly reclassifies those six
numbers as equations. Match the kind word with an optional `Rough ` prefix.

### Trap 5 — Exercise 3.98 has no printed solution

243 body exercise numbers vs 242 Appendix A solution headers; the difference is exactly
`{3.98}`. Not an extraction failure. Do not go looking for it.

### Trap 6 — Appendix A has no items of its own

It runs a **separate** equation counter, `(A.1)`–`(A.4)`, exactly four, and its only
headers are the unnumbered italic `Solution to Exercise N.M.` — whose numbers are
back-references into chapters 1–7, **not** new items. An inventory pass over PDF 271–334
must not mint items from them.

### Trap 7 — front matter uses a different offset

PDF 1–12 = roman i–xii at **offset 0**. PDF 1 (title) and PDF 2 (blank verso) print no
folio at all. `printed = pdf - 12` is meaningless below PDF 13. The Preface carries no
numbered environments and no equations; its four subsections are unnumbered.

### Trap 8 — unnumbered bold run-in headings are not sections

E.g. "A simple system." and "Joining our simple systems." (printed 3–4), "A database is a
system of interlocking tables." (printed 77). They have no number and are not in the TOC.
Do not count them as sections or items. Section depth is at most three levels
(`N`, `N.M`, `N.M.K`) — no four-level subsections, no Part divisions, no unnumbered
chapter-level introduction. Every chapter ends with an `N.last Summary and further reading`
section (1.5, 2.6, 3.6, 4.6, 5.5, 6.6, 7.6).

### Trap 9 — footnotes are numbered continuously per chapter

Not per page. Superscript arabic markers below a short rule. A wholly independent sequence
from the item counter — never confuse a footnote marker with an item number.

### Trap 10 — text-extraction false positives

Two verified non-items: `Definition 7.25. 8` (a list item "8." wrapping onto the reference)
and `Example 2.2.23` (a citation to a *different* book's numbering, in a bibliographic aside
near printed 218). Item numbers are **always exactly two levels** (`CHAPTER.ITEM`); a
three-level number in running text is a section reference or a foreign citation, never an
item.

### Trap 11 — the `sections[].n` field is an ordinal, not a section number

The launch-args schema types `n` as an integer, so it cannot hold `1.2.3`. In the emitted
args `n` is the section's 1-based ordinal within its chapter and the real dotted number is
prefixed onto `name` (e.g. `n=7, name="1.2.3 Monotone maps"`). Parse the dotted number off
the front of `name`; never read `n` as a section number. The unprefixed table above is the
authoritative TOC.

### Legibility

- **Born-digital pdfTeX output, not a scan.** No skew, speckle, or OCR noise. All glyphs
  render cleanly: script/calligraphic category letters, blackboard bold, Φ/Ψ/Σ/Π/Ω, the
  `;` composition symbol, the exercise lozenge, the pushout corner marker.
- All figures are vector line art and render correctly: wiring diagrams, commutative
  diagrams with labelled arrows, the coloured Definition/Example callout boxes, the
  two-tone dashed bridge diagrams in Appendix A. No unrenderable or missing figures in the
  pages opened.
- **Chapter and appendix openers DO print their folio** (bottom centre) in this edition —
  verified on PDF 13, 51, 89, 129, 159, 193, 233, 271, 335, 343. Ordinary pages carry the
  folio in the **outer** top corner beside a running head (`CHAPTER N. TITLE` on verso,
  `N.M SECTION TITLE` on recto). There are **no unnumbered body pages** other than the six
  blanks.
- **Hyperlink colouring is live and can fool a folio detector:** internal cross-references
  and index locators are blue, citation keys orange/brown, URLs blue monospace. On
  Bibliography and Index pages the blue numbers are page back-references, not folios. The
  true folio is always the outer-edge number in the running head, or bottom-centre on an
  opening page.
- The rotated `arXiv:1803.05316v3 [math.CT] 12 Oct 2018` stamp appears in the left margin
  of PDF page 1 only. It is the sole non-original mark and does not overlap body text.
- `pdftotext -layout` works cleanly on every page, so item headers can be harvested
  mechanically — subject to traps 1, 4 and 10 above.
- Bibliography (printed 323–330) uses alpha-style bracketed keys (`[Ada17]`, `[AGV71]`,
  `[Awo10]`, …), **not** numeric `[1]`, `[2]`. Entries end with back-references
  `(cit. on p. NNN)` whose numbers are **printed folios**. The Index (printed 331–341) is
  two-column with printed-folio locators including roman front-matter references
  (e.g. "wiring diagram, iv, 40, 43–48, …").
