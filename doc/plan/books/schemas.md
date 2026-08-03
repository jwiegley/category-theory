# Campaign 3 artifact schemas (frozen with the plan)

## Inventory range report (Phase A agent output; one JSON object per range)

```json
{
  "book": "maclane",
  "range": {"pdf_start": 21, "pdf_end": 40},
  "pages": [
    {
      "pdf_page": 21,
      "book_page": "7",
      "empty": false,
      "items": ["maclane:I.2:def-category", "..."],
      "notes": "optional: legibility issues, anomalies"
    }
  ],
  "items": [
    {
      "id": "maclane:I.2:def-category",
      "kind": "definition",
      "number": null,
      "name": "category (metacategory made concrete)",
      "statement_summary": "PARAPHRASE, never verbatim: what is defined/claimed, hypotheses, conclusion",
      "book_section": "I.2",
      "book_page": "7",
      "pdf_pages": [21, 22],
      "cross_refs": ["maclane:I.1:def-metacategory"],
      "flags": []
    }
  ]
}
```

Rules: `pages` MUST contain an entry for EVERY pdf page in the range
(page accounting is the completeness gate); `empty: true` pages still get
an entry. `kind` ∈ definition | rough-definition | theorem | proposition | lemma |
corollary | exercise | construction | remark | example | equation.
(`example` added 2026-07-23 for Awodey, which typesets Example as a
first-class numbered environment sharing the chapter counter.
`rough-definition` and `equation` added 2026-07-29 for Seven Sketches, see
below.)

⚠ **SEVEN SKETCHES: DISPLAYED EQUATIONS SHARE THE ITEM COUNTER.** Verified in
A0 against the page images, then mechanically across the whole text: there is
exactly ONE counter per chapter and numbered displays draw from it alongside
every named environment. Printed pp. 31–32 run Proposition 1.111 → Exercise
1.112 → Example 1.113 → Exercise 1.114 → Theorem 1.115 → **equation (1.116)**
→ Example 1.117. Consequences, both mandatory:
- A **NUMBERING-CONTINUITY CHECK MUST NOT REPORT EQUATION NUMBERS AS GAPS.**
  Chapter 1 has named items only at 117 of its 125 numbers; the missing
  {2,3,5,8,15,96,108,116} are all numbered displays, each verified. An agent
  that "fills the gaps" will invent items that do not exist.
- Record an `equation` item ONLY when the display carries a distinct
  formalizable claim (e.g. (1.96), the Galois-connection condition
  `f(p) ≤ q ⟺ p ≤ g(q)`). For a mere intermediate step, do not create an
  item — instead note in the owning page entry that the number is consumed by
  a display, so the continuity check stays satisfiable.
`rough-definition` is Seven Sketches' own informal/provisional Definition
header (6 occurrences: 4.45, 4.51, 5.33, 6.68, 6.91, 6.98), numbered from the
same shared counter and boxed like a Definition. Neither source agent
enumerated it; the reconciler caught it.

`number` is the book's own number when
one exists ("VII.3.2", "2.7", "1.32"). IDs: `<book>:<chapter>.<section>:<kind><number|slug>`
with book ∈ maclane | awodey | 7sketches | riehl. ⚠ **Book 3 uses TWO different
spellings and both are load-bearing** — the item-ID prefix is `7sketches:`
(this schema, and `check_graph.py`'s ITEM_ID regex), while the DIRECTORY and
the `file_chapter.py` BOOK argument are `seven-sketches` (its PROJECT map is
`{"maclane":"4","awodey":"5","seven-sketches":"6"}`, and `ISSUEMAP` is
`<books>/<BOOK>/issue-map.json`). Do not "fix" either one in isolation: the
prefix appears in every filed item id, the directory in every tool path. An
empty `doc/plan/books/7sketches/` exists as a stale scaffold from setup — it
is NOT the live directory. `flags` free-form, e.g.
"unnumbered-construction", "continued-from-previous-page",
"statement-illegible" (the last triggers a re-read in Phase B).

## Coverage record (Phase C output; one per item, extended by Phase D)

```json
{
  "id": "maclane:V.6:thm2",
  "classification": "PARTIAL",
  "aliases": ["adjoint functor theorem", "AFT", "SolutionSet", "GAFT", "Freyd"],
  "evidence": [
    {"file": "Adjunction/GAFT.v", "line": 210, "symbol": "GAFT",
     "intree_statement": "QUOTED Coq statement (types/hypotheses), trimmed"}
  ],
  "statement_record": {
    "book": "paraphrase of the book's statement",
    "intree": "quoted in-tree statement",
    "strength_comparison": "same | intree-weaker: <how> | intree-stronger: <how>"
  },
  "gap": "for PARTIAL only: precisely what is missing",
  "negative_search_log": ["rg -i 'solution set' -- searched, 0 hits", "..."],
  "out_of_scope_reason": null,
  "verifier": {"verdict": "CONFIRMED", "notes": "blind search found same evidence"}
}
```

Rules: PRESENT/PARTIAL require `evidence` + `statement_record`; ABSENT
requires `negative_search_log` (aliases + commands actually run);
OUT_OF_SCOPE requires `out_of_scope_reason`. Phase D fills `verifier`
(CONFIRMED | OVERTURNED:<new classification>) after its own blind pass.

## Issue draft (Phase E output; one markdown block per issue)

Exactly the frozen issue contract sections (Source / Background /
Current state in the library / Work to be done / Definition of Done /
Verification / Dependencies), preceded by a YAML header used only for
filing (not part of the body):

```yaml
title: "MacLane V.6: ..."
labels: [book:maclane, kind:theory, coverage-gap]
projects: [4]
covers: [maclane:V.6:thm2]
deps_item_ids: [maclane:V.1:def-limit]
```

and ending the BODY with the machine trailer:
`<!-- catalog: {"ids":["maclane:V.6:thm2"],"deps":["maclane:V.1:def-limit"]} -->`

## Ledger (doc/plan/books/ledger.tsv, tab-separated, append-only)

`item_id  classification  issue  projects  evidence_or_note`
- `issue`: `#N` once filed; `-` for PRESENT/OUT_OF_SCOPE/pending.
- `projects`: comma-separated project numbers, `-` if none.
- One row per item ID **except for a genuinely MULTI-PART item whose parts land
  in different issues** (a book item drawing two independent consequences that no
  single existing issue can absorb). Such an item gets ONE ROW PER (item, issue)
  pair, and every one of its rows must name the part in the note column. This is
  the sanctioned exception, not a collision: the Awodey Ch5 audit confirmed the
  split of `awodey:5.5:remark-hom-coproduct` (hom-out-of-a-coproduct iso -> #428;
  ultrafilter corollary -> #654) as correct, since neither target could absorb the
  other. In `issue-map.json` such an item uses `"<item-id>" : <primary issue>` plus
  `"<item-id>@<other issue>" : <other issue>` for each further leg.
- A filed issue covering k items yields k rows.
- Appended SYNCHRONOUSLY after each successful gh mutation (idempotency:
  pre-flight the ledger + `gh issue list --label book:<book>` on resume).

## Book 4: Riehl (added 2026-07-30, queued behind Seven Sketches)

Emily Riehl, *Category Theory in Context*. PDF
`/Users/johnw/Desktop/riehl-category-theory-in-context.pdf`, **296 pages**
(letter, LaTeX+hyperref, pdfTeX 1.40.29). GitHub project **10** ("Riehl"),
label `book:riehl`, item-ID prefix `riehl:`, directory
`doc/plan/books/riehl/`. Unlike book 3, the prefix and the directory name
AGREE here — do not replicate the `7sketches`/`seven-sketches` split.

Registered in the tooling: `file_chapter.py` and `validate_drafts.py` PROJECT
maps, `check_graph.py`'s ITEM_ID regex and its issue-map loop.

⚠ Page count came from **`pdfinfo`**, not the `/Count` trick used for the
first three books: this PDF stores its page tree in compressed object
streams, so `strings | grep '/Count'` and a raw `/Type /Page` count both
return nothing. Use `pdfinfo <pdf> | grep ^Pages` first from now on.

### Duplicates entry (Phase E output, `duplicates-<R>.json`)

`{"item_id", "issue", "part", "append_block"}` where **`part`** is a short
(≤60 char) phrase naming WHICH PART of the item this target covers. It is
REQUIRED whenever an item lands on more than one issue and empty otherwise;
`file_chapter.py` writes it verbatim into the ledger's note column to satisfy
the multi-part rule above.

⚠ **Why it is a structured field and not parsed from the prose.** Recovering
the part from `append_block` failed FOUR times, because each chapter phrased
the citation differently: `"(first leg) — printed pp. …"` (Awodey 9),
`"(parts (a) and (b); part (c) is recorded on #252)"` (Awodey 10 — nested
parens, and naming the OTHER leg second so a greedy match inverts the label),
`"item \`id\` — the second half of the remark"` (7S 2), and
`"Example 3.74, clause 2 (free preorder and free category on a graph)"`
(7S 3). Each fix worked for its chapter and missed the next. Do not add a
fifth regex — emit the field.

### Riehl numbering (A0-verified 2026-07-31) — DIFFERENT FROM BOOKS 1-3

**ONE SHARED COUNTER PER *SECTION***, written `chapter.section.item`, running
across Definition / Theorem / Proposition / Lemma / Corollary / Example /
Remark / Notation **and also across numbered displayed equations and diagrams**.
It is NOT per-chapter (books 2-3) and NOT per-kind.

Proved from the page: §3.1 runs Definition 3.1.1, Definition 3.1.2, then the
numbered displays **(3.1.3)** and **(3.1.4)**, then Definition 3.1.5, Definition
3.1.6, Proposition 3.1.7. So the equation-counter trap of Seven Sketches is LIVE
here too — an inventory that reads (3.1.3) as an environment is wrong, and one
that assumes 3.1.3 must exist as an environment will fail to find it.

**EXERCISES ARE ON A SEPARATE COUNTER** in LOWERCASE ROMAN, collected at the end
of each SECTION under an unnumbered "Exercises." heading: `1.1.i`, `1.1.ii`, …
They do NOT advance the arabic counter (§1.1 ends at Lemma 1.1.14 and its
exercises are 1.1.i ff., not 1.1.15). **206 body exercises** in Chapters 1-6
(the TOC agent said 216; the reconciler re-extracted every definition site and
corrected it downward — use 206). No solutions anywhere in the book.

`riehl:` item IDs therefore use the book's own dotted number:
`riehl:<chapter>.<section>:<kind><item>` for arabic items and
`riehl:<chapter>.<section>:ex<roman>` for exercises (e.g. `riehl:1.1:def1`,
`riehl:3.1:prop7`, `riehl:1.1:exiii`).

Other A0 facts: **SECOND EDITION**, a locally recompiled author's copy — **NOT
the Dover/AMS print pagination**, so never cite these folios as Dover pages.
Uniform offset **+20** (printed = pdf − 20) over PDF 21-296 only; front matter
PDF 1-20 is lowercase roman at offset 0. Seven blank pages, all counted. Chapter
label for the Epilogue is **`E`**. Section index **0 is legal** — display
(1.0.1) sits in the Chapter 1 roadmap before §1.1 exists (the only instance).
Chapters 3 and 4 were REORDERED in the second edition and §4.5 is new, so
first-edition section numbers for those chapters do not transfer.


## PARTIAL vs ABSENT: the boundary rule (written down 2026-08-01, after the fact)

This rule governed all 2920 classifications in the campaign and existed **only** in one
verifier's note on `riehl:6.2:cor7` until the Chapter 6 audit flagged that a future chapter had
no artifact to inherit it from. Stated now so it survives:

> **PARTIAL requires a PROVED statement covering part of the item. A never-instantiated class
> does not qualify.**

Concretely, as applied across Riehl Ch6's 85 items and confirmed by an independent blind pass:

- **PARTIAL** — every one rests on a `Qed`'d theorem: `Kan_Limit`, `yoneda_reduction`,
  `coyoneda_reduction`, `coend_ump`, `Adjunction_Monad`, `localization_universal`.
- **ABSENT** — every one rests on definitions-without-instances. `Theory/Kan/Extension.v`
  declares `LeftKan`/`RightKan`, but both are *assumed*, have zero in-tree instances, and the
  composition theorems each assume ONE class twice rather than both. A class you cannot
  inhabit proves nothing about the book's claim.

This is why Riehl Ch6 scored **1 PRESENT in 85** while sitting on a file literally named
`Theory/Kan/Extension.v`. A blind reclassification of §6.2 and §6.5 with no access to
`doc/plan/` independently found **zero PRESENT** in either section, and of nine disagreements
six ran the direction where the campaign was the MORE generous of the two. The rule is
defensible and was applied consistently; it just needed writing down.

**Corollary for appends:** a NEAR MISS is not evidence. `riehl:6.5:exix`'s log names
`Monad/Adjunction.v:48`'s `Adjunction_Monad` and then says "NEAR MISS, deliberately NOT counted
as evidence -- nothing in the tree says that monad IS `Ran_G G`". Record the near miss so the
implementer finds it; do not let it move the classification.
