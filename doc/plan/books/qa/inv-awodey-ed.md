# Inventory — Awodey edition relabel (Decision 5.4, branch (a))

**Scope of this document.** Read-only enumeration of every GitHub issue in
`jwiegley/category-theory` whose body carries an Awodey edition label, with the exact verbatim
substring in each. No issue was modified.

**Data provenance.** All 845 issues (numbers 1–1039, all states) fetched in one call on
2026-08-01:
`gh issue list --repo jwiegley/category-theory --state all --limit 2000 --json number,title,body,state`.
Five issues (#226, #643, #648, #658, #679) were re-fetched individually with `gh issue view` and
their bodies match the bulk fetch byte-for-byte on the relevant lines.

---

## 1. Headline: the "~34" figure in Decision 5.4 is a batch-local count, not the campaign total

`doc/plan/books/qa/judgement-calls.md:465–466` says verbatim:

> `pagemap.md` establishes that the campaign PDF is the 1st-ed CMU pre-print (OLG 49, September
> 2005); ~34 issues label it "2nd ed. (Oxford Logic Guides 52)", inherited from the `*-drafts.md`
> templates.

That "~34" traces to the T2 reviewer's own words in `doc/plan/books/qa/findings-tail-0.json:492`:

> `all 34 other issues in this batch say "(2nd ed.)"`

— i.e. 34 *within that reviewer's slice*. **Campaign-wide the real figure is 157 issues carrying
184 label occurrences.** Two things inflate it beyond the reviewer's batch:

1. Only 19 issues actually use the exact string `2nd ed. (Oxford Logic Guides 52)`. The dominant
   form, 135 occurrences across 113 issues, is the bare parenthetical `(2nd ed.)` with no series
   number — Decision 5.4's phrasing ("about 34 issues instead say `2nd ed. (Oxford Logic Guides
   52)`") does not describe the bulk of the corpus.
2. 86 of the 184 occurrences sit in `### Also covered by` cross-reference blocks, 78 of them inside
   **MacLane-titled** issues. A relabel restricted to `Awodey NN.N:`-titled issues would miss those
   78 entirely.

All 157 issues are `OPEN`. None is a Riehl issue (see §5).

---

## 2. The seven verbatim variants

Every label was extracted from the raw body. **No label spans a newline** — each is a contiguous
single-line substring, so a literal search-and-replace is safe. One occurrence sits inside a
blockquote (§6); none sits inside a code fence or the `<!-- catalog: … -->` trailer.

| # | Verbatim substring (exact, including `*` emphasis markers) | Issues | Occurrences | Action |
|---|---|---|---|---|
| A | `Awodey, *Category Theory* (2nd ed.)` | 113 | 135 | relabel |
| B | `Awodey, *Category Theory* (2nd edition)` | 22 | 26 | relabel |
| C | `Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52)` | 19 | 19 | relabel |
| D | `Awodey, *Category Theory* 2nd ed. (Oxford Logic Guides 52)` | 1 | 1 | relabel |
| E | `Awodey, *Category Theory* (2nd ed., Oxford University Press)` | 1 | 1 | relabel |
| F | `Awodey, *Category Theory* (2nd ed., Oxford Logic Guides 49)` | 1 | 1 | **leave** (#658, operator decision) |
| G | `Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print, September 2005)` | 1 | 1 | **do not touch** (#679, already correct) |

Note the distinguishing punctuation, which matters for mechanical replacement:

- **A/B/E/F/G** put the edition inside the parenthesis that follows the title with **no comma**
  after `*Category Theory*`.
- **C** has a **comma** after `*Category Theory*` and the edition **outside** the parenthesis:
  `*Category Theory*, 2nd ed. (Oxford …)`.
- **D** (#226 only) is C **without** that comma, and is additionally wrapped in `**…**` bold —
  the full line is
  `**Awodey, *Category Theory* 2nd ed. (Oxford Logic Guides 52), §1.4 (Examples of categories), printed pp. 6–7 (PDF pp. 15–16)**`.

Only #643 mixes variants (one A and one C — see §4).

Totals: 113 + 22 + 19 + 1 + 1 + 1 + 1 = 158 label-issue pairs over **157 distinct issues**
(#643 counted twice). Wrong-label issues = **156**. Excluding #658 per the operator's decision,
**155 issues need editing**, covering **182 occurrences** (184 minus #658's and #679's).

---

## 3. The correct replacement text

**Plain statement first: `pagemap.md` does not contain a ready-made short citation label.** It
states the edition facts, not a citation string. The relevant lines, verbatim:

`doc/plan/books/awodey/pagemap.md:7`

> `**First edition content — specifically the author's Carnegie Mellon pre-print/draft of the 1st edition (Oxford Logic Guides 49, OUP 2006), dated September 2005.** Evidence:`

`doc/plan/books/awodey/pagemap.md:175`

> `2. **Pre-print, not the OUP printing** — page numbers may drift slightly from the published 1st edition (and definitely from the 2nd edition). All page references in inventory records cite this PDF's own folios/PDF pages.`

The only label **already in the corpus** that is consistent with those lines is #679's, quoted
verbatim from the live body (line 3):

```
Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print, September 2005),
```

**Recommended replacement text for A–E (matching #679 exactly):**

```
Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print, September 2005)
```

This is a recommendation derived from #679 plus `pagemap.md:7`, not a string lifted from
`pagemap.md`. If the coordinator wants the campaign label to name the series volume as
`pagemap.md:7` does, the alternative would be
`Awodey, *Category Theory* (1st ed., Oxford Logic Guides 49; Carnegie Mellon pre-print, September 2005)`
— but that diverges from #679, which would then also need editing. **Choosing #679's exact form is
the only option that leaves #679 untouched**, as required.

For variant **C** the comma must be absorbed:
`Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52)` →
`Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print, September 2005)`.
For **D**, likewise, keeping the surrounding `**` bold markers.

---

## 4. #679 — confirmed accurate, do not touch

Live body line 3 of #679 (*"Awodey 5.5: Composition-reversal and identity laws for contramap"*),
verbatim:

> `Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print, September 2005),`
> `§5.5 Definition 5.28, printed p. 114 (PDF p. 123). Item covered: …`

Corroboration:

- `pagemap.md:7` (quoted in §3) fixes the campaign PDF as the CMU pre-print of the 1st edition,
  dated September 2005 — #679's label reproduces exactly that.
- `pagemap.md` TOC line 60 places §5.5 "Preservation of limits" at book p.112, and the +9 rule
  (`pagemap.md:112`: `**Rule: PDF page = printed book page + 9**`) gives printed 114 → PDF 123.
- `doc/plan/books/awodey/inventory/5.json` records
  `{"id": "awodey:5.5:def28", … "book_page": "114", "pdf_pages": [123]}`.

#679 carries the **only** accurate Awodey edition label among all 157. **No edit.** This matches
the standing verdict at `doc/plan/books/qa/all-verdicts.json:1062` ("Correct action on #679: no
edit") and the `remediation.json` "do not touch the edition line" note recorded at
`judgement-calls.md:472–474`.

---

## 5. Riehl and Mac Lane are not affected

`Riehl, *Category Theory in Context*, 2nd ed.` occurs 360 times and `Mac Lane` editions 434 times.
**Zero** of those matched the Awodey pattern — the extraction requires the literal token `Awodey`
immediately followed by `*Category Theory*` (Riehl's title is `*Category Theory in Context*`, which
cannot match). No Riehl-titled issue appears anywhere in §2's lists.

Two adjacency hazards for whoever applies the edits:

- **#590 and #534** appear in variant A *and* are also Group E targets in `remediation.json` for
  **adding** `(2nd ed.)` to a **Riehl** citation (`judgement-calls.md:475–477`: *"several entries
  in `remediation.json` add "(2nd ed.)" to Riehl citations (#497, #520, #590, #772) — that is the
  **Riehl** edition, which is not in dispute"*). A body-wide `s/(2nd ed.)//` on #590 would corrupt
  the Riehl line. Anchor every replacement on the full `Awodey, *Category Theory* …` prefix, never
  on the bare parenthetical.
- **#497, #520, #772** carry no Awodey edition label at all and are not in this inventory.

---

## 6. Occurrence-placement notes

- 98 occurrences are the `## Source` line of an `Awodey NN.N:`-titled issue — exactly one per
  Awodey-titled issue that has a label (98 issues).
- 86 occurrences are inside `### Also covered by` blocks: 78 in MacLane-titled issues, 8 in
  Awodey-titled issues.
- **#671** has 3 occurrences, one of which is inside a **blockquote** in a `### Correction (QA
  audit)` section, verbatim:
  `> Awodey, *Category Theory* (2nd ed.), §8.8 (Topoi), Remark 8.18, printed page 211 (PDF page 220), item …`
  Relabelling it keeps the correction text consistent with the block it prescribes; flagged only so
  the change is not a surprise.
- No occurrence is inside a code fence or inside the `<!-- catalog: {"ids": …} -->` trailer.

---

## 7. Out of scope but adjacent: 51 issues cite Awodey with **no** edition label

208 issues cite the Awodey book; 157 carry an edition label, so **51 cite it with none** — e.g.
`Awodey, *Category Theory*, §9.7 "Locally cartesian closed categories".` (#732) and
`Awodey, *Category Theory* §5.5 (printed p. 114, PDF p. 123)` (#654). Sixteen of these are
Awodey-titled: **#724, #725, #726, #727, #728, #729, #730, #731, #732, #733, #734, #735, #736,
#737, #738, #739** (the whole Chapter 9 run). Decision 5.4 as written says nothing about them.
They are not *wrong* — they assert no edition — so they are excluded from §2. If the goal is a
uniform campaign label, they are the remaining gap; that is a decision for the operator, not a
finding.

---

## 8. Full enumeration

### Variant A — `Awodey, *Category Theory* (2nd ed.)` — 113 issues, 135 occurrences

#234, #237, #238 (x2), #241, #245, #247, #248, #250, #253, #254, #261, #266 (x2), #270, #271, #275,
#277, #279, #296 (x2), #315 (x3), #316, #321, #324 (x3), #328 (x2), #335, #341 (x2), #345, #346,
#369, #374 (x2), #384, #389, #392, #403 (x2), #404, #405, #407, #414 (x2), #422 (x2), #424, #425,
#428, #429, #442, #447, #458, #479 (x2), #503, #530 (x2), #534, #590, #643, #649, #650, #651, #652,
#653, #654 (x3), #655, #656, #657, #659, #660, #661, #662, #663, #664, #665, #666, #667, #668,
#669, #670, #671 (x3), #672, #673, #674, #675, #676, #677, #678, #680, #681, #682, #683, #684,
#685, #686, #687, #688, #689, #690, #691, #692, #693, #694, #695, #696, #697 (x3), #698, #699,
#700, #701, #702, #703, #704, #705 (x2), #706, #707, #708, #709, #710, #711, #712

### Variant B — `Awodey, *Category Theory* (2nd edition)` — 22 issues, 26 occurrences

#252 (x2), #463 (x2), #466 (x2), #469, #471 (x2), #476, #482, #637, #740, #741, #742, #743, #744,
#745, #746, #747, #748, #749, #750, #751, #752, #753

### Variant C — `Awodey, *Category Theory*, 2nd ed. (Oxford Logic Guides 52)` — 19 issues, 19 occurrences

#640, #641, #642, #643, #644, #645, #646, #647, #713, #714, #715, #716, #717, #718, #719, #720,
#721, #722, #723

### Variant D — `Awodey, *Category Theory* 2nd ed. (Oxford Logic Guides 52)` — 1 issue

#226 (*"MacLane I.2: The roster of standard large categories"*), inside a bolded `### Also covered
by` line.

### Variant E — `Awodey, *Category Theory* (2nd ed., Oxford University Press)` — 1 issue

#648 (*"Awodey 2.1: Monomorphisms in Mon are exactly the injective homomorphisms"*), `## Source`
line. This variant is not mentioned anywhere in the QA findings; it is a third drafting template
not previously enumerated.

### Variant F — `Awodey, *Category Theory* (2nd ed., Oxford Logic Guides 49)` — 1 issue — **LEAVE**

#658 (*"Awodey 3.2: The coproduct bifunctor + : C ∏ C ⟶ C"*). Per Decision 5.4 branch (a), #658 is
left as-is and the `49 → 52` remediation is **not** applied. Recorded here for completeness: after
the relabel #658 will be the only Awodey citation in the corpus still reading "2nd ed.", and its
volume number 49 is the *first*-edition volume — so its label remains internally inconsistent
("2nd ed." + OLG 49). Flagging, not disputing: the operator's instruction is explicit.

### Variant G — `Awodey, *Category Theory* (1st ed., Carnegie Mellon pre-print, September 2005)` — 1 issue — **DO NOT TOUCH**

#679. See §4.
