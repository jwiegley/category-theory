# QA investigation — DECISIONS 1.5 (item-id labels) and 1.6 (Group A body riders)

Read-only verification against the LIVE GitHub bodies, fetched 2026-08-01 with
`GH_TOKEN=$(gh auth token --user jwiegley) gh issue view <N> --repo jwiegley/category-theory --json body`.
Native edges read from `repos/jwiegley/category-theory/issues/<N>/dependencies/blocked_by`.
Every quotation below is verbatim from the fetched body; line numbers are 1-based within the body text.

---

## Part (a) — DECISION 1.5: missing item-id labels on #444 / #453 / #455

**Verdict: NOTHING TO FIX. All three labels are already present and correct, and no literal
ellipsis appears in any of the three live bodies.**

### The three lines the plan names

| Issue | Line | Exact current text |
|---|---|---|
| **#444** | 67 | ``Depends on: #422 (`maclane:V.2:remark1`) — supplies the preorder-limit identification (products in a preorder are greatest lower bounds) used to prove `Ord^op` small-complete`` |
| **#453** | 69 | ``Depends on: #353 (`maclane:IV.2:construction2`) — supplies the Δ-adjunction characterization of colimits consumed by the Riehl §4.7 cocompleteness-corollary checkbox`` |
| **#455** | 63 | ``Depends on: #413 (`maclane:V.1:ex2`) — supplies `CompHaus` and the creation of limits by its underlying-set functor, the subject of the discrete case`` |

All three carry exactly the label the plan prescribes:
`maclane:V.2:remark1`, `maclane:IV.2:construction2`, `maclane:V.1:ex2`.

### Ellipsis scan

Scanned every line of #444, #453 and #455 for `...` and `…`:

```
444 no ellipsis in any maclane: id
453 no ellipsis in any maclane: id
455 no ellipsis in any maclane: id
```

The feared `maclane:IV.2:...` is **not** in any live body. (Out of scope but checked, since
judgement-call F3 flagged the same risk there: **#458** line 130 reads
``- Related (NOT blocking): #416 (`maclane:V.2:thm1`) — the products-and-equalizers route to `Complete Top`; the direct route is equally acceptable.``
and line 133 even says ``item id `maclane:V.2:thm1`, not an ellipsis.`` — also clean.)

### Every `Depends on:` line in the three bodies

```
#444
 67  Depends on: #422 (`maclane:V.2:remark1`) — supplies the preorder-limit identification (products in a preorder are greatest lower bounds) used to prove `Ord^op` small-complete
 68  Depends on: #436 (`maclane:V.6:thm2`)
 69  Depends on: #437 (`maclane:V.6:thm3`)

#453
 69  Depends on: #353 (`maclane:IV.2:construction2`) — supplies the Δ-adjunction characterization of colimits consumed by the Riehl §4.7 cocompleteness-corollary checkbox
 70  Depends on: #438 (`maclane:V.6:lem1`) — supplies the comma-projection creation result that Work item 1's monos lemma runs through
 71  Depends on: #452 (`maclane:V.8:thm1`)
 72  Depends on: #451 (`maclane:V.8:def1`)
 73  Depends on: #445 (`maclane:V.7:def2`)

#455
 63  Depends on: #413 (`maclane:V.1:ex2`) — supplies `CompHaus` and the creation of limits by its underlying-set functor, the subject of the discrete case
 64  Depends on: #259
 65  Depends on: #436 (`maclane:V.6:thm2`)
 66  Depends on: #453 (`maclane:V.8:thm2`)
```

One line is bare: **#455 line 64, `Depends on: #259`**, with no `(item-id)` label. #259 does have an
id (`<!-- catalog: {"ids": ["maclane:I.7:construction4", "7sketches:7.3.2:def7.25"], "deps": []} -->`),
and #455's own trailer records this dep as the literal string `"#259"`:

```
<!-- catalog: {"ids": [...], "deps": ["#259", "maclane:V.6:thm2", "maclane:V.8:thm2", "maclane:V.1:ex2"]} -->
```

**This does NOT trip invariant 3.** `check_graph.py`'s `unresolved_deps()` only collects item-ids
that appear on a `Depends on:` line *outside* a `RESOLVED_LABEL` (`#\d+\s*\(\s*`[^`]*`[^)]*\)`) match.
A bare `Depends on: #259` contains no item-id at all, so it yields nothing. Confirmed by running the
real function from `doc/plan/books/tools/check_graph.py` against the live bodies:

```
444 unresolved: []  body_deps: [422, 436, 437]
453 unresolved: []  body_deps: [353, 438, 445, 451, 452]
455 unresolved: []  body_deps: [259, 413, 436, 453]
```

So the labelling clean-up 1.5 was worried about is either already applied or was never needed.
Adding `` (`maclane:I.7:construction4`) `` to #455's #259 line would be cosmetic uniformity only.

---

## Part (b) — DECISION 1.6: the four Group A body riders

**Verdict: ALL FOUR ARE ABSENT — and so are their edge halves.** These four rows were never
applied at all, in either half. #704 alone shows a *partial*, and the part that is present comes
from a different edit, not from the planned one.

The plan text for each is in `doc/plan/books/qa/plan-tail-sections.md`
(#704/#926/#959 at lines 27–36, section 1; #485 at line 439, section 3) and
`doc/plan/books/qa/plan-tail-432-1038.md` (F8a for #704, line 157 ff.).

### Native `blocked_by` — the edge halves were not run either

```
#485 blocked_by: 481 484        (plan: → [481])
#926 blocked_by: 345 705        (plan: drop 705)
#959 blocked_by: 425 428 720 481 406 671   (plan: drop 720 and 671)
#704 blocked_by: 311 428 227    (plan: drop all three)
```

### #485 — Work-bullet rewrite routing through `beck_monadicity`: **ABSENT**

Planned change: ``routing through the completed Beck theorem (the §VI.7 Theorem 1 issue) / `beck_monadicity` ``
→ ``routing through the in-tree `beck_monadicity` (`Monad/Monadicity/Beck.v:739`)``.

Live body line 13, verbatim (the OLD text, unchanged):

```
- Prove Ex. 7 (CTT ⇒ `K` an equivalence) and Ex. 8 (VTT ⇒ `K` an equivalence), routing through the completed Beck theorem (the §VI.7 Theorem 1 issue) / `beck_monadicity`; reconcile the crude form (`crude_monadicity`) with the `C_G`-quantified CTT.
```

The rest of the row is equally unapplied. Live lines 33–36:

```
33  Depends on: #481 (`maclane:VI.7:def2`)
34  Depends on: #484 (`maclane:VI.7:thm1`)
35
36  <!-- catalog: {"ids":["maclane:VI.7:def3","maclane:VI.7:ex7","maclane:VI.7:ex8"],"deps":["maclane:VI.7:def2","maclane:VI.7:thm1"]} -->
```

No `- Related (NOT blocking): #484 …` line exists anywhere in the body; trailer `deps` still holds
`maclane:VI.7:thm1`; `blocked_by` still holds 484.

### #926 — the `Graph` name-clash note: **ABSENT**

Planned: replace the #705 Depends-on line with a `- Related (NOT blocking):` line whose tail reads
``NOTE: #705's Work item 1 also names its category `Graph` (in `Instance/Parallel/Graphs.v`); this issue's `Instance/Graph.v` must pick a distinct name (e.g. `SimpleGraph`) or the two cannot be imported together.``

Live body, `## Dependencies` (lines 65–70), verbatim and complete:

```
65  ## Dependencies
66
67  - Depends on: #345 (the category of elements of a set-valued functor)
68  - Depends on: #705 (the category of directed graphs as a functor category — the nearest in-tree graph development; this issue must build the *simple*-graph variant and relate the two)
69
70  <!-- catalog: {"ids":["riehl:2.0:construction-ncolor","riehl:2.4:example3"],"deps":["#345","#705"]} -->
```

The strings `SimpleGraph`, `Instance/Parallel/Graphs.v` and `Related (NOT blocking)` appear
**nowhere** in the body. The nearest existing text is DoD line 38, which is the ORIGINAL wording and
carries no clash warning:

```
- [ ] `Graph` is defined for **simple** graphs, and the header states precisely how it differs from `Quiver`/`QuiverCategory` and from #705's directed graphs
```

Note this also interacts with DECISIONS §3.3 (`[+] Rename #705's` directed-graph category to
`Quiver`/`DiGraph`; #926 keeps `Graph`) — neither half of that pair is visible on #926 either.

### #959 — dropping #720/#671 from the In-tree donors line: **ABSENT**

Live "In-tree donors" paragraph, lines 74–76, verbatim — **both `#720` and `#671` are still there**:

```
In-tree donors: `Functor/Hom.v`, `Theory/Equivalence/Limit.v`, `Structure/Limit/Preservation.v`,
`Structure/UniversalProperty/Limit.v`, `Structure/Limit/Weighted.v`, `Instance/Fun.v`, #425, #428,
#720, #481, #406, #671.
```

`## Dependencies`, lines 108–116, verbatim:

```
108  ## Dependencies
109  Depends on: #425
110  Depends on: #428
111  Depends on: #720
112  Depends on: #481
113  Depends on: #406
114  Depends on: #671
115
116  <!-- catalog: {"ids":["riehl:3.5:thm5","riehl:3.5:thm10","riehl:3.5:exii","riehl:3.5:remark14"],"deps":["#425","#428","#720","#481","#406","#671"]} -->
```

No `- Related (NOT blocking)` line for either #720 or #671. (Both planned Related lines are quoted
in `plan-tail-sections.md:35-36`.)

**Counter-evidence that other passes DID run on this issue:** the `remediation.json` group-E fix for
#959 (`Theory/Equivalence/Limit.v:353` → `:350`) IS applied — live line 26 reads
``  (`Theory/Equivalence/Limit.v:350`), which must be discharged at the Yoneda embedding.`` and the
string `:353` no longer occurs. So `remediation.json` was executed; these riders simply were not in it.

### #704 — the whole `## Dependencies` block replacement: **ABSENT (block still mangled), with an unrelated PARTIAL edit present**

Planned (F8a / plan-tail-sections F1): replace the whole block with `None.` plus three
`- Related (NOT blocking):` lines (#227, #311, #428), trailer `"deps": []`, `ids` preserved,
and three `blocked_by` deletions.

Live body, lines 124–132, verbatim:

```
124  ## Dependencies
125
126  Depends on: #311 (MacLane III.1: A universal element for the contravariant
127  Depends on: #227 — creates `Instance/Sets/Powerset.v`
128  - Related (NOT blocking): coordinate the module layout so the covariant and contravariant halves coexist.
129  power-set functor)
130  Depends on: #428 (MacLane V.4: Hom-functors are continuous) — the book's stated
131  route for Exercise 1
132
```

Trailer, line 180 (unchanged, all three deps still present):

```
<!-- catalog: {"ids": ["awodey:7.5:construction-sets-double-dual", "awodey:7:ex9", "awodey:7:ex1", "awodey:9:ex5", "riehl:1.3:example7", "riehl:4.4:exiii"], "deps": ["#311", "#428", "#227"]} -->
```

**What is present, and why it is not the planned edit.** The plan quotes the pre-edit #227 line as
one physical line:

```
Depends on: #227 — creates `Instance/Sets/Powerset.v`; coordinate the module layout so the covariant and contravariant halves coexist.
```

Live, that trailing clause has been split off onto its own `- Related (NOT blocking):` line (128).
That is the F2-shaped *hedge-split* treatment, **not** the F1/F8a whole-block replacement: the block
is still mangled (line 129 `power-set functor)` is still orphaned from line 126), all three
`Depends on:` lines survive, `None.` was never written, none of the three planned Related lines
(which each name their `#N` and reason) exist, the trailer is untouched, and all three native edges
survive. Worse, the split line as written carries **no issue number at all**, so it is inert:
`check_graph.py` still reports `body_deps(#704) = [227, 311, 428]`.

I could not locate an instruction anywhere in `plan-head-216-471.md`, `plan-tail-432-1038.md`,
`plan-tail-sections.md` or `remediation.json` that produces line 128 in this form —
`grep -rn "coordinate the module layout"` over those four files returns only the #382/#745 record in
`remediation.json:3785` and the two verbatim *pre-edit* quotations of #704's block. **So the
provenance of line 128 is unexplained**; a hand edit from an earlier pass is the likeliest
explanation, but I have no positive evidence for it and am not guessing.

Two adjacent LOW items on #704 for the coordinator's bookkeeping:
- the `remediation.json` group-F whitespace fix (`## Work to be done\n\n\n` → `\n\n`) **IS applied**;
- the still-open F8a rider "insert a blank line between `` > `P X`. `` and `` Suggested module: … ``"
  is **NOT** applied — live lines 60–61 are `` > `P X`. `` immediately followed by
  ``Suggested module: `Instance/Sets/Powerset.v`.``.

---

## The broader pattern this exposes

DECISIONS 1.6 records Group A as "done". That is true of the **head plan's** Group A
(`plan-head-216-471.md`, issues #216–#471) and false of the **tail chunks'** Group A. Spot check:

```
head plan Group A (applied — target edges gone):
  #263 blocked_by:            (was 260)
  #311 blocked_by: 303        (was 227, 303)
  #333 blocked_by:            (was 259)
  #363 blocked_by:            (was 220)
  #375 blocked_by:            (was 374)

tail chunks' Group A (NOT applied — every demotion target still present):
  #723  blocked_by: 403 404 718     (demote 404)
  #785  blocked_by: 223             (demote 223)
  #814  blocked_by: 813 811 785 262 (demote 262)
  #822  blocked_by: 776             (demote 776)
  #886  blocked_by: 402 885         (demote 402)
  #890  blocked_by: 460 259 268     (demote 460)
  #918  blocked_by: 712 231         (demote 231)
  #986  blocked_by: 559 437         (demote 437)
  #1008 blocked_by: 467 481 407     (demote 481)
```

So the scope of 1.6 is larger than the four named rows: **the entire tail-chunk Group A appears
unapplied, edges and bodies alike**, including the #890 fifth edit that 1.6 calls MANDATORY (#890
still has `blocked_by: 460 259 268`). The four riders are not stragglers from a mostly-complete
pass; they are part of a pass that did not run. `remediation.json` (which was run — two #959/#704
items from it are live) covers Groups C/D/E/F, not the tail Group A demotions.

## What I could not settle

- The provenance of #704 body line 128. Evidence missing: an instruction anywhere in the four plan
  files that yields exactly that line. I searched all four; nothing matches.
- Whether the tail-chunk Group A was *deliberately* deferred rather than dropped. I have no
  execution log for the Group A pass — only the "Group A is recorded as done" claim in
  `judgement-calls.md` §1.6 and the live-state evidence above, which contradicts it for the tail
  chunks. The missing evidence is whatever run record marked Group A done and what issue range it
  covered.
