# mf-final.json — merge and conflict report

Merged from `mf-edges.json` (28), `mf-naming.json` (119), `mf-content.json` (28),
`mf-crossfile.json` (231) = 406 candidate edits → **405 edits** in
`doc/plan/books/qa/mf-final.json` (one exact duplicate removed, see C2).

**Array order is application order.** Element schema is unchanged from the four sources
(`issue`, `decision`, `mode`, `find`/`replace`/`block`/`file`, `note`). Every change I made to a
source entry is recorded inline in that entry's `note`, tagged `[MERGE C<n>]`.

## 1. Totals

| | |
|---|---|
| Total edits | **405** |
| Issues touched | 223 |
| Cross-file targets | `ledger.tsv`, `graph/serialize-groups.json`, `seven-sketches/issue-map.json` |

By mode: `replace_text` 348 · `file_edit` 14 · `append_block` 11 · `trailer_deps` 11 ·
`trailer_ids` 7 · `edge_remove` 9 · `edge_add` 5.

## 2. Edits per decision

| § | n | § | n | § | n | § | n |
|---|--:|---|--:|---|--:|---|--:|
| 1.6 | 18 | 2.19 | 4 | 3.9 | 5 | 5.3 | 1 |
| 2.6 | 1 | 3.1 | 6 | 4.1 | 6 | 5.4 | 182 |
| 2.7 | 4 | 3.2 | 95 | 4.3 | 1 | 5.6 | 6 |
| 2.11 | 1 | 3.3 | 9 | 4.4 | 1 | 6.1 | 1 |
| 2.12 | 3 | 3.5 | 3 | 4.5 | 3 | 6.2 | 8 |
| 2.14 | 3 | 3.6 | 4 | 4.8 | 5 | 6.3 | 6 |
| 2.15 | 5 | 3.7 | 1 | 5.1 | 3 | 6.4 | 1 |
| 2.16 | 8 | 3.8 | 2 | 5.2 | 4 | | |
| 2.17 | 5 | | | | | | |

## 3. Validation performed

All 223 issue bodies and all three cross-file targets were re-fetched live (2026-08-01) and the
whole manifest was **simulated in array order**:

- every `replace_text` / `file_edit` `find` matches **exactly once** at the moment it is applied —
  0 failures across 362 text edits, both against the pristine body and against the body as
  mutated by every earlier edit in the merged order;
- `serialize-groups.json` and `seven-sketches/issue-map.json` still parse as JSON afterwards;
- `ledger.tsv` still has 5 tab-separated columns on every row;
- `lint_issue_bodies.py` rules L1–L7 re-implemented and run on the post-edit bodies:
  **0 new defects**, and 0 pre-existing defects in the touched set.

## 4. Conflicts found and how they were resolved

### C1 — `#1038` takes 2.19 and 3.2, and 2.19 re-seeds the identifier 3.2 retires (CONTENT CONFLICT, fixed)

`mf-edges.json[15]` (2.19) adds two new `Depends on:` lines whose labels read ``​`CRng`​`` and
``Field ⟶ CRng``. Decision 3.2 renames #257's commutative category to `CRing`, and
`mf-naming.json[89–92]` scrubs `CRng` from four *other* places in this same body. The two edits
compose textually (disjoint find-strings) but not semantically: applying both leaves #1038 as the
only issue in the tree still naming the retired identifier, on the one line the 3.2 sweep cannot
match because 2.19 creates it.

**Resolved:** rewrote `mf-edges.json[15]`'s `replace` to `CRing` / `Field ⟶ CRing`. Note tagged.

### C2 — `#869` trailer_ids emitted twice, byte-identical (DUPLICATE, deduped)

`mf-edges.json[24]` (3.6) and `mf-crossfile.json[230]` (5.2 edit 4/4) both set #869's trailer
`ids` to the same array `["7sketches:6.3.1:thm6.58","7sketches:6.3.1:ex6.57"]`. Both notes demand
"apply LAST". Not a contradiction — the operator required 3.6 and 5.2 be reconciled in one pass,
and they were, independently, to the same value.

**Resolved:** dropped the `mf-edges.json` copy; the surviving `mf-crossfile.json` entry discharges
both decisions and is ordered **dead last among the trailer edits**, after the three 5.2 cross-file
edits (`ledger.tsv:1964` rewrite, the new #869 PARTIAL row, the `issue-map.json` `@869` leg) — as
both source notes require, because `7sketches:6.3.1:ex6.57` resolves to #868 alone until those land.

### C3 — `#518` find-string collision between 3.2 and 3.5 (ORDER-CRITICAL, resolved by ordering)

`mf-edges.json[26]` (3.5) finds `` Suggested module: `Instance/GroupRing.v`. ``. That string is a
**substring of** `mf-naming.json[77]`'s (3.2) find — the whole Work paragraph — and is re-emitted
verbatim inside `mf-naming.json[77]`'s replace. Applied 3.5-first, the 3.2 edit silently no-ops and
five `Rng`→`Ring` renames vanish from #518's Work paragraph.

**Resolved:** the merged order runs all `mf-naming.json` `replace_text` (bucket 10) before all
`mf-edges.json` `replace_text` (bucket 40). Simulation confirms both apply. Both entries carry an
ORDER-CRITICAL note.

This was the **only** substring/find-in-replace collision in the corpus outside the 6.2 pairs.

### C4 — the four 6.2 blockquote relocations are delete/insert pairs (ORDER-CRITICAL, resolved)

`#843`, `#827`, `#829`, `#832`: edit A deletes the audit blockquote from the end of
`## Dependencies`, edit B re-emits it verbatim before `## Definition of Done`. B's `replace`
*contains* A's `find`. Run B-first, the blockquote exists twice and A's find becomes ambiguous.

**Resolved:** all four deletions are at indices 0–3; all four insertions at 343–346.

Cross-checked with the 4.5 edits that also touch `#829`: `mf-content.json[16]` adds a Correction
item reading "The SCOPE blockquote **above** overstates the transfer". The blockquote is at body
line 99 and the Correction block at line 109; the relocation moves the blockquote *up* (to before
`## Definition of Done`, line 56), so "above" stays true. No conflict; the 4.5 author deliberately
avoided editing the blockquote to dodge exactly this race.

### C5 — `#926` / `#959` trailer_deps keep issue numbers (CONVENTION-4 DEVIATION, escalated not fixed)

Convention 4 says trailer `deps` use item ids. `mf-edges.json` and `mf-content.json` convert
everything they touch. `mf-crossfile.json[5]` emits `["#345"]` for #926 and
`mf-crossfile.json[9]` emits `["#425","#428","#481","#406"]` for #959.

I did **not** convert them. Both edits only *remove* entries; every retained entry is pre-existing,
and conversion is not mechanical here: `#345` resolves to **9** candidate item ids, `#428` to
**12**, `#481` to **6**, `#406` to **6**, `#425` to **4**, and neither body carries a resolved
backtick label to disambiguate. A wrong id points the graph at the wrong issue — the exact failure
convention 4 exists to prevent.

**Operator call required.** Either (a) read convention 4 as binding only on deps the manifest adds
or re-aims — in which case these two entries are correct as written — or (b) resolve the five ids
by hand before applying. Do not let a script guess.

### C6 — `#460 ← #890` (decision 2.12) creates a cycle: its precondition exists in NO manifest (**BLOCKING**)

`mf-edges.json[4]`'s note says the removal of #890's `Depends on: #460` is "already decided, in
remediation.json". **It is not.** Verified live today:

- `#890` body: `Depends on: #460 — the gluing/sheaf-condition statement…` still present;
- `#890` trailer: `"deps": ["#460", "#259", "#268"]`;
- `#890` native: `blockedBy = [259, 268, 460]`;
- `remediation.json` contains **no** edit removing it — only `remediation.json[329]`, the DoD
  *rider* to the demotion, whose own note says "verify it was not already applied".

Applying the 2.12 trio as-is produces a **460 ↔ 890 cycle in body, trailer and native
simultaneously**, which `check_graph.py` will reject.

**Resolved by gating, not by authoring new scope:** the three #460 entries are the **last three
elements** of `mf-final.json` and each carries a `DO NOT APPLY UNTIL…` note. The coordinator can
truncate there.

The three prerequisite edits on #890, for the coordinator to file and apply first:

```
1. replace_text  #890  find: "Depends on: #460 — the gluing/sheaf-condition statement for the sheaf of continuous functions; this issue generalizes it to an arbitrary space, re-founds the in-tree predicate, and builds the category, and deliberately does not restate that issue's concrete instance.\n"
                       replace: "- Related (NOT blocking): #460 — the concrete sheaf of continuous functions on a single space; this issue generalizes the gluing/sheaf-condition statement to an arbitrary space, re-founds the in-tree predicate and builds the category, and deliberately does not restate that issue's concrete instance. The dependency runs the other way (see #460).\n"
2. trailer_deps  #890  replace: ["#259", "#268"]        (item-id conversion subject to C5)
3. edge_remove   #890  replace: "460"
```

`remediation.json[329]` (the "positive instance of `Sheaf` built HERE" DoD rider) is the mandatory
companion to that removal and is likewise still unapplied.

### C7 — 4.1 and 4.8 add ledger rows with no `issue-map.json` leg (HALF-APPLIED CROSS-FILE, escalated)

Measured invariant on the current tree: **2294 of 2294** `(item_id, issue)` pairs in `ledger.tsv`
have a matching leg in the book's `issue-map.json`, either as the base key or as `id@issue`.
Decision 5.2 preserved it by emitting `mf-crossfile.json[24]`
(`"7sketches:6.3.1:ex6.57@869": 869`). Decisions 4.1 and 4.8 add seven ledger rows and emit no map
edit. Post-manifest the invariant becomes 2295/2300 — five first-ever exceptions, all in
`doc/plan/books/riehl/issue-map.json`:

```
"riehl:1.3:example14@258": 258      (from mf-content.json[27], 4.1)
"riehl:1.3:example14@259": 259      (from mf-content.json[27], 4.1)
"riehl:1.4:example4@259":  259      (from mf-content.json[26], 4.1)
"riehl:1.4:example4@278":  278      (from mf-content.json[26], 4.1)
"riehl:4.5:example7@732":  732      (from mf-content.json[21], 4.8)
```

Not repaired here: adding a map leg for a clause that is deliberately "ledger row only" and is
*not* going into the issue's trailer `ids` may be the wrong register. The two coherent options are
(a) emit the five legs, matching 5.2's three-register pattern, or (b) accept ledger-only rows and
record the invariant relaxation. `file_chapter.py` keys its dedup on the ledger pair, not the map,
so nothing breaks either way — but a 2294/2294 invariant should not be broken silently. Notes are
tagged on all three ledger entries.

### Checked and clean (no conflict)

- `#237` (4.1 append + 5.4 relabel), `#310` (3.2 naming append + 4.4 rescope), `#370` (3.2 + 6.3),
  `#705` (3.3 ×6 + 5.4 ×2), `#750` (2.6 + 5.4), `#829` (4.5 ×3 + 6.2 ×2), `#926` (3.3 ×2 + 1.6 ×3),
  `#1038` (2.19 ×4 + 3.2 ×4 after C1) — all compose; disjoint find-strings verified by simulation.
- `#926`'s 1.6 rider had already been adapted to decision 3.3's `DiGraph` rename by the crossfile
  author, so the 3.3 and 1.6 edits agree on the name.
- The four `ledger.tsv` anchor pairs that touch adjacent lines (4.8's 2617-rewrite vs its
  companion row anchored on 2618; 5.2's 1964-rewrite vs its row anchored on 1965) are
  order-independent, as their notes claim. Verified.
- Nothing sorts after the trailer: all 11 `append_block` entries target issues whose body already
  ends with the catalog trailer, and the simulator inserts before it.

## 5. Path-decision sets — completeness check

| Decision | Halves required | Present | Verdict |
|---|---|---|---|
| **3.1** `Instance/Mod` vs `Instance/Module` | #388 body ×3, #449 body ×2, serialize key | `naming[0,1,2]`, `naming[3,4]`, `naming[5]` | **COMPLETE** — after the merge, zero `Instance/Module` references remain in either issue or the serialize file; the #388/#449 pair stays path-keyed on `Instance/Mod/Tensor.v` and visible to `check_collisions.py` |
| **3.8** `#1003` lattice | #1003 body + `Structure/Lattice.v` serialize entry → `[340,389,422,1003]` | `naming[117]`, `naming[118]` | **COMPLETE** (both-halves-or-neither honoured) |
| **3.9** `#516` path | #516 ×3, #517 ×1, #519 ×1 | `naming[111,112,113]`, `naming[114]`, `naming[115]` | **COMPLETE** — all three now name `Structure/Abelian/Homology/Simplicial.v`; no `Structure/Homology.v` reference survives in the trio |
| **3.5** monoid ring | #518 body ×2 (path unification) + serialize amendment; #310 needs none | `edges[26,27]`, `crossfile[18]` | **COMPLETE** — after C3's ordering, #518 names `Instance/Rng/MonoidRing.v` in both Work and Verification, matching #310 |
| **3.7** numeric substrate | serialize entry only | `naming[116]` | **COMPLETE AS DECIDED**, but note: #967's body still says `Instance/ExtReal.v` and #1022's still says `Instance/Poset/Reals.v`. The entry's own `rationale` discloses this and the decision text does not order the retarget. Flagged, not repaired. |

## 6. Edge / body agreement

All 14 native-relation edits have a body counterpart **and**, where the trailer carries the dep, a
`trailer_deps` counterpart. Verified against live `blockedBy` today.

| Edit | Body | Trailer | Live `blockedBy` before | OK |
|---|---|---|---|---|
| `#1002` −1004 | `edges[0]` | `edges[2]` | `[259,481,1004]` | ✓ |
| `#921` −261 | `edges[7]` | `edges[8]` | `[261]` | ✓ |
| `#1017` +347 | `edges[10,11,12]` | `edges[13]` | `[]` | ✓ |
| `#1038` +257, +232 | `edges[15]` | `edges[16]` | `[605,971]` | ✓ |
| `#869` +879 | `edges[21]` | `edges[23]` | `[827,868]` | ✓ |
| `#485` −484 | `crossfile[1]` | `crossfile[2]` | `[481,484]` | ✓ |
| `#926` −705 | `crossfile[4]` | `crossfile[5]` | `[345,705]` | ✓ |
| `#959` −720, −671 | `crossfile[8]` | `crossfile[9]` | `[406,425,428,481,671,720]` | ✓ |
| `#704` −311, −428, −227 | `crossfile[12]` | `crossfile[13]` | `[227,311,428]` | ✓ |
| `#460` +890 | `edges[4]` | `edges[5]` | `[259]` | ✓ **but see C6** |

Reverse direction — body edits that touch a `Depends on:` line without an edge change — all
intentional and all edge-preserving: `#750` (2.6, relabel only), `#822` (2.15, relabel + item-id
trailer), `#818` (2.16, relabel only), `#876` (2.11, Work-item wording only, `## Dependencies`
already byte-identical to #873's).

Ordering: all 9 `edge_remove` precede all 5 `edge_add`, so no transient cycle is created by the
manifest itself.

One cosmetic note, not a defect: `mf-content.json[8]` (2.16) turns #818's single-line
`Depends on: #799 …` into a hard-wrapped three-line form. `check_graph.py` is line-based and reads
`#799` off line 1, so the hard dep survives; lines 2–3 become orphan prose inside
`## Dependencies`.

## 7. Decisions from DECISIONS.md with NO edit in the manifest

### Correct — the decision *is* "no action"

| § | Reason |
|---|---|
| **1.1** `Adjunction/Representability.v` entry | Decision is literally **Omit** (dead data, `reach()` resolves it first). |
| **2.1** `#256 → #255` | "No action — keep the edge." Verified in force: #256 body carries `` Depends on: #255 (`maclane:I.6:construction2`) ``. |
| **2.5** `#900 → #245` | "Keep." Verified: body `Depends on: #245`, trailer `"#245"`, and #900's Correction block already re-words it. |
| **2.18** `#718` | "Defer to a later pass." |
| **4.2** `#383` | "Corrected split (already applied)." |
| **4.7** `#647` | "`n + e ≤ 6` only (already applied)." |

### Correct — verification-only, and I performed the verification

| § | Result |
|---|---|
| **1.5** missing item-id labels (#444/#453/#455) | **VERIFIED CLEAN.** All three trailers carry fully populated item-id `ids` arrays (`maclane:V.6:*`, `maclane:V.8:*`, `awodey:*`, `riehl:*`). Nothing to file. |
| **5.5** post-trailer blocks (#1011/#1014/#1016) | **VERIFIED CLEAN.** All three bodies end with their `<!-- catalog: … -->` trailer (lint L2 passes). "Likely already done" confirmed. |

### Correct — discharged by `remediation.json`, which the coordinator applies separately

| § | Where |
|---|---|
| **2.9** `#592 → #227` "leave Related" | `remediation.json[205]`; live #592 already carries the `- Related (NOT blocking): #227` line. |
| **2.10** `#336 / #536` "Related-only" | The weaker of the two options, and it is the status quo: `#336 blockedBy = [335]`, no #536 edge, and `remediation.json[201]/[110]` supply the citation. Nothing to add. |
| **3.4** `Pointed/Sets` vs `Sets/Pointed` | `remediation.json[258]`, `[259]` emit the rename. "Rename stays" = leave those entries in. |
| **3.10** two free groups | `remediation.json[20]`, `[21]` require the proved comparison on #298/#442. |

### **NOT correct — decisions with no coverage anywhere** (escalations)

| § | Decision | State on the live tree | What is missing |
|---|---|---|---|
| **2.2** | "#542→#417, #559→#417: **Take both**, knowingly" | `#542 blockedBy [530]`, `#559 blockedBy []`. Neither body nor trailer mentions #417 anywhere. Not in `remediation.json`. | **6 edits**: `Depends on: #417` body line + `trailer_deps` + `edge_add` on each of #542 and #559. |
| **2.3** | "#530→#255: **Take edge** + keep the illustration deferral" | Deferral half **is** applied (`remediation.json[349]`). Edge half absent: #530's `## Dependencies` reads "None." and `blockedBy = []`. | **3 edits** on #530. `judgement-calls.md` §2.3 is explicit: *"asserting the deferral **without** the edge is not [coherent]"* — the tree is currently in exactly that incoherent state. |
| **2.4** | "#471→#296: **Keep**" | `#471 blockedBy [470]`; body `## Dependencies` lists only #470. `remediation.json[132]` rewrites Work bullets to consume #296 but declares no edge. | **3 edits** on #471, or an explicit reversal to the `- Related (NOT blocking)` fallback that §2.4 names (#296 **and** #502). |
| **2.20** | "#422 vs #737: **Investigate first, then act**" | The investigation is complete (`inv-422-737.md`, verdict + §7 one-line answer). **The "then act" half was never converted to edits.** | #737: delete its identification work item, add a hard `Depends on: #422` (safe — `blockedBy(422) = {}`, #737 stays layer 2), the matching DoD box, the `Print Assumptions` line, and the `— #422 owns this lemma.` append. Plus the wording correction `inv-422-737.md` §6.4 requests in `judgement-calls.md:263-264`, `plan-tail-432-1038.md:257`, `plan-tail-sections.md:614`. |

### Residual defect surfaced during the pass, owned by no decision

`#649`'s `## Dependencies` carries a parenthetical that wraps across a line boundary, producing a
second physical line that begins `Depends on: #648 (…)`. `check_graph` and GitHub agree
(`#649 blockedBy [296, 648]`, which is what decision **2.8(a)** wants), but the trailer reads
`"deps": ["#296"]` only — body/native say 648, trailer does not. `remediation.json[368]` fixes the
*identical* defect on **#648** and nobody fixes #649. Not a decision gap; a missed sibling.

## 8. Flags carried forward from the source manifests (unresolved by design)

- **`#257` / `#839` name collision (3.2 + 4.3), UNRESOLVED.** `mf-naming.json[96]`'s append_block
  itself declares it: `#839` already builds a rig class in `Theory/Algebra/Rig.v` **and** already
  defines `Class Ring` there as `Rig` + additive inverses, consumed by seventeen Seven-Sketches
  issues. After 3.2 there are two global `Ring`s in one import closure (a set-level structure and a
  category) and after 4.3 two rig classes. `mf-naming.json[97]`'s note says the coordinator must
  confirm before applying. **Do not land either side before this is settled.**
- **5.1 Rider B** (`crossfile[21]`): `doc/plan/books/maclane/coverage/verified-IX-3.json` still
  records `PARTIAL` for both `maclane:IX.4:construction{2,4}`; ledger and provenance will disagree
  unless it is flipped too. Left to the operator per the decision.
- **Drop-if-unwanted entries**, each self-contained and safe to delete alone: `content[3]` (2.15
  hygiene rewrite of #822's mid-sentence dep line), `content[21]` (4.8 companion ledger row),
  `content[25]` (4.1 clause-(vii) filing on #237 — **if dropped, the #255 clause map in
  `content[24]` needs its last sentence adjusted by hand**), `crossfile[18]` (3.5 serialize
  `reason` amendment).
- **Tooling**: `crossfile[20]`'s note is right — `sed -i ''` silently no-ops on this box (nix GNU
  sed). Use `perl -pi -e`. Applies to every `ledger.tsv` edit here.
- **`crossfile[214]`** (6.1) uses EN DASH U+2013 in `printed pp. 206–208`; do not normalise it to a
  hyphen.
