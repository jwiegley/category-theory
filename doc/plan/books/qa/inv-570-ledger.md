# DECISION 5.1 — #570 ledger flip: verification

**Verdict: row indices are CORRECT. The flip's *conclusion* holds, but its *stated reason* is
factually false about the repo. Apply the flip — with two riders (§5, §6).**

---

## 1. Are lines 790–791 the right rows?

Yes. Verbatim, with tabs shown as `\t` (`sed -n '790,791p'`, verified against `cat -A`):

```
790:maclane:IX.4:construction2\tPARTIAL\t#570\t4\tMacLane IX.4: Canonical wedges — evaluation and the identity family
791:maclane:IX.4:construction4\tPARTIAL\t#570\t4\tMacLane IX.4: Canonical wedges — evaluation and the identity family
```

(The `—` is U+2014 EM DASH; `cat -A` shows `M-bM-^@M-^T`. Ledger line 1 is the header
`item_id\tclassification\tissue\tprojects\tevidence_or_note`, so these are physical file lines.)

Three independent confirmations that these are the rows #570 means:

1. `grep -n "#570" doc/plan/books/ledger.tsv` returns **exactly these two lines and no others**.
2. #570's catalog footer is verbatim:
   `<!-- catalog: {"ids":["maclane:IX.4:construction2","maclane:IX.4:construction4"],"deps":[]} -->`
   — the same two ids, in the same order.
3. Each id occurs exactly once in the ledger (`grep -c` = 1 each), so an id-keyed edit and a
   line-number edit target the same bytes.

**No row-number correction is needed.**

## 2. The rule, quoted exactly

`doc/plan/books/schemas.md:212-219`:

> ## PARTIAL vs ABSENT: the boundary rule (written down 2026-08-01, after the fact)
> …
> > **PARTIAL requires a PROVED statement covering part of the item. A never-instantiated class
> > does not qualify.**

## 3. Is the class genuinely never instantiated in-tree? — **NO for `Wedge`/`Cowedge`; YES for `Dinatural`**

#570's body asserts, verbatim:

> Partial. The `Wedge`/`Cowedge` classes exist (`Structure/Wedge.v:38,61`) and the `Dinatural`
> class (`Theory/Dinatural.v:51`), but they have zero instances tree-wide.

The second half of that sentence is **false for `Wedge`/`Cowedge`**:

- `Instance/Sets/End.v:101-102` — a real inhabitant, obligation `Qed`'d at line 111:
  `Program Definition Sets_End_Wedge : Wedge F := @Build_Wedge C Sets F Sets_End_obj (fun x => end_projection x) _.`
  (`F : C^op ∏ C ⟶ Sets` is a `Context` variable of `Section SetsEnd`, `Instance/Sets/End.v:50-53`.)
  It is consumed by `Sets_End : End F` (`Instance/Sets/End.v:144-145`, `end_wedge := Sets_End_Wedge`),
  and `Instance/Sets/End.v` is line 232 of `_CoqProject`, so this compiles in the normal build.
- `Structure/Coend.v:168-172` — `covariant_cowedge` assembles cowedge data into a `Wedge F^op`
  (`= Cowedge F`) via `@Build_Wedge (C^op) (D^op) (F^op)`; `Instance/Sets/Coend.v:163`
  `Definition SetsCoend : Coend F` is a concrete consumer, and the cowedge condition
  `Cowedge_cond` (`Structure/Coend.v:160`) is `Qed`'d at `Theory/Coend/Yoneda.v:118`,
  `Theory/Coend/Fubini.v:175,292,357,368,386`, `Construction/Day.v:272,420,526`,
  `Instance/Sets/Coend.v:116`.

`Dinatural` is a different story: `grep -rn 'Dinatural' --include='*.v' .` returns only
`Theory/Dinatural.v` itself plus four prose mentions (`Instance/Sets/End.v:29`,
`Construction/Product.v:82`, `Structure/Wedge.v:18`, `Structure/Monoidal/Traced.v:140`). Zero
instances — that half of the sentence is true.

Note the campaign's own coverage record already knew this. `verified-IX-3.json`, in
`maclane:IX.4:construction4`'s `negative_search_log`, says verbatim:

> `grep -rn -e 'Build_Wedge' --include=*.v . -> Wedge instances only in Instance/Sets/End.v (universal end wedge), none is the identity/hom unit wedge`

So the coverage record and the issue body **contradict each other** on "zero instances tree-wide".

## 4. Does the rule's operative clause still bite? — **Yes**

The corollary ("a never-instantiated class does not qualify") misfires, but the requirement
("PARTIAL requires a PROVED statement covering part of the item") is independently unmet:

- **construction2** (evaluation is extranatural). The only in-tree evidence is
  `Structure/Cartesian/Closed.v:75`, `Definition eval {x y} : y^x × x ~> y := uncurry id.` — a
  bare definition. The one `Qed`'d fact about it, `ump_exponents` (`Closed.v:79-80`), is the
  exponential UMP, a *different* statement; nothing states or proves the wedge/extranaturality
  condition, and the bifunctor `hom(-,A) × (-)` does not exist in-tree.
- **construction4** (identities form a wedge `Δ* ⇒ Hom`). Evidence is `Functor/Hom.v:49`'s
  target bifunctor plus "the identity legs exist trivially". The target functor is the *setting*
  of the claim, not part of it; no `Wedge (Hom C)` is built. The record's own gap field says
  "nobody constructs the wedge whose apex is the terminal/one-point object and whose legs are the
  identities, nor proves its extranaturality condition."

Neither item has a `Qed`'d statement covering any part of the book's assertion. Under
`schemas.md:218`, both are ABSENT.

**Counterweight the coordinator should know about.** The Phase-D verifier considered exactly this
question and confirmed PARTIAL, under a *differently phrased* frozen definition
(`verified-IX-3.json`, construction2 verifier notes, verbatim):

> "The PARTIAL is on the GENEROUS end -- the substantive content of IX.4 (the extranaturality/wedge
> condition) is entirely absent; only the underlying component morphism exists … But under the
> frozen definition PARTIAL = 'some of the item exists + gap stated precisely,' … Confirmed as PARTIAL."

So this is a conflict between two campaign-internal phrasings of the boundary, not a case of the
classifier being careless. `schemas.md:212` is the version that was written down as governing, and
it was applied to Riehl Ch6 in exactly this direction ("ABSENT — every one rests on
definitions-without-instances"). Flipping is the consistent call.

## 5. Exact edits

### 5a. `doc/plan/books/ledger.tsv` line 790

OLD (tabs as `\t`):
```
maclane:IX.4:construction2\tPARTIAL\t#570\t4\tMacLane IX.4: Canonical wedges — evaluation and the identity family
```
NEW:
```
maclane:IX.4:construction2\tABSENT\t#570\t4\tMacLane IX.4: Canonical wedges — evaluation and the identity family
```

### 5b. `doc/plan/books/ledger.tsv` line 791

OLD:
```
maclane:IX.4:construction4\tPARTIAL\t#570\t4\tMacLane IX.4: Canonical wedges — evaluation and the identity family
```
NEW:
```
maclane:IX.4:construction4\tABSENT\t#570\t4\tMacLane IX.4: Canonical wedges — evaluation and the identity family
```

Only column 2 changes on each line. Both ids are unique in the file, so an id-anchored
substitution is safe. Note: `sed -i ''` silently no-ops on this box (GNU sed from nix); use
`perl -pi -e`.

### 5c. #570 body

OLD (first word of `## Current state in the library`):
```
Partial. The `Wedge`/`Cowedge` classes exist
```
NEW:
```
Absent. The `Wedge`/`Cowedge` classes exist
```
Nothing else on the line changes if only the finding is applied.

## 6. Two riders

**Rider A — the sentence being kept is false.** If 5c ships as written, #570 will read
"Absent. … but they have zero instances tree-wide", and the "zero instances tree-wide" claim is
refuted by `Instance/Sets/End.v:101`. Recommended stronger 5c (one contiguous replacement):

OLD:
```
Partial. The `Wedge`/`Cowedge` classes exist (`Structure/Wedge.v:38,61`) and the `Dinatural` class (`Theory/Dinatural.v:51`), but they have zero instances tree-wide.
```
NEW:
```
Absent. The `Wedge`/`Cowedge` classes exist (`Structure/Wedge.v:38,61`) and the `Dinatural` class (`Theory/Dinatural.v:51`); the only in-tree `Wedge` instance is the universal end wedge `Sets_End_Wedge` (`Instance/Sets/End.v:101`), and `Dinatural` has zero instances tree-wide. Neither of the two wedges of this item is built.
```
This is a superset of the finding and keeps the ABSENT justification true. If the coordinator
prefers minimal diffs, apply 5c alone and file the false sentence separately — but do not cite
"zero instances tree-wide" as the reason for the flip in any commit message.

**Rider B — ledger/coverage desync.** The finding mutates only `ledger.tsv` and the issue body.
`doc/plan/books/maclane/coverage/verified-IX-3.json` will still carry, for both ids,
`"classification": "PARTIAL"` and `"verifier": {"verdict": "CONFIRMED", …}`. Nothing automated
cross-checks the two (`doc/plan/books/tools/check_graph.py` checks the dependency graph only;
`file_chapter.py` is the sole ledger writer), so this will not break a build — it will just leave
the ledger and its provenance record disagreeing. If the coordinator wants them consistent, the
JSON's `classification` fields for both ids should flip too; the schema requirement for ABSENT
("ABSENT requires `negative_search_log`", `schemas.md:101-103`) is already satisfied — both
records carry populated `negative_search_log` arrays — so the flip is schema-legal there.

## 7. Bottom line

- Row indices 790–791: **correct, no correction needed.**
- Rule's corollary as stated ("never-instantiated class"): **does not hold for `Wedge`/`Cowedge`**
  — it does hold for `Dinatural`.
- Rule's operative requirement ("a PROVED statement covering part of the item"): **unmet for both
  items**, so ABSENT is the right classification under `schemas.md:218`.
- **Recommend applying the flip**, preferably with Rider A's corrected sentence, and deciding
  Rider B explicitly rather than by omission.
