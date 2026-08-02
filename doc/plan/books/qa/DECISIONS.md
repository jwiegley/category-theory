# QA remediation — operator decisions (2026-08-01)

Every judgement call from `judgement-calls.md`, decided. **This file is the source of truth**;
where it disagrees with `judgement-calls.md`'s recommendation, this file wins.

Marked **[+]** where the decision goes BEYOND my recommendation and adds scope or edges.

## Contradictions
| § | Decision |
|---|---|
| 1.1 `Adjunction/Representability.v` entry | **Omit** — would be dead data (reach() resolves it first) |
| 1.6 Group A riders #485/#926/#959/#704 | **Apply all four** non-edge halves |
| 1.5 missing item-id labels (#444/#453/#455) | Verify before the next gate run |

## Dependency edges
| § | Decision |
|---|---|
| 2.1 #256→#255 | **No action** — keep the edge; do not orphan `Ab ⟶ Grp` |
| 2.2 #542→#417, #559→#417 | **Take both**, knowingly |
| 2.3 #530→#255 | **Take edge + keep the illustration deferral** |
| 2.4 #471→#296 | **Keep** — a second free monoid is worse than one wave |
| 2.5 #900→#245 | **Keep** — adversarial pass ruled #245 the owner |
| 2.6 #750→#704 | **Leave**, record the covariant/contravariant distinction |
| 2.7 #1002→#1004 | **Delete** + tighten #259's DoD box |
| 2.8 #649→#648 | **Keep `Instance/Mon.v` with #648** (never both routes) |
| 2.9 #592→#227 | **Leave Related** |
| 2.10 #336→#536 | **Related-only** |
| 2.11 #873→#872 | **Keep**, mirror the wording on #876 |
| 2.12 #890 | **[+] Add the reverse edge 460←890** |
| 2.14 #921→#261 | **A: demote to Related**, keep both routes in Work item 1 |
| 2.15 #822→#776 | **[+] (b) Keep the edge and ADD the consumption** — new Work item instantiating the generalised interpreter at a thin symmetric monoidal base, proving agreement with #776's validity predicate, plus a DoD box |
| 2.16 #818→#587 | **[+] (a) Generalise the base** to an arbitrary monoidal base with an initial object, making the identification a proved theorem; keep the edge. Replace the unverifiable DoD phrase "is recorded" either way |
| 2.17 #1017→#347 | **[+] State the clause over #347's `CouniversalArrow`**; add edge + trailer + native relation |
| 2.18 #718 | **Defer** to a later pass |
| 2.19 #1038 | **[+] Make the #257 and #232 edges explicit** |
| 2.20 #422 vs #737 | **Investigate first**, then act |

## Ownership and naming
| § | Decision |
|---|---|
| 3.1 `Mod`/`Module` | **Reconcile all three in ONE edit** — #388 and #449 retargeted to `Instance/Mod/*`, serialize key amended |
| 3.2 `Rng` clash | **Rig/Rng split**: the NON-unital category takes `Rng`; #257's unital one is renamed **`Ring`**. Header must disclose the clash |
| 3.3 `Graph` clash | **[+] Rename #705's** directed-graph category (to `Quiver` if no clash with the existing in-tree quiver notion, else `DiGraph`); #926 keeps `Graph` |
| 3.4 `Pointed/Sets` vs `Sets/Pointed` | Rename stays (consistent with 3.1) |
| 3.5 #518/#310 monoid ring | **No edge, unify path, serialize group** (#518 is the creator) |
| 3.6 #869/#879 | **[+] (a) Real dependency edge** #869→#879; trailer reconciled with §5.2 in one pass |
| 3.7 #1022 numeric substrate | **`Instance/Poset/Numeric.v`, #759 as creator** — owns the `docs/AXIOMS.md` entry |
| 3.8 #1003 lattice | **`Structure/Lattice.v`** + amend the existing entry to `[340, 389, 422, 1003]` (both halves or neither) |
| 3.9 #516 path | **`Structure/Abelian/Homology/Simplicial.v`**; retarget #517 and #519 in the same edit |
| 3.10 two free groups | **Keep both** with a proved comparison |

## Scope
| § | Decision |
|---|---|
| 4.1 #255/#267 Riehl clauses | **File the complementation clause once** (gated on #259); clauses (i)→#248 and (iii)→#258 as **ledger rows only**; no-cloning scoped as Riehl's concrete Vect_k computation |
| 4.2 #383 | Corrected split (already applied) |
| 4.3 #221 rig | **[+] Re-home the rig class to #257** — combines with the `Rng`→`Ring` rename into one #257 edit |
| 4.4 #310 exterior algebra | **Scope to the universal-arrow form** — no graded-algebra substrate needed |
| 4.5 #829/#824 | **Reword, do not delete** |
| 4.7 #647 | `n + e ≤ 6` only (already applied) |
| 4.8 #729 | **[+] Re-home to #732/#734** + correct `ledger.tsv:2617` part label |

## Cross-file
| § | Decision |
|---|---|
| 5.1 #570 | **Verify rows 790–791 first**, then apply both halves |
| 5.2 #868/#869 ledger split | **Apply all four coupled edits together**, merged with §3.6 |
| 5.3 #722 ledger note | Apply the correction (line 1339 / #405 is already correct) |
| 5.4 Awodey edition | **(a) Relabel the ~34 issues to the 1st-ed CMU pre-print (OLG 49, 2005)**, matching the calibration; leave #658 |
| 5.5 post-trailer blocks | **Sweep** #1011/#1014/#1016 (verify — likely already done) |
| 5.6 `make todo` sweep | **[+] Re-run the 19-issue sweep to confirm** before relying on it |

## Not mechanically convertible
| § | Decision |
|---|---|
| 6.1 #1005 page range | **Check the PDF**, then apply |
| 6.2 blockquote relocations | **[+] Do all four by hand** (#843, #827, #829, #832); keep the `- Related (NOT blocking):` lines in Dependencies |
| 6.3 trailer `ids` | **Apply all seven by hand** — #370/#373/#416 only AFTER their trailer moves; #869 merged with §5.2 |
| 6.4 #534 | **Locate the real sentence, fix in place**, and remove the appended block |

---

## Closing record — all disagreements resolved by evidence (2026-08-02)

**Corpus-wide disagreement sweep.** Compared the ledger classification against the authoritative
`verified-*.json` coverage record for **all 2,825 items** carrying both. Exactly **two** disagreed,
both the known §5.1 Rider B. Resolved against the source, not by preferring a register:

- `maclane:IX.4:construction2` and `:construction4` — ledger ABSENT vs coverage PARTIAL. **ABSENT
  is correct**; the coverage records are now updated to match, with the dissent recorded in each.
  The reasoning matters, because the ORIGINAL justification was false:
  - #570's body claimed the `Wedge`/`Cowedge` classes "have zero instances tree-wide". **False** —
    `Instance/Sets/End.v:102` and `Structure/Coend.v:172` both call `Build_Wedge`, the first with a
    `Qed`'d obligation. Only `Dinatural` has none. Corrected in the issue.
  - The classification nevertheless stands on the GOVERNING rule (`schemas.md`: *PARTIAL requires a
    PROVED statement covering part of the item*). Verified at source: `eval`
    (`Structure/Cartesian/Closed.v:75`) is a bare `Definition`; its only `Qed`'d fact,
    `ump_exponents`, is the exponential UMP — a different statement — and
    `rg -n 'extranatural|Wedge' Structure/Cartesian/Closed.v` returns **0 hits**. For
    construction4 the `Hom` bifunctor is the *setting* of the claim, not part of it.
  - The Phase-D verifier had confirmed PARTIAL under a differently-phrased definition ("some of the
    item exists"), and itself called that "on the GENEROUS end". Recorded rather than overwritten.
  - #570's claim that these become "the library's first concrete `Wedge`/`Dinatural` instances" is
    now precise: first `Dinatural` instances, and the first `Wedge` instances that are not the
    universal end/coend wedge.

**#649's phantom dependency** — traced to MY OWN L4 splitter. The original was one line carrying a
`Related:` clause; the splitter cut it at the second `#N` and manufactured a `Depends on: #648` line
out of a parenthetical, leaving `))` and trailing prose. Since decision 2.8 keeps `Instance/Mon.v`
with #648, the edge is intended: rewritten as two clean one-per-line dependencies with the trailer
updated, so body, trailer and native now agree.

**A sweep the disagreement check exposed.** Every `Depends on: #N (`item-id`)` label in all 824
bodies was checked against the target's own registered ids. **Six were wrong** — four "not owned at
all" and two citing the wrong book (#890 cited *Riehl* items as the reason it depends on two *Mac
Lane* issues). Two of the six were labels I invented in earlier repairs. All corrected to an id the
target actually owns, trailers kept in step.

**New linter rule L8** now enforces this: a dependency label must be an item id the target issue
owns. `check_graph.py` cannot catch it — its RESOLVED invariant only requires that *some* label be
present, so a truthful-but-misleading label passes. This is the third defect class this session that
was invisible to the graph gate and needed a body-level check.

### Final state — both gates green

| Check | Result |
|---|---|
| `check_graph.py` | **EXIT 0** — acyclic, body==native consistent, all deps resolved, conflict-free |
| `lint_issue_bodies.py` (L1–L8) | **EXIT 0** across all 824 bodies |
| ledger vs coverage | **0 disagreements** across 2,825 items |
| ledger classification/issue invariant | **0 violations** (2,928 rows) |
| ledger pairs with no issue-map leg | **0** |
| multi-part items missing a part name | **0** (72 multi-part items) |
| registers parse | all OK |

**824 issues · 1,360 edges · 12 layers · 214 at layer 0 · 38 serialize-groups.**
