# QA remediation — judgement calls

Every item either plan flags as needing a human decision, plus every point where the head plan
and a tail section **contradict** each other. Deduplicated across
`plan-head-216-471.md` §4 and `plan-tail-sections.md` §(ii) of all four sections.

None of these are represented in `remediation.json`. Everything else from the plans that is
mechanically applicable is.

Sources are abbreviated **H** (head plan) and **T1–T4** (tail sections 1–4, in file order).

---

## 0. Already resolved by the operator — recorded so nobody re-litigates

**H-7 / T1-9 — the `deps` array convention.** The corpus mixes item ids
(`"maclane:I.7:construction3"`) and issue numbers (`"#256"`); `schemas.md` names the field
`deps_item_ids`. **The operator has decided: item ids.** Every `trailer_deps` entry in
`remediation.json` is already converted, including T1's F7 batch (#953, #956, #963, #964, #968),
which the tail plan explicitly gated on this decision. Where a target issue owns several item
ids, the entry uses the first id in that issue's own trailer `ids` array that resolves back to
it — any id owned by the issue produces the same edge, since `resolve_chapter_deps.py` maps
id → issue.

---

## 1. CONTRADICTIONS BETWEEN THE TWO PLANS

### 1.1 `Adjunction/Representability.v` serialize-group entry (#348 / #437) — **H Group H item 3 vs T4**

- **H** orders the entry added: `{"module": "Adjunction/Representability.v", "issues": [348, 437], "creator": 348, "reason": "Ordered, not merely serialized: #437 is blocked_by #348, which creates the file."}`
- **T4** says **DO NOT ADD**: `check_graph.py:233-240` discharges a co-creation conflict by `reach()` first and consults `acknowledged` only when NO dependency path exists. #437 *is* `blocked_by` #348, so the entry would never be read — dead data. Worse, every other entry in the file declares "SERIALIZE_ONLY … No logical precedence exists, so NO dependency edge is asserted", the opposite of this pair.

**Options.** (a) Add it — costs nothing at runtime, but pollutes a file whose every other entry
means the opposite. (b) Omit it — the 348/437 co-creation is then visible only in #437's body.

**Recommendation: omit (b).** T4's reading of `check_graph.py` is specific and checkable, and the
body rewrite (T4's F4, **which is in `remediation.json` and should still be applied**) makes the
co-creation explicit at the point an implementer will read it. If you want a graph-level record
anyway, add it but reword `reason` so it does not claim SERIALIZE_ONLY — and then also fix the
file's contract note, or the key's semantics stay ambiguous.

*Not in `remediation.json` either way.*

### 1.2 `Grp` serialize key (#255 / #440) — **H Group H item 4 vs T2 Group H item 7**

H proposes a prose key `"Grp (construction, not a path: Instance/Grp.v vs Instance/Variety.v)"`;
T2 says every existing entry's `module` holds a real path and the precedent keys on ONE of the
two, so use `"Instance/Grp.v"`. T2 states this is a **correction, not a second entry**.

**Resolved in `remediation.json`: the `Instance/Grp.v` form is emitted; the prose key is not.**
Flagged here only so you do not create both. (Note the tension with §1.1: T4 argues against
non-path keys as dead data, while T1/T3 propose several construction-keyed entries for
genuinely path-invisible pairs — those are a different case, since no dependency path exists
between the claimants.)

### 1.3 #440 Work-bullet wording — **H Group C vs T2 Group C**

H makes *"prove `GroupVariety ≅[Cat] Grp` once #255 has landed"* an unconditional Work
deliverable while declaring the #255 relation non-blocking — a hidden blocker. T2's ADJUSTED
wording makes the comparison fall to whichever of the two lands second.
**Resolved: `remediation.json` carries T2's version.**

### 1.4 #450's second Definition-of-Done box — **H Group D vs T3 Group D**

H's box states a falsehood (`⟨Ω,E⟩-Alg` is never empty — `Instance/Comp.v:160` `Algs_Terminal`
is the one-element algebra, which satisfies every equation). T3 rewrites it as a statement about
the initial algebra's *carrier*. **Resolved: `remediation.json` carries T3's version.**

### 1.5 Missing item-id labels in the head plan's Group B lines (#444, #453) — **T1/T2 corrections**

Group B is already applied, so this is a **check, not an edit**: T1 records that H's #444 line was
written without an item-id label (correct label `maclane:V.2:remark1`), and T2 that H's #353 line
for #453 omits its id (correct label `maclane:IV.2:construction2`; the original finding wrote a
literal ellipsis `maclane:IV.2:...` into a live body). Similarly T3 supplies `maclane:V.1:ex2`
for the #455 → #413 line. **Recommendation: grep the three bodies for `maclane:IV.2:...` and for
unlabelled `Depends on:` lines before running `check_graph.py`** — invariant 3 (resolved label
required) will fire on them.

### 1.6 Group A/B riders that were *not* pure edge changes

Several Group A rows carried body edits that are not edge changes, and Group A is recorded as
"done". Two are load-bearing:

- **#890's fifth edit (MANDATORY).** With the #460 edge gone, the old DoD box still consumed a
  #460 deliverable, leaving #890 — a hub on which #888, #891, #892, #893, #894, #902, #903 all
  block — unsatisfiable. **This one IS in `remediation.json`** (group D), with a note to verify
  it was not already applied.
- **#485, #926, #959, #704** carried riders too (a Work-bullet rewrite routing through the
  in-tree `beck_monadicity`; the `Graph` name-clash note; dropping #720/#671 from an In-tree
  donors line; a whole `## Dependencies` block replacement). **These are NOT in
  `remediation.json`** — decide whether the Group A pass applied them, and if not, re-run those
  four rows' non-edge halves by hand.

---

## 2. DEPENDENCY-EDGE JUDGEMENT CALLS

### 2.1 #256 → #255 edge (H-1)

Deleting it buys one scheduling wave (unblocking the Ab/Rng/Mod/tensor/graded/representation
subtree from a leaf issue), but the finding's remediation also drops `Ab ⟶ Grp` from #256's DoD,
orphaning it — #255 runs *before* `Ab` exists and cannot absorb it.
**Recommendation: no action.** If you want the parallelism, re-home the forgetful functor first
(its own small issue depending on both, or explicitly into #257/#258's wire-up).

### 2.2 #542 → #417 (T1-2) and #559 → #417 (T2-J3) — scheduling cost

Both edges are real. #542 is layer 1, #559 layer 0, #417 layer 2 (`blocked_by [335,326,416]`), so
each edge reschedules the issue *and its dependents* (#546, #552, and through them #551/#555 for
#542; #563/#564 for #559).
**Recommendation: take both edges, knowingly.** The alternative is a descope that weakens each
issue below its own stated content (#542 below its Mac Lane §VIII.3 remark; #559 below a DoD box
that ends "…the finite-cocone lemma proved"). Note the asymmetry with §2.3 below: #546's #417
edge was *refuted* because the predicate's owner documents it does not need #417.

### 2.3 #530 → #255 (T4-2)

A DoD checkbox genuinely consumes #255's `Grp`. But #530 is a ~20-line core lemma and #542 waits
behind it, and #255 is unstarted.
**Recommendation: take the edge AND defer the Pos/Mon/Top illustration clause** (the Group D
Related-line deferral, which *is* in `remediation.json`). The verdicts jointly recommend that
pairing. Asserting neither is also coherent; asserting the deferral **without** the edge is not.

### 2.4 #471 — is `blocked_by 296` the right instrument at all? (T1-7)

The verdict rejected #502 (no `icoprod` in-tree, so it is the heaviest possible prerequisite) and
substituted #296. But by the campaign's own test #471 could discharge its DoD by building the
list monad directly, which makes *any* edge fabricated.
**Recommendation: keep #296.** A second free-monoid construction is the worse outcome. If you
drop it, keep the `- Related (NOT blocking)` line naming **both** #296 and #502.

### 2.5 #900 — who owns `surjectivity_is_epic`? (T1-3)

The finding wanted the #245 edge deleted ("the issue can build it itself"); the adversarial pass
**reversed** this and ruled #245 the owner. This is the one place in that chunk where the "no
edge if it can build it itself" rule was overridden.
**Recommendation: keep the edge** (the ADJUSTED form). The Work/DoD half of that rewrite is in
`remediation.json` and is correct either way; only the edge is at stake.

### 2.6 #750 → #704 (T2-J1)

The merits are clean — #750 needs the **covariant** powerset, #704 is explicitly the
contravariant one — but the finding is LOW, carries **no adversarial verdict**, and overrides a
recorded prior decision from a Riehl-Ch.5 audit.
**Recommendation: leave the edge, and record the covariant/contravariant distinction in the line
instead.** Demoting buys one wave; the recorded decision is worth more than one wave.

### 2.7 #1002 → #1004 (T2-J6)

The Depends-on line is a provenance note ("the notion in which Corollary 5.6.4 is stated"), not a
consumption: neither `AlgebraicCategory` nor "finitary" occurs anywhere in #1002, whose Work item
3 and DoD name only in-tree artifacts.
**Recommendation: delete the edge** — it unparks a two-lemma result from the whole
finitary/filtered chain. If the corollary is genuinely meant to be stated *for*
`AlgebraicCategory`, keep the edge and add an explicit Work item saying so; that is the only
reading under which it stands. Either way, tighten the #259 DoD box to
*"…is explicitly scoped out in the header with #259 named as the missing prerequisite"* — the
current "proved or scoped out" wording silently reintroduces the #259 prerequisite.
**Note:** the `Structure/Limit/Reflection.v` serialize entry (in `remediation.json`) is a
REQUIRED companion to the already-applied #1002 → #481 demotion regardless of how this one goes.

### 2.8 #649 → #648 is contingent (T2-J2)

A sibling chunk proposes handing the concrete monoid category to #296. If that lands, the edge
points at an issue that no longer builds the donor.
**Do exactly one of:** (a) keep `Instance/Mon.v` as #648's deliverable and declare 649→648; or
(b) reassign creation to #296, delete the 648 edge, and record #648/#649 as a serialize group on
`Instance/Mon.v`. **Never both.**
**Recommendation: (a).** `remediation.json`'s #648 rewrite keeps `Instance/Mon.v` as #648's, and
T4 explicitly warns that dropping it invalidates the #649 edge.

### 2.9 #592 → #227: Related or hard? (T2-J10)

Promote only if you decide the `2^M ≅ P(M)` identification of Work item 1 is in scope rather than
optional. #592's Current state confirms the gap.
**Recommendation: leave it Related** (that is what `remediation.json` emits) unless the
identification is a required deliverable.

### 2.10 #536 / #336: Related-only or a real edge? (T2-J9)

Once #336's boxes are amended to consume #536's artifacts (in `remediation.json`), a real edge
`336 blocked_by 536` is defensible and layer-compatible (#536 layer 0, #336 layer 1).
**Recommendation: Related-only.** It is the safer edit, and `Related (NOT blocking)` is in
`REVERSE_CUE` so it asserts nothing.

### 2.11 #873 — keep the #872 edge or parallelise? (T3-3)

Keeping it costs one scheduling wave and guarantees the six `DecCospan_*_Coherent` instances land
once; dropping it buys parallelism at the risk of two competing instance sets.
**Recommendation: keep the edge.** Whichever you choose, **apply the same wording to #876** or the
two drift.

### 2.12 #890 — add the reverse edge 460←890? (T3-5)

Removing 890←460 was right (it inverted precedence and parked a seven-issue hub). Adding the
reverse is optional: #460's Work already presumes #890's strengthening, so it is honest, but it
lengthens #460's chain.
**Recommendation: do not add it.** The serialize-group entry (in `remediation.json`) plus the
mandatory DoD rewrite already record the relation.

### 2.13 #465's edge strength (T3-10)

#388 is arguably needed for #465's **main** Work item ("build the endofunctor `R ⊗ (−) : Ab ⟶ Ab`"),
not merely the appended checkbox. The edge is right either way; only the stated reason changes.
**Recommendation: no action** beyond the already-applied Group B edge.

### 2.14 #921 — demote the #261 edge, or delete the alternative route? (T4-4)

Work item 1 sanctions building `Fin_*` *either* as the pointed restriction of #261's `Set_*`
*or* directly over `Instance/FinSet.v`, and its own stated criterion (preserve skeletal
computability) points **away** from #261.
**Option A:** demote to Related, empty the trailer deps, drop `blocked_by` 261.
**Option B:** keep the edge and delete the "or directly over `Instance/FinSet.v`…" alternative
from item 1 and "(or imported)" from the DoD.
**Recommendation: A** — the campaign precedent (the #541/#536 demotion). **Do not blend.**
*(The format half of #921 — blockquote → `- Related (NOT blocking):` line — IS in
`remediation.json` and is correct under either option.)*

### 2.15 #822 — demote #776, or home the reuse? (T3-4)

(a) drop the edge and record the link in prose; (b) keep it by adding a real consumption — a Work
item instantiating the generalised interpreter at a thin symmetric monoidal base and proving it
agrees with #776's validity predicate, plus a matching DoD box.
**Recommendation: (a)** unless you want the extra mathematics; (b) is more work for a link the
book itself only states informally.

### 2.16 #818 — generalize the base, or demote #587? (T1-1)

Work item 4 asserts #587's category is an instance of the quantale-parameterised collage. That is
**false as written**: #587's `C_K` has genuine hom-*setoids* and `Sets` is not thin.
(a) Generalize the base to an arbitrary monoidal base with an initial object, making the
identification a proved theorem — real generality work, keeps the edge and the deliverable.
(b) Keep the quantale scoping, downgrade Work item 4 to a header *analogy*, and demote the #587
edge — cheap, but loses a stated deliverable.
**Recommendation: (b)** unless the generality is wanted for its own sake. Either way, replace the
unverifiable DoD phrase *"is recorded"* — say whether a proof or a header note is required.

### 2.17 #1017 — descope, or state terminality over #347's class? (T4-5)

**Recommendation: descope** (that is what `remediation.json` emits): #1017 does not consume #347
today, it ADDS a rival, and its terminality proof goes directly through `Construction/Comma.v` +
`Structure/Terminal.v`. Adding the edge would serialise an otherwise-unblocked flagship
Kan-extension issue behind MacLane IV.1 (#347, itself blocked by #302) for a deliverable it can
simply drop. Only if you positively want the clause stated over `CouniversalArrow` should the
edge + trailer + native relation be applied.

### 2.18 #723 and #718 (T3-2)

#718 stands in the *same* Sets-vs-FinSet relation to part (b) that justified demoting #404. If
#404 is demoted, #718's blocking status deserves the same scrutiny.
**Recommendation: defer to a later pass**, as T3 does; the Work-item-4 rewrite in
`remediation.json` is correct either way.

### 2.19 #1038 — make the inherited ordering explicit? (T2-J11)

After the Group C rewrite, #1038 explicitly consumes #257's `CRng` and #232's `Frac`, but its
ordering is inherited by accident (1038→971→{226,232}→257).
**Recommendation: optional.** The verdict: "not required, and not adding them is not wrong."

### 2.20 NEW duplicate pair surfaced, outside every chunk's issue set: #422 vs #737 (T3-7)

Both schedule the Proset colimit-is-a-join / limit-is-a-meet identification (#422 the general
J-indexed statement; #737 the discrete-diagram case, with `proset_colimit_is_join` in its
Verification and its own DoD box).
**Recommendation: register it as its own duplicate pair** — #737 should consume #422 rather than
re-prove the discrete case. Not actionable from the audited evidence alone.

---

## 3. OWNERSHIP AND NAMING CALLS

### 3.1 `Instance/Mod` vs `Instance/Module` (H-4)

#258 creates `Instance/Mod.v`; #388 and #449 both propose `Instance/Module/*` over it. Renaming
only #388 makes the 388/449 pair path-disjoint and invisible to the collision check.
**Either reconcile both issues plus the serialize-groups key in one edit, or leave the paths and
add the PATH NOTE. Do not do half.** `remediation.json`'s #388 block deliberately says "do NOT
rename on this issue alone".

### 3.2 `Rng` name clash (#362 / #257) (H-5)

#257 uses `Rng` for the *unital* category (Mac Lane's usage); #362 uses "rng" for the non-unital
one. **Pick the name for the non-unital category and require the header to disclose the clash**,
so the forgetful functor's direction is unambiguous. `remediation.json`'s #362 block states the
constraint without picking the name.

### 3.3 `Graph` name clash (#705 / #926) (T1-5)

#705 names its directed-graph category `Graph` in `Instance/Parallel/Graphs.v`; #926 names a
*different* simple-graph category `Graph` in `Instance/Graph.v`. Renaming #926's to `SimpleGraph`
is the obvious call but touches #926's body, its DoD, and the Group H key.
**Recommendation: resolve it exactly the way you resolve `Rng` and `Grp`**, in one edit touching
both issues plus the serialize key. The serialize entry itself IS in `remediation.json`.

### 3.4 `Instance/Pointed/Sets.v` vs `Instance/Sets/Pointed.v` (#529 / #261) (T2-J7)

Same near-mirror hazard as `Mod`/`Module`. LOW, no verdict; the obligations are genuinely
distinct (#261 builds the category, #529 builds `(− ∧ S) ⊣ Set_*(S, −)` over the in-tree
`Par`/`Coslice 1 Sets` model), so no edge is warranted either way.
**`remediation.json` emits the rename** (`Instance/Sets/Pointed/Smash.v`) with the disambiguating
donor note folded in. If you decide `Mod`/`Module` the other way, drop these two entries and keep
only the note.

### 3.5 #518 vs #310 — who owns the monoid ring? (T3-1)

The finding said #518 consumes #310; the adversarial pass **reversed** it and made **#518 the
creator** (an adjunction yields the universal arrow, not conversely). #518 is focused and nearly
ready (blocked only on #257); #310 is a three-part bundle additionally requiring an
`Instance/Vect` substrate that does not exist and has no builder issue.
**Recommendation: the ADJUSTED version (in `remediation.json`) — no edge, path unified, serialize
group.** Decide separately whether to also add `Depends on: #518` to #310, an out-of-batch edit.

### 3.6 #869 / #879 `CospanCat FinSet` (T4-3)

(a) `Depends on: #879 (`7sketches:6.5.2:example6.94`) — the named `CospanCat FinSet` term.` plus
trailer and native edge; or (b) the construction-keyed serialize entry, keeping both unblocked.
**Recommendation: (b)**, matching the precedent for path-invisible pairs — but (a) costs little
(#879 has no blockers). **The #869 Work-item-5 and DoD deletions in `remediation.json` are
unconditional either way.** Whichever you choose determines #869's final trailer `deps`, which
must be reconciled in ONE edit with the ledger `ids` rewrite (§5.2).
*The (b) serialize entry is NOT in `remediation.json` — it is conditional on this decision.*

### 3.7 #1022's serialize-group `module` key is a literal placeholder (T1-6)

The proposed entry keys on `"<numeric substrate: Instance/Poset/Numeric.v | Instance/ExtReal.v |
Instance/Poset/Reals.v>"` for issues [759, 967, 1022]. One of the three must be nominated as the
carrier path, and whichever lands first owns the `docs/AXIOMS.md` entry (all three commit to
extending it; all three make the same `Coq.Reals`-vs-constructive decision).
**Decide the path first — the entry is NOT in `remediation.json`** because its key is unwritable
as given. **Recommendation: `Instance/Poset/Numeric.v` (#759 as creator)**, since #774 and #775
are already being rewritten to consume #759's carriers.

### 3.8 #1003 — `Structure/Lattice.v` or `Instance/Lattice.v`? (T3-6)

Landing the vocabulary in `Structure/Lattice.v` beside #340/#389/#422 **requires** amending that
existing serialize entry, or `check_graph` invariant 4 fires three new violations. Staying in
`Instance/Lattice.v` keeps the collision invisible but is architecturally defensible — the repo
already ships both idioms (`Structure/Monoid.v` `MonoidObject` vs `Instance/CMon.v`).
**`remediation.json` emits the coordination bullet naming `Structure/Lattice.v`; the matching
amendment to the existing `Structure/Lattice.v` entry is NOT emitted** (existing key, per the
skip rule). **If you apply the #1003 bullet, you must also amend that entry to
`issues: [340, 389, 422, 1003]`. Do not do half.**

### 3.9 #516's new module path (T2-J8)

The finding says `Instance/Simplicial/Homology.v`; the verdict prefers
`Structure/Abelian/Homology/Simplicial.v` as more consistent with the repo's `Structure/` vs
`Instance/` split, since the alternating-sum construction is general over any abelian category.
**Either resolves the finding, but #517 line 17 and #519 line 17 must be retargeted to the same
choice in the same edit.** `remediation.json` carries the finding's path and states the
propagation requirement.

### 3.10 Two free groups: #298 (word model) vs #442 (AFT) (H-6)

Mac Lane presents both routes deliberately; #442's value is the tree's first concrete
`SolutionSet`, which does not survive a merge.
**Recommendation: keep both with a proved comparison** (per #443's Work item 3 precedent) — which
is what `remediation.json` emits. **Do not write "the tree must end with ONE free-group
adjunction" into a live issue.**

---

## 4. SCOPE CALLS

### 4.1 #255 / #267 unhomed Riehl clauses (H-2)

Taken literally, the two findings file the *same* complementation isomorphism twice
(`riehl:1.4:example4` clause (v) = `riehl:1.3:example14` clause (iv)) and file a no-cloning
theorem that already has a weaker in-tree counterpart (`Structure/Monoidal/Collapse.v:526`
`no_cloning`).
**Recommendation:** file the complementation clause **once** (gated on #259); record clause
(i)→#248 and clause (iii)→#258 as **ledger rows only**; scope any clause-(vii) filing as "Riehl's
concrete Vect_k computation" rather than a fresh no-go theorem. Filing all six as new issues
creates two duplicates. *The corresponding H Group E clause-map inserts for #255 and #267 are NOT
in `remediation.json` — they depend on this decision.*

### 4.2 #383 scope (H-3)

The finding's remediation deletes #383's Work item 1, which would drop the Δ⊣∩ meet adjunction —
#383's own named artifact (`Print Assumptions powerset_meet_adjunction`) and half its catalog
item `maclane:IV.5:construction3`.
**Recommendation: the corrected split, which is what `remediation.json` emits** — item 1
*consumes* #389's cartesian structure and keeps the meet/join adjunction; item 3 delegates the
exponential; the DoD and `Print Assumptions` line are untouched.

### 4.3 #221 rig/semiring (H-8)

The checkbox adds a genuinely new class (`Rng`/`CRng` from #257 do not include rigs).
**Decide whether that is in scope for a matrix-category issue or belongs upstream with #257.**
`remediation.json` emits the checkbox with a header note saying the rig vocabulary is built here;
if you re-home it to #257, drop that entry.

### 4.4 #310 exterior-algebra left adjoint (H-9)

The checkbox implies a category of graded anticommutative K-algebras, which neither #257 nor #258
supplies.
**Either accept the substrate cost or scope the checkbox to the universal-arrow form.**
`remediation.json` emits both boxes with the substrate gap flagged inline.

### 4.5 #829 step (1) is a paired edit or nothing (T2-J4)

If you delete #829's first Work bullet and its `Construction/Cospan/Corelation/Monoidal.v`
module, you must **simultaneously** edit #824's step 3 to prove the restriction once at an
ARBITRARY base and instantiate at FinSet, adding that path to #824's Verification. Otherwise
leave the bullet and reword it to "the GENERAL restriction (arbitrary base); the FinSet
instantiation is #824's".
**`remediation.json` emits steps (2)–(4) only.** Step (5) — consolidating `Instance/FinSet/Corel.v`
into #824's `Instance/FinSet/Corelation.v` — is safe either way, since the 829→824 edge already
serialises the file.
**Recommendation: the reword, not the deletion**, unless you are prepared to edit #824 in the
same pass.

### 4.6 #547 requires editing a SECOND live issue, #534 (T4-6)

The corrected remediation changes #534's own append (*"should share the resulting lemma rather
than proving it twice"* → *"cover both routes under disjoint hypotheses…"*).
**Recommendation: edit both** — the #547 note alone contradicts #534's text and a reader will not
know which to believe. **Both are in `remediation.json`** (#534's as a block, because the quoted
string is not verbatim in the live body — see §6).

### 4.7 #647 bound refinement (T3-8)

`n + e ≤ 6` is solid. The parenthetical `e ≤ 4` rests on "loops excluded by acyclicity" and is a
weaker claim.
**Recommendation: keep only `n + e ≤ 6` (hence `n ≤ 6`, `e ≤ 5`)** — which is what
`remediation.json` emits. (The finding's original "at most 6 nodes and at most 3 edges" is FALSE:
n=2, e=4 parallel arrows is acyclic with exactly six arrows.)

### 4.8 #729's Riehl §4.5 clause (T3 Group D, stated alternative)

`remediation.json` emits the fibrewise-cartesian-closure checkbox on #729. The plan's stated
alternative is to re-home it on #732/#734 and correct `ledger.tsv:2617`'s part label to
`part: the fibrewise adjoint triple`. **Minor; either is defensible.**

---

## 5. CROSS-FILE MUTATIONS (not issue edits)

### 5.1 #570 mutates `ledger.tsv` on unverified evidence (T1-8)

Lines 790–791 `PARTIAL` → `ABSENT`, plus #570's Current state `Partial.` → `Absent.`. The rule
quoted from `schemas.md` is right ("a never-instantiated class does not qualify"), but the row
indices are inherited and both plans warn that ledger row numbers were never confirmed.
**Recommendation: verify the two rows, then apply.** Not in `remediation.json` — it is a
`ledger.tsv` edit, and the issue-body half is gated on it.

### 5.2 Ledger multi-part split for `7sketches:6.3.1:ex6.57` (#868 / #869) (T4 Group H item 5)

Four coupled edits: `ledger.tsv:1964` note column; a new PARTIAL row for #869;
`seven-sketches/issue-map.json` gains `"7sketches:6.3.1:ex6.57@869": 869`; and #869's trailer
`ids` become `["7sketches:6.3.1:thm6.58","7sketches:6.3.1:ex6.57"]`.
**Not in `remediation.json`** — three of the four are cross-file edits and the fourth is a trailer
`ids` change, for which the manifest has no mode. **Sequencing: apply the trailer edit LAST, or
merge it with whatever §3.6 decides.**

### 5.3 #722's ledger note (T4 Group E)

`ledger.tsv:1323` note column: the stray phrase *"the higher-order-logic/quantifier reading"*
belongs to `awodey:8.8:remark18` and should read *"every slice of a topos is again a topos"*.
**Not in `remediation.json`** (ledger edit). Line 1339 (#405) is correct as it stands.

### 5.4 The Awodey edition label is a campaign-wide decision (T2-J5)

`pagemap.md` establishes that the campaign PDF is the 1st-ed CMU pre-print (OLG 49, September
2005); ~34 issues label it "2nd ed. (Oxford Logic Guides 52)", inherited from the `*-drafts.md`
templates. #658's proposed fix (49 → 52) makes #658 *consistent with the corpus* and
*inconsistent with the calibration report*.
**Either (a) relabel the ~34 to match `pagemap.md` and leave #658 as-is, or (b) record an explicit
convention that "2nd ed." is shorthand for the pre-print and apply #658's edit. Do not apply #658
in isolation.**
**Recommendation: (a).** #679 gets no edit either way — its edition line is the only accurate one
in its batch, and `remediation.json` carries an explicit "do not touch the edition line" note on
it. *#658's edit is NOT in `remediation.json`.*
Note the friction: several entries in `remediation.json` add "(2nd ed.)" to Riehl citations
(#497, #520, #590, #772) — that is the **Riehl** edition, which is not in dispute.

### 5.5 Post-trailer blocks on #1011 / #1014 / #1016 (T3-9)

All three carry content after the trailer marked "(added on audit)"; all three still parse, and
the verdict rated them LOW/no-action.
**Options:** sweep them into F1 alongside #589/#918/#972, or accept that `file_chapter.py` will
silently skip the `ids` update on the next append to any of them.
**Recommendation: sweep them** — it is the same one-line defect, and `file_chapter.py:224`'s
silent `else` branch is exactly what produced the missing trailer ids elsewhere. *Not in
`remediation.json`* (no verdict, and the three were not enumerated as F1 targets).

### 5.6 F9's 19-issue `make todo` sweep reaches outside the audited set (T4-8)

Only #566 was audited; #567–#584 come from a machine-checked substring sweep (19 hits for
`` `make todo` clean. ``, 0 for the correct phrase; #585–#600 the exact complement). The defect is
real — `make todo` prints 89 pre-existing hits, so the box can never be ticked.
**`remediation.json` emits all 19** (verified: the substring occurs exactly once in each of the 19
live bodies). **Either accept the sweep as evidence or re-run it before applying.**

---

## 6. ITEMS NOT CONVERTIBLE AS SPECIFIED

### 6.1 #1005's page range is stated conditionally (T1 Group E)

The plan says: `(printed pp. 206–207, PDF pp. 226–228)` → `(printed pp. 206–208, PDF pp. 226–228)`
**if** the lemma runs onto printed p. 208 (consistent with #1006/#1007 putting Exercises 5.5.v–vii
on printed 208–209), **otherwise** `(printed pp. 206–207, PDF pp. 226–227)`.
**Nobody checked which.** Decide against the PDF; then it is a one-substring edit.

### 6.2 Blockquote relocations inside `## Dependencies` (T4 F5)

#843 (plus cosmetically #827, #829, #832): move a `> **SCOPE (added on audit).**` blockquote out
of `## Dependencies` to the end of `## Work to be done`. A *move* is not expressible in the
manifest's modes. The verdict itself rates this uniformity/readability, MEDIUM-minus, **not a
proven resolver bug**. **Do by hand or skip.** Note the explicit warning: after the move,
`## Dependencies` must still keep its `- Related (NOT blocking):` lines — the finding's "only the
Depends-on lines and nothing else" wording contradicts its own sibling remediation.

### 6.3 Trailer `ids` edits have no mode

The manifest supports `trailer_deps` but not `trailer_ids`. Affected, all **NOT in
`remediation.json`**: #370 (+`riehl:5.3:exii`), #373 (+`riehl:5.6:cor6`), #416
(+`riehl:E.1:thm-colimit-construction`), #384 (−`awodey:8.8:remark18`), #918
(+`riehl:2.2:cor8`), #1006 (+`riehl:5.5:example7`), #869 (§5.2). The #384 removal is stated inside
that issue's Group C block so it is at least recorded where an implementer will see it.
**All seven must be applied by hand, and #370/#373/#416 only AFTER their F1 trailer moves** —
while the trailer is not last, `file_chapter.py:224` falls to the `else` at `:231` and appends
without ever updating `ids`.

### 6.4 #534's quoted string is not verbatim in the live body

The plan quotes *"should share the resulting lemma rather than proving it twice"*; that exact
substring does not occur in #534's live body. Delivered as an appended correction block instead of
an in-place replacement. **Someone should locate the real sentence if an in-place fix is wanted.**
