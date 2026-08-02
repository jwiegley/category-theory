# Campaign 3 — Book-coverage catalog: MacLane / Awodey / Seven Sketches

**Frozen plan. Read-only for the purpose of lowering the bar.** Drafted
2026-07-22 from the user's /wiggum invocation; PAL-conferred before freezing
(see the consensus note at the end).

## Objective

Build a complete, dependency-aware catalog of every item of category theory
present in three books but missing from (or only partially covered by) this
library, recorded as GitHub issues on `jwiegley/category-theory` and organized
under three successive GitHub Projects (v2, owner `jwiegley`):

1. **MacLane** — Mac Lane, *Categories for the Working Mathematician*
   (`/Users/johnw/dl/Maclane_Categories.pdf`, 320 PDF pages, old scan —
   every page must be examined as a rendered image).
2. **Awodey** — Awodey, *Category Theory*
   (`/Users/johnw/dl/Awodey_Category_Theory.pdf`, 314 PDF pages).
3. **Seven Sketches** — Fong & Spivak, *Seven Sketches in Compositionality*
   (`/Users/johnw/dl/Spivak_Fong_Seven_Sketches.pdf`, 353 PDF pages).

The books are processed strictly in that order; a later book reuses the
earlier books' catalog for dedup. The campaign creates **no repo code
changes**; its repo-side artifacts (this plan, inventories, ledgers, the
handoff) stay untracked per campaign convention.

## Inventory scope ("every single item")

For each book, inventory EVERY:
- numbered definition, theorem, proposition, lemma, corollary;
- named-but-unnumbered construction or concept developed in the text
  (e.g. a category built in prose, a functor defined mid-section);
- exercise / problem statement.

Trivial restatements, historical asides, and pure motivation prose are
inventoried only when they carry mathematical content that could be
formalized. Every inventoried item gets a stable ID
`<book>:<chapter>.<section>:<kind><number-or-slug>` (e.g.
`maclane:III.1:thm2`, `awodey:9.5:ex4`, `7sketches:4.2:construction-collage`).

## Classification

Each item is classified against the library with file:line evidence:
- **PRESENT** — formalized in-tree in substance (statement matches up to
  presentation; setoid rephrasing is fine). Evidence required.
- **PARTIAL** — some of the item exists; the gap must be stated precisely.
- **ABSENT** — no in-tree counterpart.
- **OUT-OF-SCOPE** — not meaningfully formalizable in this library's setting
  (e.g. metamathematical remarks, set-theoretic foundations discussions,
  historical notes). Must carry a one-line justification; used sparingly.

PARTIAL and ABSENT items produce issues. PRESENT and OUT-OF-SCOPE do not,
but remain in the durable coverage matrix with their evidence.
Classification honesty is protected by an adversarial verification pass
(below): false-PRESENT silently loses work; false-ABSENT files noise.

## Issue contract (every filed issue)

Title: `<Book> <section-ref>: <concise item name>` (e.g.
`MacLane V.6: Adjoint functor theorem for complete lattice-ordered sets`).

Body sections, in order:
1. **Source** — book, edition, section, book page(s), PDF page(s), item
   ID(s) covered.
2. **Background** — 1–3 sentences; at least one link to nLab and/or
   Wikipedia (nLab preferred for category theory; both when useful).
3. **Current state in the library** — what exists (file:line), what is
   missing; for PARTIAL, the precise gap.
4. **Work to be done** — requirements: what to define/prove, suggested
   module path (Theory/ Structure/ Construction/ Instance/ per the
   library's layout), in-tree donors to build on.
5. **Definition of Done** — checklist; must include: statement fidelity to
   the book (setoid `≈` discipline, never `=` on morphisms); no
   `Admitted`/`admit`/`Axiom` (zero axioms in core theory per
   docs/AXIOMS.md scoping); `Print Assumptions` closed for each principal
   artifact; registered in `_CoqProject`; full `make` green on Rocq 9.1;
   builds on Coq 8.19/8.20 (nix targets); `make todo` adds no new hits;
   CLAUDE.md Key Files index updated if the result is flagship-level.
6. **Verification** — the exact commands/evidence a reviewer runs
   (single-file compile, `Print Assumptions` on named artifacts, nix build
   targets), plus "statement matches book §X" as a review item.
7. **Dependencies** — `Depends on: #N` lines (GitHub cross-links) for both
   in-catalog prerequisites and cross-book prerequisites. Where the
   repository supports native issue relationships ("blocked by"), mirror
   them there as well; the body lines are the source of truth.

Labels: `book:maclane` / `book:awodey` / `book:seven-sketches` (all books
that cover the item), plus `kind:theory` or `kind:exercise`, plus
`coverage-gap`. Project association: every project whose book covers the
item.

Granularity: one issue per coherent, independently-completable unit of
work (roughly: one PR's worth). A section's main theorem plus its
supporting lemmas is ONE issue; an exercise cluster forming one development
is ONE issue; do not file page-level or single-trivial-lemma issues, and do
not bundle unrelated results merely because they share a section.

## Dedup across books

One canonical issue per missing item of theory. When a later book covers an
item already filed: do NOT open a duplicate; instead (a) add the later
book's `book:` label, (b) add the issue to the later book's project,
(c) append an `## Also covered in` source block to the body. The ledger
records the mapping from every item ID to its issue (or PRESENT evidence).

## Pipeline per book (workflow-orchestrated; user authorized workflows)

- **A0 (calibration + page map)**: one agent reads front matter + TOC +
  sample pages; reports scan quality, book-page→PDF-page offset(s), chapter
  boundaries. Output: `pagemap.md` per book.
- **A (inventory)**: fan-out agents over PDF page ranges (≤20 pages each,
  1-page overlap at boundaries; ranges aligned to chapters via A0). Old
  scans are read as rendered page images via the Read tool. Output:
  structured item lists (JSON) per range.
- **B (merge)**: merge ranges into per-chapter inventory files; resolve
  boundary overlaps; sanity-check numbering continuity (gaps in theorem
  numbering = a missed page → re-read that page).
- **C (coverage)**: per-chapter agents classify every item
  (PRESENT/PARTIAL/ABSENT/OUT-OF-SCOPE) with file:line evidence, using
  CLAUDE.md's Key Files index, grep, and file reads.
- **D (adversarial verify)**: independent agents re-check every PRESENT
  claim (hunting false-PRESENT) and every ABSENT claim (hunting
  false-ABSENT/duplicates); disagreements resolved by a third look in the
  main loop.
- **E (draft)**: per-chapter agents draft issue bodies per the contract,
  with dependencies expressed as item IDs; links verified resolvable.
- **F (file)**: the MAIN LOOP (coordinator only) creates issues via `gh`,
  paced to respect API limits, applies labels, adds to project(s), records
  `item-ID → issue#` in the ledger TSV as it goes.
- **G (dependency resolution)**: post-pass rewrites item-ID dependencies
  into `Depends on: #N` via `gh issue edit`, and mirrors native
  relationships where supported.
- **H (fess audit)**: a fess-auditor samples filed issues against the book
  pages, the repo, and the ledger: link validity, classification honesty,
  template completeness, project/label association. Findings verified,
  then fixed in the main loop.

Fan-out is bounded at 3–5 concurrent agents per wiggum; subagents never
run `gh` mutations and never touch shared state — they return artifacts.

## Durable artifacts (all under `doc/plan/books/`, untracked)

- `<book>/pagemap.md` — A0 output.
- `<book>/inventory/<chapter>.json` — merged Phase-B inventories.
- `<book>/coverage/<chapter>.json` — Phase-C/D classifications + evidence.
- `<book>/issues/<chapter>.md` — Phase-E drafts (pre-filing).
- `ledger.tsv` — item ID → classification → issue# (or evidence) → projects.
- `doc/wiggum-handoff.md` — Campaign 3 section: phase status, attempt
  counters, learnings.

## Definition of Done

Per book: (1) the project exists and is linked to the repo; (2) pagemap +
complete inventory on disk covering every page of the PDF; (3) every item
classified with evidence and adversarially verified; (4) every
PARTIAL/ABSENT item mapped to exactly one issue satisfying the issue
contract; (5) issues associated to the correct project(s) and labels;
(6) dependency pass complete (`Depends on:` resolved to numbers);
(7) fess audit passed with findings folded; (8) ledger current.

Campaign: all three books done, in order; the working tree carries no
tracked changes (verified by `git status`); a closing summary is recorded
in the handoff. Wiggum's build/test/rebase gates are ADAPTED for this
no-code campaign: the "build passes" gate becomes "no tracked file was
modified and the baseline `make` state is untouched"; the "branch rebased"
gate is vacuous (no commits). This adaptation is frozen here, up front —
it is not a mid-campaign bar change.

## Stop-and-escalate (campaign-specific additions)

Standard wiggum conditions, plus: `gh` mutation failures persisting after 3
attempts (rate limits: back off and retry before counting an attempt);
unreadable/missing PDF pages that a re-read cannot recover; any sign the
account lacks permission for Projects v2 mutations; ambiguity about whether
a borderline item deserves an issue that evidence cannot settle (batch such
questions for the user rather than stalling the loop on each one).

## Consensus amendments (2026-07-22, folded pre-freeze; all strengthenings)

PAL consensus (gpt-5.5-pro 8/10, gemini-3.1-pro-preview 8/10, no
disagreements) confirmed the architecture and added the following, now
PART OF THE FROZEN PLAN:

1. **Granularity refinement**: a reusable definition / named construction /
   API-instance whose formalization serves multiple downstream issues gets
   its OWN issue (and becomes a dependency target); only proof-local
   support lemmas stay bundled with their theorem. Exercises bundle only
   when they form one mathematical development, never by mere adjacency.
2. **Dedup by normalized mathematical obligation**, not name similarity.
   When a later book states a strictly stronger/more general version:
   extend the canonical issue if one PR reasonably satisfies both,
   otherwise file a separate variant/generalization issue that
   depends on the canonical one.
3. **Phase C search protocol**: before ANY search, the agent must write an
   alias/abstraction expansion for the item (3–5 alternative names,
   likely typeclass encodings, Coq-idiom renderings, dual forms); search
   uses ripgrep over the whole tree (never only the CLAUDE.md index) plus
   the library's own naming conventions. Evidence contracts: PRESENT and
   PARTIAL verdicts must include a STATEMENT RECORD — the book statement
   (paraphrased) and the in-tree statement (quoted, file:line) side by
   side, with hypotheses/conclusion strength compared; ABSENT verdicts
   must include a NEGATIVE-SEARCH LOG (aliases tried + search commands).
4. **Phase D discipline**: the verifier performs its OWN blind alias
   expansion + search BEFORE looking at C's evidence (for ABSENT claims);
   PRESENT claims are checked against the statement record for
   same-name-weaker-statement, special-case-only, dual-assumed-but-absent,
   and not-actually-compiled failure modes; OUT-OF-SCOPE claims are
   audited too; Print Assumptions spot-checks on PRESENT claims for
   foundational results (docs/AXIOMS.md is the baseline).
5. **Completeness is page-accounting, not numbering**: Phase A agents
   return a PER-PAGE report (every PDF page → items found, or an explicit
   "no inventoriable items" entry); Phase B verifies every page of the
   book's inventoriable range is accounted for. Numbering continuity and
   TOC/section cross-checks are secondary heuristics; exercise counts per
   section are reconciled against the book's own statements where visible.
6. **Copyright**: filed issues PARAPHRASE book statements and cite
   section/page; never reproduce substantial verbatim text of theorems or
   exercises. (The repo is public.)
7. **Machine-readable trailer**: every issue body ends with an HTML
   comment block `<!-- catalog: {"ids":[...],"deps":[...]} -->` carrying
   item IDs and item-ID dependencies; Phase G rewrites the human-readable
   Depends-on lines to #N but PRESERVES the item-ID trailer, then runs an
   automated graph validation (no dangling references, no self-deps, no
   cycles) over the ledger.
8. **Phase F idempotency**: append to ledger.tsv synchronously after EACH
   successful gh mutation; on any resume, pre-flight the ledger (and
   `gh issue list` for the book label) so no item is double-filed.
9. **Pilot**: MacLane Chapter I runs the ENTIRE pipeline A→H, including a
   small filing batch, and the pilot's output is reviewed in the main
   loop before any mass processing of remaining chapters.
10. **Schema validation**: inventory/coverage JSON and ledger rows are
    schema-checked before filing.

## Model/infrastructure notes

Subagent model env pin: `claude-fable-5` (settings.json, read at session
start). Anvil: dedicated Emacs daemon backend available; used per the anvil
skill where it amplifies; its buffer checks do NOT cover the user's
interactive Emacs (recorded boundary). GitHub auth: active account
`jwiegley` with `repo` + `project` scopes verified. Issues API sanity
verified against the repo (default labels only; no open issues at start).
