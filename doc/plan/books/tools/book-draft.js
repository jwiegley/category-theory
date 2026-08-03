export const meta = {
  name: 'book-draft',
  description: 'Phase E only: re-run the issue drafter for a chapter whose upstream artifacts already exist on disk',
  phases: [{ title: 'Draft', detail: 'one drafter, retried on transient API failure' }],
}

// args: same `book`/`roman`/`title`/`pdfStart`/`pdfEnd`/`offset`/`sections`/`scratch` as
// book-chapter.js, PLUS verifiedPaths: [<verified-*.json>, ...].
//
// WHY THIS EXISTS: the Ch2 drafter died on a transient 'API Error: Server error
// mid-response' after 17 upstream agents had already succeeded. Resuming the full
// pipeline is the obvious move and it BACKFIRED -- I had edited invPrompt first, which
// invalidated the cache for the FIRST agents and therefore the whole chain, so the resume
// re-ran inventory from scratch (and hit 529s). Decoupling Phase E means a drafter failure
// costs one agent, never eighteen, and is immune to cache-key changes upstream.
const A = typeof args === 'string' ? JSON.parse(args) : args
const MODEL = 'opus'
const BOOK = A.book
const IDP = BOOK.id
const R = A.roman
const SCRATCH = A.scratch
const REPO = '/Users/johnw/src/category-theory/master'
const SCHEMAS = REPO + '/doc/plan/books/schemas.md'
const PLAN = REPO + '/doc/plan/books-catalog-campaign.md'
const LEDGER = REPO + '/doc/plan/books/ledger.tsv'
const FILED = REPO + '/doc/plan/books/' + IDP + '/filed-issues.tsv'
const PAGEMAP = REPO + '/doc/plan/books/' + IDP + '/pagemap.md'
const PRIOR = (BOOK.priorBooks || []).map(b => REPO + '/doc/plan/books/' + b + '/filed-issues.tsv')
const secList = (A.sections || []).map(s => s.name + ' (printed ' + s.printed + ')').join('; ')
const scanNote = BOOK.scan ? 'This is a SCANNED book; read pages as images.' : ''
const CH = 'Chapter ' + R + ' "' + A.title + '" of ' + BOOK.cite + '. Printed pages ' + (A.pdfStart - A.offset) + '-' + (A.pdfEnd - A.offset) + ' = PDF pages ' + A.pdfStart + '-' + A.pdfEnd + ' (printed = PDF - ' + A.offset + ' throughout this chapter). Sections: ' + secList + '. ' + scanNote + ' Numbering: ' + BOOK.numbering + ' Full calibration report: ' + PAGEMAP + '.'
const PATH_STATS = {
  type: 'object',
  properties: {
    output_path: { type: 'string' },
    summary: { type: 'string' },
    item_count: { type: 'number' },
    problems: { type: 'array', items: { type: 'string' } },
    duplicates_path: { type: 'string' },
  },
  required: ['output_path', 'summary'],
}
function draftPrompt(verifiedPaths) {
  const priorNote = PRIOR.length
    ? `CROSS-BOOK DEDUP: this is NOT the first book in the campaign. Before drafting, also read the prior books' filed catalogs: ${JSON.stringify(PRIOR)}. If an item's mathematical obligation is ALREADY covered by an issue filed for an earlier book (same theorem/definition, e.g. Yoneda, adjunctions, limits — mathematics belongs to the theory, not the book), do NOT file a new issue: add it to the duplicates list targeting that existing issue number, with an "### Also covered by" block citing THIS book's section/pages. Only file a NEW issue if this book demands strictly MORE than the existing issue's scope (then "Depends on: #<that issue>"). Cross-book duplicates are how the catalog stays one-issue-per-obligation.`
    : ''
  return `You are the Phase-E issue-drafting agent for ${BOOK.name} Chapter ${R}. Read, in order: (1) the frozen campaign plan ${PLAN} — especially the Issue contract, Granularity, Dedup, and Consensus amendments sections; (2) ${SCHEMAS} (section "Issue draft"); (3) the merged inventory ${SCRATCH}/inventory-${R}.json; (4) ALL verified coverage files: ${JSON.stringify(verifiedPaths)}; (5) the ALREADY-FILED issue catalog for THIS book: ${FILED} (number<TAB>title) and the item ledger ${LEDGER} (item_id, classification, issue#, projects, note).

${priorNote}

For every item whose FINAL classification (after verifier verdicts) is PARTIAL or ABSENT:
- SAME-BOOK DEDUP FIRST: if the item's mathematical obligation is already covered by a filed issue for THIS book (check the ledger + filed titles), do NOT draft a new issue. Instead add it to a duplicates list: {"item_id", "issue" (number), "append_block": a short markdown block titled "### Also covered by" citing this chapter's section/pages/item-id and any NEW aspect the later section adds}. CLOSURE-TRACKING RULE: if the append names a NEW formalizable aspect that the target issue's Definition-of-Done checklist does NOT already cover (a dual direction, an added corollary, an extra concrete instance), the append_block MUST include that aspect as a markdown CHECKBOX line "- [ ] (from <BookName> §<sec>) <the new aspect>" — so the increment is a trackable sub-obligation that gates the issue's closure, not closure-invisible prose. (If the target's existing DoD already scopes the aspect — e.g. it says "and dually" — a checkbox is optional; note that instead.) If the later section demands strictly MORE than the filed issue's scope AND the increment is substantial (its own PR), draft a NEW issue for it that "Depends on: #<that issue>" rather than an append.
- MULTI-PART RULE: if a MULTI-PART item (an exercise with parts a/b/c, or a definition covering several distinct notions) deduplicates on SOME parts but has other parts that are distinct FORMALIZABLE obligations not covered by the target issue, do NOT bury those parts as prose in the append block. Either file the non-matching parts as their own small issue (which may "Depends on: #<target>"), or record them in deps_pending — a clean formalizable increment must become a first-class obligation, never append-only prose.
- Otherwise group items into issues per the frozen granularity policy: one independently-completable unit (~one PR) per issue; a reusable definition/construction serving multiple downstream issues gets its OWN issue; proof-local lemmas bundle with their theorem; exercises bundle only when they form one mathematical development. PRESENT and OUT_OF_SCOPE items get NO issue.

Draft each issue exactly per the contract: title "${BOOK.name} ${R}.<sec>: <concise name>"; body sections Source (cite ${BOOK.name}, the section, printed pages, PDF pages, item IDs) / Background (1-3 sentences; at least one nLab and/or Wikipedia link — canonical slugs; VERIFY each link resolves with WebFetch and list failures in problems) / Current state in the library (file:line evidence and the precise gap, from the verified records) / Work to be done (what to define and prove, suggested module path per the library's Theory-Structure-Construction-Instance layout, in-tree donors) / Definition of Done (the frozen checklist, as markdown checkboxes) / Verification (concrete reviewer commands) / Dependencies. Dependency rules: on a FILED issue (this book OR a prior book) -> write "Depends on: #<number>" directly; on a same-chapter item -> "Depends on: <item-id>" (resolved later); on a future-chapter item -> deps_pending in the YAML. PARAPHRASE everything — the repo is public; never reproduce book text verbatim. Each draft gets the YAML header (title, labels: [book:${IDP}, kind:theory|kind:exercise, coverage-gap], projects: [${BOOK.project}], covers, deps_item_ids, deps_pending) and the body ends with the catalog HTML trailer. The trailer's "deps" array must list EVERY dependency the body declares — same-chapter ones as item IDs and cross-chapter/cross-book ones as the "#N" strings — so the trailer alone is a complete machine-readable edge set.

LIBRARY-DEFECT PASS: scan every verified record's problems[]/verifier.notes for entries flagged "LIBRARY-DEFECT". Each one must land somewhere visible: fold it into the Definition of Done of whichever drafted issue touches that file, or — if no drafted issue touches it — emit it in your returned problems[] as "UNPLACED LIBRARY-DEFECT: <file>:<line> — <what>" so the coordinator can surface it.

In Work-to-be-done and Current-state PROSE, never reference bare item IDs (an outside reader cannot resolve them): cite the filed issue number when one exists, else the book section (item IDs belong only in Source, Dependencies lines, the YAML, and the trailer). Write ALL drafts to ${SCRATCH}/drafts-${R}.md, separated by lines containing exactly "---8<---"; write the duplicates list (possibly empty) to ${SCRATCH}/duplicates-${R}.json. Return output_path (drafts file), duplicates_path, summary (issue count + full title list + duplicate count), item_count (= issue count), problems. READ-ONLY except your two output files; never run git or gh.`
}

phase('Draft')
let draft = null
for (let attempt = 1; attempt <= 3 && !draft; attempt++) {
  if (attempt > 1) log('drafter attempt ' + attempt + ' (previous attempt returned null)')
  draft = await agent(draftPrompt(A.verifiedPaths), {
    label: 'draft:' + R + (attempt > 1 ? ':retry' + attempt : ''),
    phase: 'Draft',
    schema: PATH_STATS,
    model: MODEL,
  })
}
if (!draft) return { error: 'drafter returned null after 3 attempts', chapter: R }

return {
  chapter: R,
  book: IDP,
  drafts: { path: draft.output_path, duplicates: draft.duplicates_path || null, summary: draft.summary, problems: draft.problems || [] },
}
