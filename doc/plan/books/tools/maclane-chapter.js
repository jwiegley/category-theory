export const meta = {
  name: 'maclane-chapter',
  description: 'MacLane chapter pipeline: inventory -> merge -> coverage -> verify -> draft (args-parameterized)',
  phases: [
    { title: 'Inventory', detail: 'page-image inventory, 2 agents' },
    { title: 'Merge', detail: 'merge ranges, page accounting, batch split' },
    { title: 'Coverage', detail: 'classify vs library: alias expansion, evidence, statement records' },
    { title: 'Verify', detail: 'adversarial blind-first verification' },
    { title: 'Draft', detail: 'issue drafts for PARTIAL/ABSENT items, same-book dedup' },
  ],
}

const A = typeof args === 'string' ? JSON.parse(args) : args
// 2026-07-22: Fable 5 credits exhausted; user directive = Opus for all
// subagents. Applied to the draft call first (cache-safe for the Ch IV
// resume); extended to every call for Ch V onward.
const MODEL = 'opus'
// A = { roman, title, pdfStart, pdfEnd, offset, splitAt,
//       sections: [{n, name, printed}], scratch }
const R = A.roman
const SCRATCH = A.scratch
const REPO = '/Users/johnw/src/category-theory/master'
const PDF = '/Users/johnw/dl/Maclane_Categories.pdf'
const SCHEMAS = REPO + '/doc/plan/books/schemas.md'
const PLAN = REPO + '/doc/plan/books-catalog-campaign.md'
const LEDGER = REPO + '/doc/plan/books/ledger.tsv'
const FILED = REPO + '/doc/plan/books/maclane/filed-issues.tsv'

// section -> pdf page helper
const secs = A.sections.map((s, i) => {
  const pdf = s.printed + A.offset
  const next = A.sections[i + 1]
  const end = next ? next.printed + A.offset - 1 : A.pdfEnd
  return { ...s, pdf, end }
})
const secList = secs.map(s => `${R}.${s.n} ${s.name} (printed ${s.printed} / PDF ${s.pdf}-${s.end})`).join('; ')

// MAX=2 counting semaphore — standing user directive; never raise.
let active = 0
const waiters = []
async function gated(fn) {
  while (active >= 2) await new Promise(r => waiters.push(r))
  active++
  try { return await fn() } finally { active--; const w = waiters.shift(); if (w) w() }
}

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
const MERGE_SCHEMA = {
  type: 'object',
  properties: {
    output_path: { type: 'string' },
    summary: { type: 'string' },
    item_count: { type: 'number' },
    problems: { type: 'array', items: { type: 'string' } },
    batches: { type: 'array', items: { type: 'array', items: { type: 'string' } } },
  },
  required: ['output_path', 'summary', 'item_count', 'batches'],
}

const CH = `Chapter ${R} "${A.title}" of Mac Lane, Categories for the Working Mathematician, 2nd ed. Printed pages ${A.pdfStart - A.offset}-${A.pdfEnd - A.offset} = PDF pages ${A.pdfStart}-${A.pdfEnd} (printed = PDF - ${A.offset} throughout this chapter). Sections: ${secList}. The PDF is an OLD SCAN: the rendered page images (what the Read tool shows you for PDF pages) are the source of truth; ignore any text layer. Numbering conventions: theorems/propositions/lemmas/corollaries restart at 1 WITHIN EACH SECTION; many key items are UNNUMBERED "Definition."/"Lemma." blocks; exercises sit at section ends numbered 1,2,3... per section; unnumbered end-of-chapter "Notes." blocks are historical prose, not inventoriable. Full calibration report: ${REPO}/doc/plan/books/maclane/pagemap.md.`

const INV_RULES = `Inventory EVERY: definition (including unnumbered "Definition." blocks and definitions made in running prose), theorem/proposition/lemma/corollary, exercise, and named-but-unnumbered construction developed in the text (a category, functor, or transformation built in prose). Record remarks only when they carry formalizable mathematical content (kind "remark"). Skip pure historical/motivational prose. IDs: maclane:${R}.<section>:<kind><n> with kind in {def,thm,prop,lem,cor,ex,construction,remark}; <n> is the book's own number when one exists, else the per-section per-kind ordinal in order of appearance. statement_summary: PARAPHRASE ONLY (never verbatim beyond a <=10-word technical phrase) but mathematically complete — hypotheses and conclusion precise enough that a coverage agent can classify the item against a Coq library WITHOUT reopening the PDF. First read the schema file ${SCHEMAS} (section "Inventory range report") and conform to it exactly: the pages[] array MUST contain an entry for EVERY PDF page of your OWNED range, with empty:true where a page has nothing inventoriable; an item spanning pages is recorded once, under its starting page, with all pdf_pages listed. You are READ-ONLY except for your single output file; never run git or gh; do not modify anything else.`

function invPrompt(owned, readRange, outfile) {
  return `You are a Phase-A page-image inventory agent for a book-coverage campaign. ${CH}

Your OWNED pages: PDF ${owned} (account for every one of them in pages[]). Read PDF pages ${readRange} of ${PDF} with the Read tool (pages parameter; split into calls of <=20 pages) — the extra page(s) beyond your owned range are context so you can recognize items that continue across the boundary; items STARTING outside your owned range belong to the other agent, do not record them.

${INV_RULES}

Write your completed JSON object to ${SCRATCH}/${outfile} (create with the Write tool). Then return exactly: output_path, summary (2-4 sentences: what the range contains, item totals by kind), item_count, problems[] (illegible statements — also flag "statement-illegible" on the item —, suspected numbering gaps, anomalies).`
}

const mid = A.splitAt
const INV_A = invPrompt(`${A.pdfStart}-${mid}`, `${A.pdfStart}-${Math.min(mid + 1, A.pdfEnd)}`, `inventory-${R}-A.json`)
const INV_B = invPrompt(`${mid + 1}-${A.pdfEnd}`, `${Math.max(mid, A.pdfStart)}-${A.pdfEnd}`, `inventory-${R}-B.json`)

function mergePrompt(pa, pb) {
  return `You are the Phase-B merge agent for MacLane Chapter ${R}. ${CH}

Read the schema file ${SCHEMAS}, then the two range reports ${pa} and ${pb}. Tasks:
1. Validate both against the "Inventory range report" schema; note violations in problems[].
2. Verify PAGE ACCOUNTING: the union of pages[] entries must tile PDF ${A.pdfStart}-${A.pdfEnd} exactly (every page present exactly once across the two owned ranges). Missing/duplicated pages -> problems[] with the page numbers.
3. Dedupe: if the same item appears in both files (boundary spill), keep one record, merging pdf_pages.
4. Numbering-continuity check (SECONDARY heuristic): within each section, for numbered kinds, report gaps in 1..n sequences in problems[] (do not invent items).
5. Exercise reconciliation: count exercises per section; note in the summary.
6. Write the merged single JSON object (schema-conformant, range ${A.pdfStart}-${A.pdfEnd}) to ${SCRATCH}/inventory-${R}.json.
7. Split all item IDs into batches of 10-15, in section order, keeping each section's items contiguous where possible.
Return: output_path, summary (totals by kind and per section), item_count, problems, batches. You are READ-ONLY except ${SCRATCH}/inventory-${R}.json; never run git or gh.`
}

const CLASS_DEFS = `Classification definitions (frozen): PRESENT = formalized in-tree in substance (statement matches up to presentation; setoid rephrasing with hom-setoids and ≈ instead of = is faithful); PARTIAL = some of the item exists, the gap must be stated precisely; ABSENT = no in-tree counterpart; OUT_OF_SCOPE = not meaningfully formalizable in this library's setting (use SPARINGLY, one-line justification required; note the library HAS universe polymorphism, so size/foundations discussions are often PARTIAL or PRESENT, not OUT_OF_SCOPE).`

function covPrompt(ids, k) {
  return `You are a Phase-C coverage-classification agent. The library: ${REPO} (Coq/Rocq category theory, ~484 .v files; its CLAUDE.md Key Files index is a MAP to start from, but NEVER conclude ABSENT from the index alone — always search the whole tree). Read ${SCHEMAS} (section "Coverage record") and the merged inventory ${SCRATCH}/inventory-${R}.json first.

Your items (classify EVERY one): ${JSON.stringify(ids)}

${CLASS_DEFS}

MANDATORY protocol per item, in this order:
1. ALIAS EXPANSION first, before any search: write 3-5 alternative names — textbook synonyms, likely Coq/typeclass encodings, this library's naming conventions, and dual forms.
2. Search the whole tree with Grep over *.v for each alias; read the candidate files at the hit sites.
3. Classify. Evidence contracts (MANDATORY): PRESENT/PARTIAL require evidence[] (file, line, symbol, quoted in-tree statement) AND statement_record {book (paraphrase), intree (quote), strength_comparison} — actively hunt the same-name-but-weaker trap (extra hypotheses, special case only, apex-only vs cone-level, dual assumed but absent, definition without the API the book item needs). ABSENT requires negative_search_log[] listing every alias and the actual searches run. OUT_OF_SCOPE requires out_of_scope_reason. Exercises: classify the exercise's mathematical CONTENT. Leave verifier null.
Write the JSON array of coverage records for your batch to ${SCRATCH}/coverage-${R}-${k}.json. Return output_path, summary (counts per classification + notable calls), item_count, problems. READ-ONLY except your output file; never run git or gh.`
}

function verPrompt(covPath, ids, k) {
  return `You are a Phase-D adversarial verification agent. Read ${SCHEMAS} and the merged inventory ${SCRATCH}/inventory-${R}.json for the statements of these items: ${JSON.stringify(ids)}. The library: ${REPO}.

${CLASS_DEFS}

STRICT ORDER — the value of your pass depends on it:
1. BEFORE opening the coverage file, do your OWN alias expansion and whole-tree searches for EVERY item in the batch and write down your own preliminary classification + search log (keep it; it goes into verifier.notes when relevant).
2. Only then read ${covPath} and compare, record by record:
   - PRESENT/PARTIAL claims: open the cited files; confirm the evidence exists at the cited location, the quote is accurate, and strength_comparison is honest. Hunt: same-name-weaker-statement, special-case-only, dual-assumed-but-absent, definition-without-required-API, file not registered in ${REPO}/_CoqProject.
   - ABSENT claims: did YOUR blind search find a counterpart the classifier missed?
   - OUT_OF_SCOPE claims: is the justification legitimate under the frozen definition?
3. Fill verifier on every record: {"verdict":"CONFIRMED"} or {"verdict":"OVERTURNED:<NEWCLASS>","notes":"..."}; when you overturn, also CORRECT the record's fields with your own findings AND set "phase_c_classification" on the record to the classifier's ORIGINAL verdict before you overwrite the classification field (provenance must survive — do not destroy what Phase C said).
4. LIBRARY-DEFECT CHANNEL: if while confirming ANY record (especially a PRESENT one) you find a genuine in-tree defect — a comment that contradicts the code, a header claiming something is built when it is not, a stale pointer — record it in problems[] prefixed "LIBRARY-DEFECT: <file>:<line> — <what is wrong>". PRESENT items generate no issue, so without this channel such findings are lost.
Write the verified array to ${SCRATCH}/verified-${R}-${k}.json. Return output_path, summary (confirmed/overturned counts, overturned IDs with one-line reasons), item_count, problems. READ-ONLY except your output file; never run git or gh.`
}

function draftPrompt(verifiedPaths) {
  return `You are the Phase-E issue-drafting agent for MacLane Chapter ${R}. Read, in order: (1) the frozen campaign plan ${PLAN} — especially the Issue contract, Granularity, Dedup, and Consensus amendments sections; (2) ${SCHEMAS} (section "Issue draft"); (3) the merged inventory ${SCRATCH}/inventory-${R}.json; (4) ALL verified coverage files: ${JSON.stringify(verifiedPaths)}; (5) the ALREADY-FILED issue catalog: ${FILED} (number<TAB>title) and the item ledger ${LEDGER} (item_id, classification, issue#, projects, note).

For every item whose FINAL classification (after verifier verdicts) is PARTIAL or ABSENT:
- SAME-BOOK DEDUP FIRST: if the item's mathematical obligation is already covered by a filed issue (check the ledger + filed titles; e.g. a topic introduced in an earlier chapter and revisited here), do NOT draft a new issue. Instead add it to a duplicates list: {"item_id", "issue" (number), "append_block": a short markdown block titled "### Also covered by" citing this chapter's section/pages/item-id and any NEW aspect the later section adds}. If the later section demands strictly MORE than the filed issue's scope, draft a NEW issue for the increment that "Depends on: #<that issue>".
- Otherwise group items into issues per the frozen granularity policy: one independently-completable unit (~one PR) per issue; a reusable definition/construction serving multiple downstream issues gets its OWN issue; proof-local lemmas bundle with their theorem; exercises bundle only when they form one mathematical development. PRESENT and OUT_OF_SCOPE items get NO issue.

Draft each issue exactly per the contract: title "MacLane ${R}.<sec>: <concise name>"; body sections Source / Background (1-3 sentences; at least one nLab and/or Wikipedia link — canonical slugs; VERIFY each link resolves with WebFetch and list failures in problems) / Current state in the library (file:line evidence and the precise gap, from the verified records) / Work to be done (what to define and prove, suggested module path per the library's Theory-Structure-Construction-Instance layout, in-tree donors) / Definition of Done (the frozen checklist, as markdown checkboxes) / Verification (concrete reviewer commands) / Dependencies. Dependency rules: on a FILED issue -> write "Depends on: #<number>" directly; on a same-chapter item -> "Depends on: <item-id>" (resolved later); on a future-chapter item -> deps_pending in the YAML. PARAPHRASE everything — the repo is public; never reproduce book text verbatim. Each draft gets the YAML header (title, labels: [book:maclane, kind:theory|kind:exercise, coverage-gap], projects: [4], covers, deps_item_ids, deps_pending) and the body ends with the catalog HTML trailer. The trailer's "deps" array must list EVERY dependency the body declares — same-chapter ones as item IDs and cross-chapter ones as the "#N" strings — so the trailer alone is a complete machine-readable edge set (a validator reading trailers only must not silently see a partial graph).

LIBRARY-DEFECT PASS: scan every verified record's problems[]/verifier.notes for entries flagged "LIBRARY-DEFECT". Each one must land somewhere visible: fold it into the Definition of Done of whichever drafted issue touches that file, or — if no drafted issue touches it — emit it in your returned problems[] as "UNPLACED LIBRARY-DEFECT: <file>:<line> — <what>" so the coordinator can surface it. Defects found while confirming a PRESENT item otherwise vanish, since PRESENT items generate no issue.

In Work-to-be-done and Current-state PROSE, never reference bare item IDs (an outside reader cannot resolve them): cite the filed issue number when one exists, else the book section (item IDs belong only in Source, Dependencies lines, the YAML, and the trailer). Write ALL drafts to ${SCRATCH}/drafts-${R}.md, separated by lines containing exactly "---8<---"; write the duplicates list (possibly empty) to ${SCRATCH}/duplicates-${R}.json. Return output_path (drafts file), duplicates_path, summary (issue count + full title list + duplicate count), item_count (= issue count), problems. READ-ONLY except your two output files; never run git or gh.`
}

phase('Inventory')
const [invA, invB] = await Promise.all([
  gated(() => agent(INV_A, { label: `inv:${R}-A`, phase: 'Inventory', schema: PATH_STATS })),
  gated(() => agent(INV_B, { label: `inv:${R}-B`, phase: 'Inventory', schema: PATH_STATS })),
])
if (!invA || !invB) throw new Error('an inventory agent returned null — cannot proceed')
log(`inventory done: A=${invA.item_count} items, B=${invB.item_count} items`)

phase('Merge')
const merged = await gated(() => agent(mergePrompt(invA.output_path, invB.output_path), { label: `merge:${R}`, phase: 'Merge', effort: 'low', schema: MERGE_SCHEMA }))
if (!merged) throw new Error('merge agent returned null')
log(`merged: ${merged.item_count} items in ${merged.batches.length} batches; problems: ${(merged.problems || []).join('; ') || 'none'}`)

const verified = await pipeline(
  merged.batches,
  (ids, _orig, k) => gated(() => agent(covPrompt(ids, k), { label: `cover:${R}-${k}`, phase: 'Coverage', schema: PATH_STATS })),
  (cov, ids, k) => cov ? gated(() => agent(verPrompt(cov.output_path, ids, k), { label: `verify:${R}-${k}`, phase: 'Verify', schema: PATH_STATS })) : null,
)
const okVer = verified.filter(Boolean)
log(`verified ${okVer.length}/${merged.batches.length} batches`)
if (okVer.length === 0) throw new Error('no coverage batch survived')

phase('Draft')
const draft = await gated(() => agent(draftPrompt(okVer.map(v => v.output_path)), { label: `draft:${R}`, phase: 'Draft', schema: PATH_STATS, model: MODEL }))

return {
  chapter: R,
  inventory: { path: merged.output_path, items: merged.item_count, problems: merged.problems || [] },
  coverage: okVer.map(v => ({ path: v.output_path, summary: v.summary, problems: v.problems || [] })),
  drafts: draft ? { path: draft.output_path, duplicates: draft.duplicates_path || null, summary: draft.summary, problems: draft.problems || [] } : null,
  batches_lost: merged.batches.length - okVer.length,
}