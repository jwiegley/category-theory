export const meta = {
  name: 'book-a0',
  description: 'Phase A0 calibration for a book: edition, page-offset function, numbering scheme, chapter ranges',
  phases: [
    { title: 'Calibrate', detail: 'TOC/front-matter reader and independent offset prober, in parallel' },
    { title: 'Reconcile', detail: 'merge both, resolve disagreements, emit the pagemap' },
  ],
}

// args: {book, title, pdf, pages, project, priorBooks}
const A = typeof args === 'string' ? JSON.parse(args) : args
const MAX = 2

const TOC_SCHEMA = {
  type: 'object',
  required: ['edition', 'chapters', 'numbering', 'notes'],
  properties: {
    edition: { type: 'string', description: 'exact edition/printing/date as stated on the title or copyright page' },
    front_matter_pages: { type: 'string', description: 'which PDF pages are front matter, and how they are numbered' },
    chapters: {
      type: 'array',
      items: {
        type: 'object',
        required: ['n', 'title', 'printed_start', 'sections'],
        properties: {
          n: { type: 'string' },
          title: { type: 'string' },
          printed_start: { type: 'integer' },
          sections: {
            type: 'array',
            items: {
              type: 'object',
              required: ['n', 'name', 'printed'],
              properties: { n: { type: 'string' }, name: { type: 'string' }, printed: { type: 'integer' } },
            },
          },
        },
      },
    },
    numbering: {
      type: 'string',
      description:
        'How numbered environments are counted: ONE shared counter per chapter, or per-section, or per-kind? Where do exercises live and how are they numbered? Are displayed equations on a separate counter? Quote an example that proves it.',
    },
    exercise_scheme: { type: 'string' },
    notes: { type: 'array', items: { type: 'string' } },
  },
}

const OFFSET_SCHEMA = {
  type: 'object',
  required: ['uniform', 'probes', 'conclusion'],
  properties: {
    uniform: { type: 'boolean', description: 'true iff ONE offset works for the whole body' },
    offset: { type: ['integer', 'null'], description: 'pdf_page - printed_page, when uniform' },
    blocks: {
      type: 'array',
      description: 'when NOT uniform: per-range offsets, with the cause (dropped blank versos, plates, part-title pages)',
      items: {
        type: 'object',
        required: ['pdf_from', 'pdf_to', 'offset'],
        properties: {
          pdf_from: { type: 'integer' },
          pdf_to: { type: 'integer' },
          offset: { type: 'integer' },
          cause: { type: 'string' },
        },
      },
    },
    probes: {
      type: 'array',
      description: 'every page actually opened: what printed folio it showed and what content',
      items: {
        type: 'object',
        required: ['pdf_page', 'printed_folio', 'evidence'],
        properties: {
          pdf_page: { type: 'integer' },
          printed_folio: { type: 'string' },
          evidence: { type: 'string' },
        },
      },
    },
    conclusion: { type: 'string' },
    legibility: { type: 'array', items: { type: 'string' } },
  },
}

const RECONCILE_SCHEMA = {
  type: 'object',
  required: ['agreement', 'chapters', 'pagemap_markdown', 'warnings'],
  properties: {
    agreement: { type: 'string', description: 'where the two agents agreed, and every place they did not' },
    disagreements: { type: 'array', items: { type: 'string' } },
    chapters: {
      type: 'array',
      description: 'FINAL per-chapter launch args for the chapter pipeline',
      items: {
        type: 'object',
        required: ['roman', 'title', 'pdfStart', 'pdfEnd', 'offset', 'splitAt', 'sections'],
        properties: {
          roman: { type: 'string' },
          title: { type: 'string' },
          pdfStart: { type: 'integer' },
          pdfEnd: { type: 'integer' },
          offset: { type: 'integer' },
          splitAt: { type: 'integer', description: 'PDF page to split the two inventory ranges at, near the midpoint' },
          sections: {
            type: 'array',
            items: {
              type: 'object',
              required: ['n', 'name', 'printed'],
              properties: { n: { type: 'integer' }, name: { type: 'string' }, printed: { type: 'integer' } },
            },
          },
        },
      },
    },
    pagemap_markdown: { type: 'string', description: 'the complete pagemap.md body, ready to write to disk' },
    warnings: { type: 'array', items: { type: 'string' } },
  },
}

const PDF = A.pdf
const HDR = [
  'Book: ' + A.title,
  'PDF: ' + PDF + '  (' + A.pages + ' pages total)',
  '',
  'Read the PDF AS IMAGES. This is a calibration pass: everything downstream (every',
  'inventory range, every page-accounting check) is computed from what you report, so a',
  'wrong offset silently corrupts all seven chapters.',
].join('\n')

function tocPrompt() {
  return [
    HDR,
    '',
    'YOUR JOB: the edition, the full table of contents, and the NUMBERING SCHEME.',
    '',
    '1. Open the title and copyright pages. Report the exact edition/printing/date.',
    '2. Read the complete table of contents. Report every chapter and every section with',
    '   its PRINTED page number (the folio shown on the page, not the PDF index).',
    '3. Determine the numbering scheme by OPENING BODY PAGES, not by guessing:',
    '   - Is there ONE shared counter per chapter across Definition/Theorem/Proposition/',
    '     Lemma/Corollary/Example/Remark, or a separate counter per kind, or per section?',
    '   - Quote a specific example that PROVES your answer (e.g. if you see "Definition 1.7"',
    '     followed later by "Example 1.8", that is a shared per-chapter counter).',
    '   - Where do exercises live? Numbered how? Are they inline within sections or',
    '     collected at the end of a chapter?',
    '   - Are displayed equations on their own counter? (Mistaking an equation number for',
    '     an item number is a known failure mode in this campaign.)',
    '4. Note anything structurally unusual: unnumbered environments, part divisions,',
    '   appendices, an index, boxed asides, exercise solutions.',
    '',
    'Do NOT report a page offset -- another agent determines that independently. Report only',
    'PRINTED page numbers here.',
  ].join('\n')
}

function offsetPrompt() {
  return [
    HDR,
    '',
    'YOUR JOB: determine the PDF-page to PRINTED-page offset function, empirically.',
    '',
    'Do NOT read the table of contents and do NOT assume the offset is constant. In this',
    'campaign one book (Mac Lane) had a NON-UNIFORM offset -- nine blank versos had been',
    'dropped from the scan, so the offset drifted from +11 down to +3 across the book, and',
    'every agent that assumed one offset produced wrong page citations.',
    '',
    'METHOD:',
    '1. Probe at least 10 pages spread across the whole PDF (early, middle, late, and near',
    '   any suspected structural boundary). For each, record the PDF page index and the',
    '   printed folio actually visible on the page.',
    '2. Compute pdf_page - printed_page at each probe. If the value is constant, say so and',
    '   report the single offset. If it drifts, BISECT to find where each change happens and',
    '   report per-range blocks with the cause you can see (dropped blank verso, inserted',
    '   plate, part-title page, front-matter roman numerals).',
    '3. Confirm the FIRST body page (printed 1) and the LAST numbered body page explicitly.',
    '4. Report any legibility problems: missing glyphs, unrenderable figures, scan artifacts,',
    '   pages whose folio is not printed at all (common on chapter-opening pages).',
    '',
    'Your probes[] must list every page you actually opened. A conclusion without probes is',
    'worthless here -- the whole point is empirical verification.',
  ].join('\n')
}

function reconcilePrompt(toc, off) {
  return [
    HDR,
    '',
    'Two agents independently calibrated this book. Reconcile them into the final pagemap.',
    '',
    '=== TOC / numbering agent ===',
    JSON.stringify(toc, null, 1),
    '',
    '=== offset agent (independent, did not read the TOC) ===',
    JSON.stringify(off, null, 1),
    '',
    'YOUR JOB:',
    '1. CROSS-CHECK. Apply the offset agent\'s function to the TOC agent\'s printed chapter',
    '   starts and OPEN those PDF pages. Does each land on the chapter opening it should?',
    '   This is the real test of the calibration -- report each check.',
    '2. Report every disagreement explicitly. Do not silently prefer one agent. If they',
    '   conflict, open the pages and decide from the evidence, saying which was right.',
    '3. Emit FINAL per-chapter launch args: roman (the chapter number as a string), title,',
    '   pdfStart, pdfEnd (inclusive; the last page of the chapter, not the first page of the',
    '   next), offset (for that chapter -- use the block value if non-uniform), splitAt (a',
    '   PDF page near the chapter midpoint, preferably at a section boundary rather than',
    '   mid-proof), and the section list with PRINTED starts.',
    '   pdfStart/pdfEnd must TILE the body with no gaps and no overlaps between chapters.',
    '4. Write the complete pagemap.md body. Include: an EDITION section; the full TOC table;',
    '   an OFFSET section stating the function and the probe evidence; a NUMBERING section',
    '   with the proving example; a per-chapter table of PDF ranges; and a WARNINGS section',
    '   for legibility issues and structural traps a downstream agent must know.',
    '   State the offset in the form a downstream agent needs: printed = pdf - offset.',
    '',
    'If anything remains genuinely uncertain, put it in warnings[] rather than guessing. A',
    'disclosed uncertainty is cheap; a confident wrong offset corrupts seven chapters.',
  ].join('\n')
}

phase('Calibrate')
log('Calibrating ' + A.title + ' (' + A.pages + ' PDF pages) with two independent agents')

const [toc, off] = await parallel([
  () => agent(tocPrompt(), { label: 'toc+numbering', phase: 'Calibrate', schema: TOC_SCHEMA }),
  () => agent(offsetPrompt(), { label: 'offset-probe', phase: 'Calibrate', schema: OFFSET_SCHEMA }),
])

if (!toc || !off) {
  return { error: 'a calibration agent failed', toc: toc || null, offset: off || null }
}
log('TOC: ' + toc.chapters.length + ' chapters | offset uniform: ' + off.uniform)

phase('Reconcile')
const rec = await agent(reconcilePrompt(toc, off), {
  label: 'reconcile',
  phase: 'Reconcile',
  schema: RECONCILE_SCHEMA,
})

return { toc, offset: off, reconciled: rec }
