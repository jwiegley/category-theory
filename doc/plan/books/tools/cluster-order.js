export const meta = {
  name: 'cluster-order',
  description: 'Decide the internal implementation order of issue clusters that share a new module',
  phases: [
    { title: 'Order', detail: 'one agent per shared module: creator + ordering edges' },
    { title: 'Verify', detail: 'adversarial check of each proposed edge set' },
  ],
}

// args: [{module, issues:[<issue number>, ...]}, ...]
// Defensive: depending on how the caller passes it, `args` can arrive either as
// a real array or as a JSON-encoded string. Accept both -- the string form
// otherwise fails deep in the loop with "batch.map is not a function".
const CLUSTERS = typeof args === 'string' ? JSON.parse(args) : args
const MAX = 1 // honour the session-wide 2-concurrent-subagent cap

const ORDER_SCHEMA = {
  type: 'object',
  required: ['module', 'verdict', 'edges', 'rationale'],
  properties: {
    module: { type: 'string' },
    verdict: {
      type: 'string',
      enum: ['ORDERED', 'SERIALIZE_ONLY', 'DEDUP_NEEDED', 'NOT_A_CONFLICT'],
      description:
        'ORDERED = a real prerequisite order exists, emit edges. SERIALIZE_ONLY = genuine peers, no logical precedence, but they write one file so they must not run concurrently. DEDUP_NEEDED = two issues state the SAME obligation and one should defer to the other. NOT_A_CONFLICT = they do not really touch the same new file (e.g. one only references it).',
    },
    creator: {
      type: ['integer', 'null'],
      description: 'issue number that should CREATE the module (null if none/NOT_A_CONFLICT)',
    },
    edges: {
      type: 'array',
      description: 'blocked-by edges to add: {from} is blocked by {to}. Empty unless ORDERED.',
      items: {
        type: 'object',
        required: ['from', 'to', 'why'],
        properties: {
          from: { type: 'integer' },
          to: { type: 'integer' },
          why: { type: 'string', description: 'the concrete artifact {to} supplies that {from} needs' },
        },
      },
    },
    rationale: { type: 'string' },
    dedup_note: { type: 'string', description: 'for DEDUP_NEEDED: which defers to which and why' },
  },
}

const VERDICT_SCHEMA = {
  type: 'object',
  required: ['module', 'agree', 'problems'],
  properties: {
    module: { type: 'string' },
    agree: { type: 'boolean' },
    problems: { type: 'array', items: { type: 'string' } },
    corrected_edges: {
      type: 'array',
      items: {
        type: 'object',
        required: ['from', 'to', 'why'],
        properties: { from: { type: 'integer' }, to: { type: 'integer' }, why: { type: 'string' } },
      },
    },
  },
}

const REPO = 'jwiegley/category-theory'
const ROOT = '/Users/johnw/src/category-theory/master'

function orderPrompt(c) {
  const list = c.issues.map((i) => '  #' + i).join('\n')
  // titles are fetched by the agent via gh; args carry only issue numbers
  return [
    'You are resolving a PARALLEL-SCHEDULING HAZARD in a catalog of category-theory formalization issues.',
    '',
    'Repo: ' + ROOT + ' (Coq/Rocq library). GitHub repo: ' + REPO + '.',
    '',
    'These ' + c.issues.length + ' issues all propose to create the SAME NEW module file:',
    '',
    '    ' + c.module,
    '',
    list,
    '',
    'They currently have NO dependency path between them, so a scheduler would treat them as',
    'independent and hand them to different agents concurrently — who would then collide while',
    'creating one file. Your job is to decide the correct relationship.',
    '',
    'METHOD (do the reading; do not guess from titles):',
    '1. Read every issue body in full: gh issue view <N> -R ' + REPO + ' --json title,body -q .body',
    '2. For each, extract precisely WHAT ARTIFACT it adds to ' + c.module + ' — the definitions,',
    '   classes, instances or theorems it would introduce. Titles are often misleading; the',
    '   "Work to be done" and "Definition of Done" sections are authoritative.',
    '3. Determine whether some issues genuinely REQUIRE artifacts introduced by another. A real',
    '   prerequisite means: the later issue cannot state or prove its result without the earlier',
    '   one having landed. Shared subject matter alone is NOT a dependency.',
    '4. Check the library itself for what already exists, so you do not invent a prerequisite',
    '   that is already in-tree: grep/read under ' + ROOT + '.',
    '',
    'VERDICTS:',
    '- ORDERED: there is a real prerequisite structure. Emit the minimal edge set (TRANSITIVELY',
    '  REDUCED — do not emit A<-C when A<-B and B<-C already give it). Name the creator.',
    '- SERIALIZE_ONLY: they are genuine peers each adding an independent piece to one file, with',
    '  no logical precedence. Still unsafe to parallelize. Name the creator (whoever introduces',
    '  the file scaffolding) but emit NO ordering edges beyond creator-first.',
    '- DEDUP_NEEDED: two issues state the same mathematical obligation; one should defer.',
    '- NOT_A_CONFLICT: they do not actually both create this file.',
    '',
    'CRITICAL: an edge you invent is worse than a hazard you leave. Only assert a prerequisite',
    'you can justify by naming the specific artifact the blocker supplies. If unsure, prefer',
    'SERIALIZE_ONLY over a speculative ORDERED.',
    '',
    'Do NOT modify any issue or file. Return the structured result only.',
  ].join('\n')
}

function verifyPrompt(r, c) {
  return [
    'Adversarially verify a proposed dependency decision. Default to REFUTING.',
    '',
    'Module: ' + c.module,
    'Issues: ' + c.issues.map((i) => '#' + i).join(', '),
    'Proposed verdict: ' + r.verdict,
    'Proposed creator: ' + r.creator,
    'Proposed edges: ' + JSON.stringify(r.edges),
    'Rationale given: ' + r.rationale,
    '',
    'Check each claim against the ACTUAL issue bodies (gh issue view <N> -R ' + REPO + ') and the',
    'library at ' + ROOT + '. Specifically hunt for:',
    '  - an edge asserting a prerequisite that is NOT real (shared topic mistaken for dependency);',
    '  - a BACKWARDS edge (the blocker actually needs the blocked issue);',
    '  - a prerequisite that is already satisfied by existing in-tree code, making the edge noise;',
    '  - a missed real prerequisite among these issues;',
    '  - an edge that is redundant under transitivity;',
    '  - a DEDUP_NEEDED that is really two distinct obligations, or vice versa.',
    '',
    'Set agree=false if ANY edge is wrong. Put corrected_edges only if you are confident.',
    'Report problems concretely, citing issue numbers and the artifact in question.',
  ].join('\n')
}

phase('Order')
log('Resolving ' + CLUSTERS.length + ' shared-module clusters (concurrency capped at ' + MAX + ')')

const results = []
for (let i = 0; i < CLUSTERS.length; i += MAX) {
  const batch = CLUSTERS.slice(i, i + MAX)
  const got = await parallel(
    batch.map((c) => async () => {
      const r = await agent(orderPrompt(c), {
        label: 'order:' + c.module.split('/').pop(),
        phase: 'Order',
        schema: ORDER_SCHEMA,
      })
      if (!r) return null
      const v = await agent(verifyPrompt(r, c), {
        label: 'verify:' + c.module.split('/').pop(),
        phase: 'Verify',
        schema: VERDICT_SCHEMA,
      })
      return { cluster: c, order: r, verify: v }
    }),
  )
  results.push(...got.filter(Boolean))
  log('cluster progress: ' + results.length + '/' + CLUSTERS.length)
}

const agreed = results.filter((r) => r.verify && r.verify.agree)
const disputed = results.filter((r) => !r.verify || !r.verify.agree)
log('verified-clean clusters: ' + agreed.length + ' | disputed: ' + disputed.length)

return {
  clusters: results.length,
  agreed: agreed.map((r) => ({
    module: r.cluster.module,
    verdict: r.order.verdict,
    creator: r.order.creator,
    edges: r.order.edges,
    rationale: r.order.rationale,
    dedup_note: r.order.dedup_note,
  })),
  disputed: disputed.map((r) => ({
    module: r.cluster.module,
    verdict: r.order ? r.order.verdict : null,
    proposed_edges: r.order ? r.order.edges : [],
    problems: r.verify ? r.verify.problems : ['verifier did not return'],
    corrected_edges: r.verify ? r.verify.corrected_edges : [],
  })),
}
