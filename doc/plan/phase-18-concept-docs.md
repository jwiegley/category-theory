# Phase 18 — Concept documentation coverage (frozen plan)

Invoked 2026-07-16 via /wiggum. User directive: the comonad files (PR #209)
carry in-depth background on purpose and utility; the rest of the library
does not. Build a follow-on PR adding similar coverage for the other
concepts, researched against nLab, Wikipedia, papers, blog posts, talks,
and presentations, "throughout the scope of this library". Workflow-based
execution explicitly requested; ultracode is on.

## Objective (Definition of Done)

- Every cluster in the inventory below is GRADED (A/B/C) and every A/B
  cluster carries a research-verified background block in its canonical
  home file.
- All changes are COMMENT-ONLY. Every touched file recompiles; the full
  build passes at the end; `make todo`-style scans and whitespace scans
  are clean on every touched file.
- Every substantive claim traces to a named primary source (URL cited in
  the block or verified during drafting); untraceable claims are dropped,
  never kept.
- Commits grouped per wave, each fess-audited; branch rebased on its base;
  PR opened at the end (user authorized PR creation in the invocation).

## Deliverable shape

- Branch: `johnw/concept-docs` off `johnw/ct-phase17` (stack tip), so the
  whole library including Phases 5-17 is in scope. The 8 comonad files of
  PR #209 are EXCLUDED (already covered; avoid merge conflicts).
- Each cluster's home file gets ONE new background comment block APPENDED
  AFTER the existing definitional header — the existing header is never
  rewritten (the Env.v two-block precedent). Register: the comonad/it-voice
  precedent — no contractions; thesis-first paragraphs; inline citations;
  no marketing diction; trade-offs stated plainly.
- Exemplars for register and depth: the it-voice comonad files in the
  worktree `scratchpad/comonad-docs-wt/` (Comonad/Core.v, Instance/Coq/
  Comonad/Env.v).

## Hard rails (unchanged from the classical campaign)

- Comment-only diffs; zero behavioural change.
- Banned substrings in comments, case-insensitive (the `make todo` egrep):
  fail, abort, admit, undefined, jww. (Note: "todo"/"fixme" are NOT in the
  Makefile scan, but avoid them anyway.)
- No contractions anywhere in new prose.
- Hom equality is `≈` in prose about morphisms; `=` only for Type-level
  object data.
- Campaign docs (doc/plan/*, doc/wiggum-handoff.md) stay untracked.
- Commit env: LEFTHOOK_EXCLUDE=nix-build,nix-check. Trailer: Fable 5
  co-author + session URL.

## Method (per wave, workflow-executed)

pipeline(clusters, research, draft, verify), then main-loop integration:

1. RESEARCH agent (web access): read the target file's existing header,
   grade A (no background) / B (definitional header only) / C (already
   rich — skip with rationale); for A/B, gather history, purpose, utility
   map, computational reading, in-tree connections; 4-10 sources (nLab,
   Wikipedia, primary papers, textbooks — CWM, Riehl, Awodey, Leinster,
   Fong-Spivak — blog posts — Milewski, Math3ma, Baez, Kmett, Piponi —
   talks — Catsters, Riehl), each with URL + the claim it supports.
   Writes `<cluster>.research.md` to the wave scratch dir.
2. DRAFT agent: reads the brief + the target file + the exemplars;
   produces the comment block honouring register + rails, citing only
   in-file identifiers that exist; writes `<cluster>.block.txt` + returns
   the unique anchor line (last line of the existing header block).
3. VERIFY agent (adversarial, web access): re-fetches cited sources,
   confirms each claim traces; greps identifiers; scans hygiene
   substrings + contractions; fixes or drops; writes
   `<cluster>.verified.txt` + verdict with dropped-claims list.
4. MAIN LOOP: apply each verified block with Edit at its anchor; compile
   touched files; run hygiene scans; commit the wave; dispatch fess audit.

## Cluster inventory (canonical home files)

Wave 1 — Theory core:
category=Theory/Category.v; functor=Theory/Functor.v;
natural-transformation=Theory/Natural/Transformation.v;
isomorphism=Theory/Isomorphism.v; adjunction=Theory/Adjunction.v;
monad=Theory/Monad.v; kan-extension=Theory/Kan/Extension.v;
yoneda=Functor/Hom/Yoneda.v; equivalence=Theory/Equivalence.v;
groupoid=Construction/Groupoid.v

Wave 2 — Universal structures:
limit=Structure/Limit.v (+Cone context); terminal-initial=
Structure/Terminal.v; cartesian=Structure/Cartesian.v;
closed-ccc=Structure/Closed.v; equalizer-coequalizer=
Structure/Equalizer.v; pullback-pushout=Structure/Pullback.v;
universal-arrow=Theory/Universal/Arrow.v; complete=Structure/Complete.v

Wave 3 — Monoidal and algebra:
monoidal=Structure/Monoidal.v; braided-symmetric (locate canonical file);
monoid-object=Structure/Monoid.v; algebra-frobenius=Theory/Algebra.v
(+ Theory/Algebra/Frobenius.v); copydiscard-markov=
Structure/Monoidal/CopyDiscard.v; premonoidal=Structure/Premonoidal.v;
funny=Construction/Funny.v; strictcat/strictness (grade first)

Wave 4 — Constructions:
opposite=Construction/Opposite.v; product-cat=Construction/Product.v;
comma=Construction/Comma.v; slice=Construction/Slice.v;
arrow-cat=Construction/Arrow.v; free=Construction/Free.v;
cayley=Construction/Cayley.v; enriched=Construction/Enriched.v;
day=Construction/Day.v (grade); karoubi=Construction/Karoubi.v (grade)

Wave 5 — Instances and applied:
sets=Instance/Sets.v (setoid rationale); coq=Instance/Coq.v;
cat=Instance/Cat.v; fun=Instance/Fun.v; lambda=Instance/Lambda.v;
finset=Instance/FinSet.v; order-family=Instance/Poset.v (+Proset/Rel/Ens
context); zx=Instance/ZX.v; shape-cats=Instance/Two.v (+One/Zero/
Parallel/Roof context); coq-bridge=Theory/Coq.v

Wave 6 — Recent-phase grade pass (skip C, enrich thin ones):
topos=Structure/Topos.v; bicategory=Theory/Bicategory.v;
double-category=Theory/DoubleCategory.v; lawvere=Theory/Lawvere.v;
multicategory=Theory/Multicategory.v; profunctor=Theory/Profunctor.v;
coend=Structure/Coend.v; falg-recursion=Construction/FAlg.v;
factorization=Structure/Factorization.v; monadicity=
Monad/Monadicity/Beck.v; grothendieck=Construction/Grothendieck.v;
abelian=Structure/Abelian.v; sheaf=Theory/Sheaf.v;
localization=Construction/Localization.v; gaft=Adjunction/GAFT.v

The inventory may gain clusters if integration reveals an uncovered home;
it never loses one without a grade-C rationale recorded in the handoff.

## Commit plan

One commit per wave: docs(Theory)/docs(Structure)/docs(Construction)/
docs(Instance) style, describing the essays added. fess audit per wave
commit. Final: full build + scans, rebase check, PR stacked after the
phase-17 PR.
