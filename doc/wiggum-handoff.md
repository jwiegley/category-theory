# Wiggum handoff — classical completion plan execution

**Untracked working-state file. Do not commit. Re-read in full after any
context compaction, together with the wiggum skill and the frozen plan.**

## Frozen plan (read-only for bar-lowering)
`doc/classical-completion-plan.md`, committed as 4d1c143 on `johnw/ct-phase5`.
13 phases (5–17), 135 files. Coverage matrix in §4; conventions in §2;
execution mechanics in §6. Definition of done per phase = its completion
checklist + the §2 gates (no-holes, Print Assumptions closed, make todo
silent, _CoqProject registered, full make + nix build + nix flake check,
8.19/8.20 portability harvest in a detached worktree).

## User directives for this run
- MODEL (2026-07-09, latest): **Fable 5 is back** — main loop switched via
  /model, and the user set `CLAUDE_CODE_SUBAGENT_MODEL="claude-fable-5"` +
  restarted; probe wf_6480008d-a08 returned `{modelId: claude-fable-5}`.
  Use Fable for main loop AND subagents "until we max allocation". KEY
  ROUTING FACT (confirmed twice, both directions): the env var pin WINS over
  per-agent `model:` overrides and is read only at session startup — changing
  routing always needs a settings.json edit + restart.
- At most **2 concurrent agents** in any workflow (reaffirmed by the user for
  the Fable run — enforce with a counting-semaphore gate). ultracode is ON.
- Implementers are `rocq-pro` agents (now on Fable).
- Phase-7-era history (Opus interlude): Phase 7's 6 remaining files were
  implemented/reviewed/audited with Opus subagents on 2026-07-09; commits
  7c14aea2..f05737da carry the Opus trailer.
- Work until fully done per the plan; if credits/session limit hit, stop
  immediately mid-loop and leave this handoff current for resume.
- PAL consensus: deliberately NOT used for routine phase execution (the plan
  was already multi-agent red-teamed); reserved for genuine impasses.

## Plan errata found during execution (frozen doc — do NOT edit it)
- Phase 5 file 4: "adjunction composition verified absent in-tree" is wrong;
  adj_comp exists (Instance/Adjoints.v:55). Handled: Compose.v documents
  definitional agreement; canonical-home consolidation deferred.
- Phase 6 file 2 (line ~667): the co-Kleisli =>=/=<= notation orientation
  in the plan is TRANSPOSED vs the repo's own >=>/<=< fish convention
  (Monad/Kleisli.v). CoKleisli.v ships the CORRECTED orientation (=>= =
  left operand first); the plan text is the erratum.
- Phase 6 files 9-10 (Store/Traced on Coq, "pointwise =, closed
  assumptions"): UNSATISFIABLE without funext — a Coq-hosted functor's
  fmap_respects field entails functional extensionality (machine-checked:
  coq_store_map_proper_entails_funext, coq_traced_map_proper_entails_funext).
  Witnesses correctly hosted on Sets instead (plan's own risk-note
  fallback), axiom-free. Env stays on Coq. RECORD in the phase-6 commit/PR.

## PUSHED (2026-07-08, user-authorized via /fess)
- PR #195: johnw/ct-phase5 -> master (Phase 5). PR #196: johnw/ct-phase6
  -> johnw/ct-phase5 (Phase 6). Both disclose their deviations in the body
  (Adjunction_Compose vs adj_comp duplication; Store/Traced on Sets).
- fess self-audit run before push: full build green, 7 principal artifacts
  Print-Assumptions-closed, notation orientation behaviorally tested
  (cokl_test.v), funext-entailment lemma confirmed non-vacuous, zero holes.
  Top honest finding: Adjunction_Compose (Adjunction/Compose.v:173)
  duplicates adj_comp (Instance/Adjoints.v:55); proven-equal, consolidation
  is a maintainer call, disclosed in PR #195.

## Repo state
- PR stack (all green CI as of 2026-07-07): #191 johnw/ct-phase1 → master,
  #192 phase2, #193 phase3, #194 phase4. Deep-review fix pass and
  8.19/8.20 portability fixes are landed and pushed.
- Current branch: `johnw/ct-phase5` (created off johnw/ct-phase4 tip
  3f04f34), first commit 4d1c143 = the plan document.
- Library fully built under Rocq 9.1 at the phase-4 tip. `nix develop`
  provides the toolchain; single-file compile also works with
  ROCQPATH/OCAMLPATH from the dev shell (equations + rocq-stdlib
  user-contrib; OCAMLPATH needed for the equations plugin).
- GPG signing: hardware-backed; the agent passphrase cache expires after
  long idle. If commit fails with pinentry cancellation, ask the user to
  unlock (they run: ! echo unlock | gpg --clearsign -o /dev/null).

## Loop per phase (established rails, adapted to MAX=4)
1. Read the phase section of the plan in full.
2. Implementation workflow (single Workflow call, 4-gated): DAG-gated
   rocq-pro implementers (per-file, deps awaited, `hard` files at
   effort max) → clean-rebuild+scan+Print Assumptions verifier →
   per-file coq-reviewer + max-effort fidelity reviewer vs the phase
   checklist → 3-vote refutation → single fixer → closure loop (≤2
   rounds, completion agents for missing checklist items) → final verify.
   Implementer rules: no Admitted/Axiom/etc.; MISSING-item escalation per
   plan §6; comments avoid make-todo words; portability: no 9.x-only
   stdlib names (plan §2 gate).
3. Integrate (main loop, not agents): _CoqProject entries, CLAUDE.md
   Key Files if the phase says so, full `nix develop -c make`,
   `make todo` campaign-silence check, 8.19/8.20 keep-going harvest in a
   detached worktree (plan §2.3), `nix build && nix flake check`.
4. Commit series: one commit per file with its _CoqProject line
   (perl-ins incremental technique, scripts in scratchpad from P1-P4 are
   the template), docs commit last. LEFTHOOK_EXCLUDE=nix-build,nix-check.
5. fess audit of the phase's commits via a fess-auditor subagent;
   verify findings before acting; fold fixes in.
6. Check doc/observations/ (non-hidden .md) → run partner-cleanup
   equivalent (triage agent), commit cleanup.
7. Update this handoff (phase status, attempt counters), then next phase.
   Branch for phase N is johnw/ct-phaseN off the previous.

## Phase status
- Phase 5: **DONE** (2026-07-08). 10 files + docs on johnw/ct-phase5,
  rebased onto master@f2c8c9a (PRs #191-194 are MERGED; master carries
  extra partner-review work). All gates green (make, 8.19+8.20 harvests
  clean, nix build + flake check with honest exit codes), fess audit PASS
  (pentagon/triangle landed — no staging needed), observations drained
  (3 processed: 1 pre-rebase, 2 post-rebase). Branch tip 9cc53ce, 16
  commits over master. NOT pushed (human-gated).
- Phase 6 (comonads + monad resolutions): **DONE** (2026-07-08), 12 commits
  on johnw/ct-phase6 over johnw/ct-phase5. Moore.v repair bundled with its
  Adjunction file (same-commit rule). All 10 checklist rows present, Print
  Assumptions closed for all 6 principal artifacts (3 Coq comonads zero
  funext), make todo silent, full 9.1 make + 8.19 + 8.20 harvests + nix
  build + flake check ALL green (honest exit codes). fess audit was
  performed IN-LOOP by the Opus main loop (see constraint below), passed;
  it caught one stale CoKleisli header ref (fixed, commit 2bc12d8). No
  observations pending. Tip 2bc12d8. NOT pushed.
- Phase 7 (F-(co)algebras/Lambek/Adamek): **10/10 FILES DONE + COMMITTED**
  (2026-07-09) on johnw/ct-phase7 (tip 660c8c28, 11 commits over ct-phase6:
  Omega, FAlg, FCoalg, Chain [prior 4], then Lambek, Recursion, Adamek,
  Adamek/Corollaries, Coq/Lists, Sets/Streams, docs[CLAUDE]). The remaining 6
  were implemented by workflow wf_32afc8af-342 (MAX=2 rocq-pro/Opus), then
  independently verified in the main loop: clean-recompile all 6, hole scan
  clean, make-todo words clean, trailing-ws clean, Print Assumptions CLOSED
  for lambek/lambek_final/cata/cata_unique/cata_fusion/ana/ana_unique/
  ana_fusion/adamek/list_initial/Stream_final/adamek_cocomplete (all 12),
  adversarial coq-reviewer pass wf_6c5f8144-bd1 = 3× CLEAN (no findings),
  full 9.1 make green, _CoqProject reconstructed IDENTICAL to the
  fully-registered set, CLAUDE.md indexed. Adamek took the sanctioned
  AdamekData fallback (bridge withheld, ledger 17, documented in header +
  commit); the C@{cobj Set Set} universe constraint is INTRINSIC (Chain pins
  Omega hom/prop to Set, Limit unifies shape+target — verified empirically,
  not a weakening). PORTABILITY HARVEST DONE: 8.19 + 8.20 keep-going builds
  both rc=0, all 10 Phase-7 .vo present under both; it caught ONE real bug —
  Instance/Omega.v's le_t_trans_* lemmas had an over-specified @{u} binder
  that breaks on 8.19/8.20 ("unbound universes"), fixed by inferred binders
  (commit fix(Omega), tip 66555f47), re-verified on all three toolchains.
  GATES ALL GREEN: nix build .#category-theory_9_1 rc=0, nix flake check
  (admitted-check + format-check) rc=0 [on tip 66555f47; a final re-gate on
  f05737da is running after two comment-only docs commits]. fess audit
  (fess-auditor subagent, Opus) = PASS: independently re-verified all 12
  Print-Assumptions-closed, AdamekData non-vacuous + adamek a real initial
  object, universe pin intrinsic (empirical probe), Streams corecursion
  sound/non-vacuous, Lists funext-free, statement orientations correct, Omega
  fix meaning-preserving; no stubs/vacuity/scope-creep. Two LOW doc nuances
  it raised were fixed (commit f05737da: Adamek/Corollaries withheld-bridge +
  NatF disclosures sharpened). **Phase 7 is DONE** (tip f05737da, 13 commits
  over ct-phase6). PR is human-gated (stacks on johnw/ct-phase6). NOT pushed.
  NEXT: phase 8 (factorization/regular/Karoubi) per doc/plan/phase-08-*.md —
  branch johnw/ct-phase8 off f05737da; recommended campaign order 8→7[done]→
  11→9→10→12→13→14→15→16→17 (00-INDEX). Subagents now run on Opus (MAX=2).
  WORKING PATTERNS established this session (reuse them for phases 8-17):
  * Sigma-carrier categories (FAlg): bundle a hom CLASS with a named
    commutes-projection (mirror Monad/Algebra.v TAlgebraHom + Moore.v). Do
    NOT hand-prove every obligation — the ambient tactic solves homset
    Equivalence / id / compose_respects / the 4 laws; write exactly ONE
    manual Next Obligation (the compose-commutes square:
    `rewrite fmap_comp; rewrite comp_assoc; rewrite <- falg_commutes;
     rewrite <- !comp_assoc; rewrite <- falg_commutes; reflexivity`).
  * Duality one-liners (FCoalg := (FAlg (F^op))^op); use backtick `(F : C ⟶ C)
    on EVERY lemma binder (plain parens leave C unbound).
  * Omega pitfalls: le_t_n's constructor return type is `le_t n` (parameter
    auto-applied — NOT `le_t n n`); its Category obligations close with
    `Solve All Obligations with (simpl; intros; try subst; rewrite
     ?le_t_trans_id_l,?le_t_trans_id_r,?le_t_trans_assoc; try reflexivity)`.
  * Initial is notation for Terminal of the op; accessors initial_obj/zero/
    zero_unique in Structure/Initial.v; build FAlg's Initial instances with
    terminal_obj/one fields.
  * 2026-07-09: implementation workflow wf_32afc8af-342 LAUNCHED (MAX=2,
    rocq-pro/Opus) for the 6 remaining files (Lambek, Recursion, Adamek,
    Lists, Streams in wave 1; Corollaries after Adamek). Fast compile
    wrapper for agents: scratchpad/coqw.sh (pinned coqc/coqtop env, adds
    -R . Category). KEY DESIGN DECISION for Adamek: the abstract
    PreservesColimit class does NOT expose that its preserved-colimit cocone
    legs are the image legs fmap[F](inj n) (colimit cocones at a shared apex
    differ by a free automorphism), yet initiality genuinely needs that
    agreement — so Adamek is delivered over the sanctioned `AdamekData`
    record (colimit witness + leg-agreement), `adamek : AdamekData → Initial
    (FAlg F)` fully proved; the PreservesColimit→AdamekData bridge is
    WITHHELD (ledger 17, not stubbed). After the workflow: verify each file
    (recompile, Print Assumptions, make todo), adversarial coq-reviewer
    pass, then integrate (_CoqProject, CLAUDE.md), full make, 8.19/8.20
    harvest, nix gates, per-file commits, fess audit.
- Phase 8 (factorization/regular/Karoubi): **12/12 FILES DONE + COMMITTED**
  (2026-07-09) on johnw/ct-phase8, 13 commits over f05737da (tip 73a7f42a =
  docs(CLAUDE); files 7e1e9f25..f99858a6 in dep order: Classes, Orthogonality,
  Coequalizer, Stability, Factorization, StrongEpi, Regular,
  Regular/Factorization, Sets/Image, Karoubi, Karoubi/Universal,
  Sets/Karoubi). Implementation wf_4d72dd61-6ab (12/12 Fable rocq-pro,
  MAX=2, ZERO fallbacks — even Karoubi_Extend_unique and
  image_comparison_monic landed in full). Main-loop verification: scratch
  recompile 12/12, hole/todo/ws scans clean, 41/41 Print Assumptions CLOSED
  (incl. Regular_OFS, Karoubi_Extend, Sets_Cauchy — the checklist's named
  three). Adversarial review wf_3cb66d28-ad8: regular-stack CLEAN; the two
  registration findings were the pending _CoqProject step (done, +12 lines,
  reconstruction diff IDENTICAL); ONE real finding fixed pre-commit:
  Universal.v header claimed the Cauchy biconditional ("precisely when") but
  only the forward direction is proven — reworded to disclose forward-only.
  Full 9.1 make green. PLAN ERRATA for the PR body: (1) pasting lemma
  transposed in the work order (TRUE law implemented: right square a
  pullback ⇒ outer ⟺ left; unpaste carries the left square's commutativity
  as an explicit hypothesis); (2) E/M determination delivered in honest
  hypothesis-form (iso-closure premise; strict form not derivable from the
  minimal OFS class). GATES at tip 73a7f42a: 8.19 + 8.20 harvests CLEAN
  (0 errors, 12/12 .vo each — no shims needed), nix build + flake check
  rc=0. fess audit (Fable fess-auditor) = substantially clean, 30/30
  assumptions re-verified, double-cover proof and Karoubi_Extend_unique
  confirmed genuine, NO fallback smuggling; findings fixed: (1) MODERATE —
  Orthogonality.v pointed to cobase-change stability in Stability.v that
  had been silently dropped → RESOLVED by LANDING the lemma
  (ortho_left_cobase_change, commit ad30c5b8, assumptions closed) and
  correcting the pointer; (2) MINOR — the correct Phase-8 commit range is
  f05737da..HEAD (13 feature/docs commits + ad30c5b8 = 14). Final-tip
  re-gates (8.19/8.20 harvests + nix build/flake check at ad30c5b8) run
  after the fix commit. Third PLAN-ERRATUM for the PR body: the work
  order's "cobase change stubs deferred to file 4" was initially dropped
  by the implementers; now delivered in file 4 as promised. PR is
  human-gated (stacks on johnw/ct-phase7).
  **PHASE 8 IS DONE** (2026-07-09): final-tip re-gates at ad30c5b8 all
  green — 8.19 + 8.20 harvests 0 errors with both edited .vo present, nix
  build rc=0, nix flake check rc=0.
- Phase 11 (additive structure): **IN PROGRESS** (2026-07-09). Branch
  johnw/ct-phase11 created off ad30c5b8 (phase-8 tip). Implementation
  workflow wf_3aba0553-383 LAUNCHED: 10 files, MAX=2 Fable rocq-pro,
  promise-DAG (zero+fork+cmon heads; biprod,preadd←zero;
  kernel←zero,fork; semiadd,additive←biprod,preadd;
  abelian←additive,kernel; cmonbi←cmon,semiadd). Verified in-tree premises:
  NO existing ZeroObject/Biproduct/Preadditive/Kernel/Abelian/CMon ('Mon'
  is taken by Theory/Algebra/Monoid/Hom.v:83 — CMon names chosen). Specs
  embed: complete Freyd/Borceux image_mediator_epic chase for Abelian
  (kernel-of-cokernel factorization; j-split-epi conclusion), the
  can-comparison convolution roadmap for bicartesian_preadditive (naturality
  conjugation discipline; assoc flagged as the hard law), the Phase-8
  payoff route Epic→IsCokernel→RegularEpi→StrongEpi→⫫ for Abelian_OFS,
  and the CMon direct-product biproduct with the h'(a,b) monoid-hom
  uniqueness trick. Semiadditive.v also adds the pointer sentence to
  Structure/Bicartesian.v's header (same-commit rule at commit time).
  Sanctioned fallbacks: AbelianImageData (ledger 17) only.
  STATUS UPDATE (2026-07-09, later): **10/10 FILES DONE + COMMITTED**, 11
  commits on johnw/ct-phase11 (tip 10ede89e = docs; files d129851e..eb874172
  in dep order). ZERO fallbacks — image_mediator_epic proven IN FULL (no
  AbelianImageData) and bicartesian_preadditive's assoc/comm landed via an
  Eckmann-Hilton argument between the coproduct- and product-flavoured
  convolutions (interchange = Bicartesian.v's fork_merge) — BETTER than the
  naturality-conjugation roadmap; the Bicartesian.v pointer edit rode the
  Semiadditive commit. Main-loop verification: scratch recompile 11/11
  (incl. edited Bicartesian.v), scans clean, 43/43 Print Assumptions CLOSED.
  Adversarial review wf_a418b672-68c: abelian-stack CLEAN; semiadd-stack
  only the pending registration; ONE REAL major finding FIXED pre-commit:
  the CMon zero-object chain was silently universe-minimized to Set
  (CMon_trivial's flexible equiv universe) pinning CMon_Zero/CMon_Biproducts/
  CMon_padd_biproduct to CMonObject@{Set Set Set} — fixed with explicit
  binders (CMon_trivial@{o} : CMonObject@{o o o}, @{u o} annotations on the
  one/zero_hom chain); verified post-fix: CMon_Zero@{u u0} with NO Set pin,
  and the reviewer's higher-universe Check now typechecks (lesson 12 strikes
  again — universe annotations are load-bearing). Full make green after
  registration (+10, alphabetical, Abelian/Additive order fixed in the docs
  commit). **PHASE 11 IS DONE** (2026-07-09): gates at 10ede89e all green
  (8.19/8.20 harvests 0 errors 10/10 .vo, nix build + flake check rc=0);
  fess audit PASS (all 7 claims confirmed, no High/Medium; its Low finding
  — Abelian.v's "loses no generality" prose — RESOLVED by proving it:
  kernel_of_any_cokernel + dual + chosen-instance corollaries, commit
  7d3b7028 [amended once to fix a trailer typo], all 4 closed); final
  re-gates at 7d3b7028 ALL GREEN (8.19/8.20 zero errors with the two
  re-touched .vo present, nix build rc=0, flake check rc=0). 12 commits
  total on johnw/ct-phase11. PR human-gated (stacks on johnw/ct-phase8).
  fess PR-body note: commit 66d57b98's "Consumed by Structure/Kernel.v"
  refers to IsEqualizer (HasEqualizers itself is forward-looking API for
  Phase 14) — phrase precisely in the PR.
- Phase 9 (monadicity): **8/8 FILES DONE + COMMITTED** (2026-07-10, after
  the session-limit reset). Relaunched script as wf_b055a29c-9a1 — 8/8
  Fable agents, ZERO fallbacks: crude_monadicity fully proven (transparent
  Crude_Inverse); Beck.v landed the FULL assembly (quarantine unused) and
  DROPPED the ReflectsIsos hypothesis by deriving conservativity from
  creation (creates_split_reflects_isos); Lifting.v delivered the full
  Dubuc adjoint-triangle theorem (more than sanctioned). Main-loop
  verification: scratch recompile 8/8, scans clean, 32/32 Print
  Assumptions CLOSED (incl. crude_monadicity, beck_monadicity,
  adjoint_lifting — the checklist's three). Adversarial review
  wf_c6f0aad9-80c: two stacks CLEAN; monadicity-core two findings BOTH
  addressed — (minor) monadic_creates covers EM_Forget only, transport
  along an equivalence over D withheld + disclosed in-file (Beck.v header;
  plan edge, ledger 17 — PR-BODY ITEM); (nit) Crude.v header
  interconvertibility overclaim REWORDED pre-commit (now notes the missing
  U◯APair ≡ APair(fmap U) identification). PR-BODY DEVIATION also:
  Comparison.v's transparent Adjunction_Induced_Monad rebuild (sealed
  Adjunction_Monad; Comonad/Duality.v precedent, disclosed in header).
  9 commits on johnw/ct-phase9 (tip 3ac0562f = docs; two mid-series amends
  repaired a mangled commit message and a missing registration line —
  final commits well-formed, _CoqProject reconstruction IDENTICAL). Full
  make green. **PHASE 9 IS DONE** (2026-07-10): gates at 3ac0562f ALL
  GREEN (8.19 + 8.20 harvests 0 errors 8/8 .vo each, nix build rc=0,
  flake check rc=0); fess audit PASS (18/18 assumptions re-verified, both
  equivalence records genuinely non-degenerate with proven conjugation
  coherence, dropped-ReflectsIsos derivation sound, commit hygiene incl.
  both amends verified). fess PR-BODY NOTES (no code changes): (1) LOW —
  no in-tree consumer fires crude/beck/lifting on a concrete instance
  beyond identity_monadic (which bypasses the coequalizer machinery,
  disclosed in-file); follow-up idea: instantiate beck_monadicity on a
  concrete adjunction. (2) nit — Lifting.v:79-84 square-form paragraph is
  a derivation sketch, not a delivered theorem; say so in the PR. (3) nit
  — commit f90c207c's message reads as if ReflectsIsos feeds the counit
  cell; the file header (Crude.v:78-90) is precise (unit cell only). PR
  human-gated (stacks on johnw/ct-phase11). NEXT: Phase 10
  (displayed/fibrations/Grothendieck; needs 5 + 8 — in-tree).
- Phase 10 (displayed/fibrations/Grothendieck): **COMPLETE (10/10),
  reviewed SOUND, all gates green, fess HONEST** (2026-07-10; finished on
  Opus 4.8 after the Fable wrap-up/handoff). Branch johnw/ct-phase10 off
  3ac0562f (phase-9 tip); tip a1e15509 = 12 commits (8 Fable
  7b0e6c85..d5867ffb + 4 Opus): RoundTrip.v (a9769ed0), Strict.v
  (5fe68b60), docs(Displayed) header fixes (ba5291ec, two review LOW
  findings), docs(CLAUDE) index (a1e15509). Each new file paired with its
  _CoqProject line; reconstruction IDENTICAL to _CoqProject.p10final.
  RoundTrip.v landed the FULL EquivalenceOfCategories (ledger-17 staged
  fallback NOT needed); Strict.v the UIP/Hedberg constructors + constant
  example. Print Assumptions CLOSED for every checklist artifact
  (Grothendieck, fiber_grothendieck_equiv, RoundTrip_Comparison +
  RoundTrip_Equivalence, IndexedCat_of_StrictFunctor, hedberg,
  Grothendieck_Constant_iso, codomain_cleaving[_pullbacks]).
  ### PHASE 10 CLOSED ON OPUS — all rails run (2026-07-10)
  - Impl: 2 rocq-pro agents (Strict, RoundTrip) on Opus, MAX=2.
  - Adversarial review: 4 coq-reviewer passes over all 10 files — ALL
    SOUND. Displayed interchange-field vacuity REFUTED (2-cocycle
    countermodel confirmed in Coq; minus-2-fields scratch record cannot
    close interchange); IndexedCat orientations correct; Grothendieck
    law-discharge traced to idx_cocycle; MANDATED Print Universes PASSED
    (Total/Grothendieck at the join, one notch up, no Set pinning); Strict
    UIP load-bearing + Hedberg axiom-free; RoundTrip full equivalence
    non-vacuous (a concrete ClovenFibration instance yields a closed
    equivalence). Two doc LOW findings folded (ba5291ec).
  - Gates (final tip a1e15509): 9.1 make EXIT 0; 8.19 + 8.20 harvests
    EXIT 0; nix flake check EXIT 0 (hermetic 9.1 build); nix build
    .#category-theory_9_1 EXIT 0.
  - fess audit: VERDICT HONEST — zero holes/axioms/overclaims/scope-drift;
    every disclosed departure genuinely in-source; numstat N/0.
  - PR: NOT pushed (human-gated; stacks on johnw/ct-phase9).
  ### PHASE-10 DEPARTURES (for the PR body)
  - RoundTrip.v: input is a SplitCleaving of P^op (variance — IndexedCat
    is covariant, matching the split opfibration Grothendieck produces);
    the split laws are provably INERT (only the underlying ClovenFibration
    is consumed — a strengthening), so section-generalized cloven-only
    RT_* forms are exported alongside the split-typed public RoundTrip_*
    (which match the checklist signature). Disclosed in header + commit +
    CLAUDE.md; three evaluators confirmed sound & disclosed.
  - Strict.v: the UIP branch IndexedCat_of_StrictFunctor is proven and
    load-bearing but not instantiated on a concrete decidable fibre (only
    Constant_IndexedCat is a concrete Grothendieck); disclosed in
    Indexed.v header.
  ### PHASE-10 PLAN ERRATA discovered (for the PR body)
  - The plan's Displayed skeleton is INSUFFICIENT: the dcomp/dtransport
    interchange is underivable from its fields (2-cocycle countermodel
    sketched in Theory/Displayed.v's header); dtransport_comp_l/r were
    added as class fields under the work order's sanctioned strengthening.
  - Consequently IndexedCat needed compositor naturality in the base
    arguments, DERIVED in Construction/Grothendieck.v from the coherence
    pack (helper lemmas idx_comp_resp_l_from, idx_cocycle_from) — the
    plan's record needed no change.
  - Grothendieck.v's tookFallback flag = the sanctioned lemma-reorder
    (Risks (c)), NOT a scope reduction; all laws fully proven.
  ### SWITCHOVER PROCEDURE (Fable → Opus)
  - settings.json: CLAUDE_CODE_SUBAGENT_MODEL="claude-opus-4-8"; restart
    Claude (env read at startup ONLY; per-agent model overrides are
    IGNORED — confirmed both directions this campaign); /model
    claude-opus-4-8 for the main loop.
  - Commit trailer becomes the Opus one (see phase-7 commits 7c14aea2..
    f05737da for the exact form) with the NEW session's URL.
  - Concurrency: MAX=2 agents (standing user directive). Implementers:
    rocq-pro. The pinned compile wrapper (works regardless of model):
    /private/tmp/claude-501/-Users-johnw-src-category-theory-master/
    77a4ac3a-916e-4640-a203-4dd3bec49591/scratchpad/coqw.sh
    (coqw.sh coqc <f.v> from repo root; survives restarts, but /private/
    tmp is cleared on REBOOT — if absent, re-derive from 'nix develop -c'
    env per 00-INDEX toolchain notes).
  ### CAMPAIGN STATE AFTER PHASE 10
  Remaining phases per 00-INDEX order: 12 → 13 → 14 → 15 → 16 → 17
  (all work orders in doc/plan/phase-NN-*.md; each self-contained).
  Completed + fully gated: 7 (johnw/ct-phase7), 8 (ct-phase8),
  11 (ct-phase11), 9 (ct-phase9), 10 (ct-phase10, tip a1e15509); all
  stacked, all unpushed (pushes human-gated). Phase 5 (ct-phase5, PR #195)
  and 6 (ct-phase6, PR #196) pushed earlier. NEXT: Phase 12 (coends /
  profunctors / Day convolution / Drinfeld centre / star-autonomous;
  12 files; in-tree deps only — branch off master/latest, NOT stacked on
  7-11).
- Phase 12 (coends / profunctors / Day / Drinfeld / star-autonomous):
  **12/12 FILES DONE + COMMITTED, reviewed SOUND** (2026-07-10, on Opus 4.8
  main loop + Opus rocq-pro subagents). Branch johnw/ct-phase12 off
  a1e15509 (phase-10 tip); 8 commits fa31f5f6..1185d315: C1 Coend infra
  (Structure/Coend.v + Instance/Sets/{End,Coend}.v), C2 Yoneda+Fubini
  (Theory/Coend/{Yoneda,Fubini}.v), C3 Profunctors (Theory/Profunctor{,/
  Adjunction}.v + Construction/Profunctor/{Compose,Laws}.v), C4 Day
  (Construction/Day.v), C5 Drinfeld (Structure/Monoidal/Drinfeld.v), C6
  StarAutonomous (Structure/Monoidal/StarAutonomous.v), C7 docs(CLAUDE),
  C8 (1185d315) in-source SCOPE notes for Fubini (Sets-scoped; ledger 6)
  and Day (Day_Monoidal deferral; ledger 5) — comment-only, closes fess.
  Each feature file paired with its _CoqProject line (incremental
  re-add; final set = 432 entries). Main-loop verification: all 12
  clean-recompiled, hole/todo/ws/funext scans clean, Print Assumptions
  CLOSED for every principal artifact; full `nix develop -c make`
  force-clean-rebuild of all 12 EXIT 0.
  ### KEY DEVIATION — file 12 base RETARGET (main-session, machine-checked)
  The plan named `ClosedMonoidal` as the "symmetric monoidal closed" base,
  but the in-tree ClosedMonoidal BUNDLES CartesianMonoidal (Closed.v:47);
  over a cartesian closed base a dualizing object forces a preorder
  (Joyal), so StarAutonomous would be VACUOUS in every nondegenerate model
  (excludes Rel/FdVect/coherence spaces). FIX: introduced a genuine general
  base `SymMonClosed` IN-FILE = ClosedMonoidal verbatim with the cartesian
  field replaced by SymmetricMonoidal; dual/StarAutonomous transplant
  unchanged. STRENGTHENING, not a weakening; realizes the plan's intent.
  Verified at term level (reviewer): SymMonClosed genuinely NON-cartesian,
  ⨂ resolves to the abstract C tensor (Set Printing All), Remove Hints
  Sets_Product_Monoidal inert. Committed in C6 with full rationale.
  ### OTHER DEVIATIONS / LEDGER (for the PR body)
  - Repr_right retyped `(U:D⟶C):C⇸D` fibre C(c,U d) — plan's `D⇸C` was
    ill-typed; matches hom-adjunction. (C3)
  - Day_Monoidal bundling -> ledger 5 (associator ISO still delivered).
  - abstract Fubini -> ledger 6 (Sets-scoped coend_fubini delivered).
  - StarAutonomous par / linear-distributivity / canonicity coherence ->
    ledger 4; header PRECISION note discloses the three fields are
    necessary-but-not-sufficient (star_double_dual is an arbitrary nat-iso,
    not canonical-δ invertibility).
  - NO Bicategory class for profunctor comp (ledger 14, deferred to P13);
    unit/associator delivered as isos.
  - Drinfeld_Braided FULL — ledger-7 fallback NOT taken (both hexagons).
  ### ADVERSARIAL REVIEW — 2 coq-reviewers (Opus), ALL 12 SOUND, ZERO
  soundness/axiom defects. Reviewer B (6-10,12): Day associator both
  round-trips genuinely proven, representable_adjunction both dirs
  non-trivial, prof_compose really via coend; file-12 SA-1[MAJOR]/SA-2/SA-3
  = faithfulness/precision ONLY, all plan-conformant ledger-4, addressed by
  PRECISION note (no tightening). Reviewer A (1-5,11): coend UMP/wedge
  genuine, Sets/Coend quotients by EXACTLY dinaturality, Fubini exchange
  correct, Drinfeld BOTH hexagons; 2 NITs (Drinfeld Program auto-names;
  yoneda_reduction raw carrier) ACCEPTED as-is (latent/cosmetic, changing
  risks breaking a verified proof).
  ### GATES ALL GREEN (tip dd032197, 2026-07-10): full 9.1 make EXIT 0
  (force-clean rebuild of all 12); nix build .#category-theory_8_19 OK +
  .#category-theory_8_20 OK (portability — no shims needed, no version
  syntax issues); nix flake check OK (hermetic 9.1 build + admitted-check
  + format-check all pass). Re-gate at disclosure tip 1185d315
  (comment-only C8) ALL GREEN (2026-07-10): 9.1 make EXIT 0; nix build
  .#category-theory_9_1 + .#default exit 0; .#category-theory_8_19 OK +
  .#category-theory_8_20 OK (BOTH fresh rebuilds — new derivation hashes,
  genuine portability re-gate, not cache hits); nix flake check OK
  (admitted-check + hermetic 9.1 build + format-check).
  ### fess HONESTY AUDIT — VERDICT: HONEST (fess-auditor, Opus, 2026-07-10).
  All 7 load-bearing claims independently confirmed with evidence: no holes
  / 19/19 principal artifacts "Closed under the global context"; no
  make-todo words, no trailing ws; ≈ not =, funext-free; the file-12
  SymMonClosed retarget is a GENUINE STRENGTHENING (non-cartesian; ⨂ =
  abstract @Monoidal.tensor C under Set Printing All; non-vacuous;
  accurately narrated — fess flagged mild OVER-disclosure, a plus); all
  deviations disclosed & accurate; no vacuity/overclaim; all 12 recompile
  EXIT 0 clean tree. 4 findings, ALL LOW/INFO: (1) Fubini lacked an in-file
  scope note — FIXED in C8; (2) Day deferral wording didn't name
  Day_Monoidal/ledger 5 — FIXED in C8; (3) commit e49d8c1c's
  "proof-irrelevant" shorthand is loose-not-wrong (the Drinfeld intertwiner
  is Type-valued, irrelevance imposed by carrier-only hom-equality; header
  Drinfeld.v is precise) — LEFT, amending would rewrite SHAs; note for PR
  body; (4) lu_iso/ru_iso top-level name collision between Day.v and
  Profunctor/Laws.v — harmless (module-qualified, last-import-wins), LEFT;
  note for PR body / qualify at the first Phase-13 file importing both.
  PR human-gated (stacks on johnw/ct-phase10). Campaign docs (doc/plan/,
  this handoff) stay UNTRACKED per convention.
  ### NEXT: Phase 13 (bicategory mates) per doc/plan/phase-13-*.md — will
  need the Bicategory class deferred here (ledger 14). DAG/scheduler notes
  for this phase: scratchpad/phase12-dag.md (durable).
- Phase 13 (bicategory upgrade / Cat as a bicategory / mates):
  **9/9 FILES DONE + COMMITTED, reviewed SOUND** (2026-07-11, Opus 4.8 main
  loop + Opus rocq-pro subagents, MAX=2). Branch johnw/ct-phase13 off
  1185d315 (phase-12 tip); 9 commits eacede61..bdc02d60: C1 (eacede61)
  Bicategory class refactor IN PLACE + Cat instance (Theory/Bicategory.v +
  Instance/Cat/Bicategory.v), C2 Pseudofunctor, C3 Lax, C4 Modification,
  C5 Adjunction, C6 Mates, C7 OneObject, C8 (5f23265c) Instance/Cat/
  Bicategory/Adjunction.v (Cat adjunction+mates unfolding), C9 (bdc02d60)
  docs(CLAUDE). Each feature file paired with its _CoqProject line
  (incremental re-add; final set = 440 entries; positions 155-156 +
  371-377, reconstruction matches the fully-registered layout). Ledger 14
  (the Bicategory class deferred from Phase 12) is now DISCHARGED.
  ### DELIVERED BEYOND THE MINIMUM
  - Bicategory class upgraded from the 2018 data-only stub to a full weak
    2-category (hcomp2 Godement product, unitors+associator as 2-isos with
    to-naturality, triangle+pentagon) mirroring Structure/Monoidal.v under
    delooping; Build_Bicategory' smart constructor. Audit-first: no code
    consumers of the old stub, so the in-place refactor is safe.
  - adjoint_unique (uniqueness of adjoints up to invertible 2-cell) and the
    general Kelly unit coincidence λ_I≈ρ_I proven from pentagon+triangle.
  - Cat_mate_unfold: the abstract bicategorical mate = the Kelly-Street
    formula, so mates are usable by ordinary-category files.
  ### PHASE-13 DEPARTURES / LEDGER (for the PR body)
  - File 1 unitor/associator NATURALITY delivered to-direction only; the
    from-direction is derivable AND is derived/used (Adjunction.v:233-236,
    hunit_left_from_natural via iso_conj_from). The class is thus LEANER
    than Structure/Monoidal.v, which states BOTH to_ and from_ naturality
    (fess LOW-2 sharpened my earlier "mirrors Monoidal.v" paraphrase) — a
    minimal-but-complete field list, NOT a weakening (the isos supply the
    other direction). CLAUDE.md says "to-direction naturality" precisely.
  - Files 3-4 (Lax/Oplax/Pseudonatural/Modification) are full-strength
    classes per Johnson-Yau Def 4.2.1, inhabited SO FAR ONLY on
    Trivial_Bicategory (Lax.v:217/225/231, Modification.v:200-206); their
    only general consumer is LaxTransformation_Category (object-trivial).
    They are NOT consumed by the Cat instance (fess LOW-1 corrected an
    earlier misstatement of mine) — a genuinely non-trivial witness (a
    lax/pseudonatural transformation between real pseudofunctors) is future
    work. The trivial witness is candidly disclosed in-source (Lax.v:159-
    169: it avoids needing the Kelly λ_I=ρ_I coincidence an arbitrary-
    pseudofunctor identity would require). NOT a named-deliverable gap; the
    classes themselves are complete.
  - File 7 uses the raw Build_Bicategory (not Build_Bicategory') so that
    bicat C D ≡ [C,D] holds definitionally via record-eta (perf/defeq
    note in the file header); reconciles Instance/Fun.v's REVERSED unitor
    names (hunit_left:=nat_ρ, hunit_right:=nat_λ, hassoc:=iso_sym nat_α).
  - Cat pentagon/triangle proven COMPONENTWISE in [C,D] (cat + fmap_comp).
  - Mates FUNCTORIALITY under pasting = ledger 10 (out of scope); the
    bijection mate_iso + both round-trips ARE delivered.
  - Naming: file 8's precomposition hom-adjunction is the ⌊−⌋ transpose
    (reflexivity); postcomp is NOT ⌈−⌉ (it whiskers by the counit) — noted
    so a future reader does not expect symmetry.
  ### ADVERSARIAL REVIEW — coq-reviewer (Opus): reviewer1 over the 8
  non-file-8 files = NO defects; file-8 self-review = SOUND. All 9
  independently re-verified in the main loop: force-clean recompile of all
  9 .vo + full `nix develop -c make` EXIT 0; per-file hygiene scan
  holes=0/todo=0/ws=0 (≈ used 140×, no = on homs); PA battery on 8 headline
  artifacts (Cat_Bicategory, Compose_Pseudofunctor, LaxTransformation_
  Category, adjoint_unique, mate_iso, Monoidal_OneObject_Bicategory,
  Cat_BicatAdjunction_iff, Cat_mate_unfold) ALL "Closed under the global
  context".
  ### GATES ALL GREEN (2026-07-11, committed HEAD bdc02d60, nixgate13.sh):
  hermetic nix build .#category-theory_9_1 OK + _9_0 OK + _8_20 OK + _8_19
  OK (all four supported toolchains, fresh from-scratch derivations — real
  portability, no shims needed, no version-syntax issues); nix flake check
  OK (admitted-check + hermetic 9.1 build + format-check). 9.1 also
  confirmed locally (nix develop -c make EXIT 0). ~17 min total.
  ### fess HONESTY AUDIT — VERDICT: HONEST (fess-auditor, Opus, 2026-07-11,
  independent re-verification on Rocq 9.1.1). No holes, no axioms (20/20
  headline artifacts "Closed under the global context" — transitively
  axiom-free cones), no vacuity, correct ≈ discipline, clean scope
  (numstat = 9 files + CLAUDE.md + _CoqProject only; doc/ untracked). All 8
  disclosed departures confirmed genuine, accurate, NON-weakening; both
  Cat_BicatAdjunction_iff directions non-trivial; Cat_mate_unfold a real
  Kelly-Street ≈ (not a tautology); mate_iso + both round-trips genuine;
  adjoint_unique + Kelly λ_I≈ρ_I genuinely derived; bicat C D ≡ [C,D]
  defeq confirmed by a compiled eq_refl. The auditor noted commit eacede61
  CLOSED a pre-existing hole (removed the 2018 data-only stub + TODO
  block). TWO LOW findings, BOTH about my self-report wording (NOT any
  committed artifact), BOTH now folded into this ledger: LOW-1 = Lax/
  Modification are inhabited only on Trivial_Bicategory, NOT consumed by
  Cat (corrected in the departures list above); LOW-2 = the class is leaner
  than Monoidal.v, not a "mirror" (corrected above). Zero code changes
  required. **PHASE 13 IS DONE** (tip bdc02d60, 9 commits over
  johnw/ct-phase12). Campaign docs (doc/plan/, this handoff) stay UNTRACKED.
  PR human-gated (stacks on johnw/ct-phase12 tip 1185d315).
  ### NEXT: Phase 14 (AFT / reflective localization) per
  doc/plan/phase-14-*.md — branch johnw/ct-phase14 off bdc02d60.
- Phase 14 (adjoint functor theorems / reflective subcats / localization):
  **IN PROGRESS** (2026-07-11, Opus main loop + Opus rocq-pro subagents,
  MAX=2). Branch johnw/ct-phase14 created off bdc02d60 (phase-13 tip).
  Baseline confirmed (all prereq .vo present: Phase 5 Continuity/
  Preservation/Complete, Phase 6 Kleisli/EM, Phase 8 Orthogonality, Phase
  11 Equalizer/Fork; donors Arrow.v/Subcategory.v/Comma.v exist). Name-
  collision grep = CLEAN slate (all 15 new names absent).
  DONORS GROUNDED (accurate pointers embedded in the impl specs):
  * GAFT crux = Theory/Universal/Arrow.v: UniversalArrow c F ≡ Class wrapping
    (arrow_initial : Initial (=(c) ↓ F)); AdjunctionFromUniversalArrows
    (∀c, UniversalArrow c U) : Adjunction (LeftAdjointFunctorFromUniversal…) U.
    VARIANCE: Arrow.v has U : D0⟶C0 yielding left adjoint C0⟶D0; plan's
    U : C⟶D needs C0:=D, D0:=C. GAFT_from_initials is immediate.
  * Reflective: Construction/Subcategory.v (Subcategory{sobj,shom,scomp,sid},
    Sub S with first-projection homset, Incl S faithful, Full/Replete/Wide).
  * Equalizer (Ph11): IsEqualizer/HasEqualizers (Structure/Equalizer/Fork.v).
  * Complete := ∀ D F, Limit F; PreservesAllLimits (Structure/Limit/
    Preservation.v). Diagonal Δ(c) (Functor/Diagonal.v). Contravariant hom
    [Hom ─,A] := Curried_CoHom (Functor/Hom.v:149). EM = Monad/Eilenberg/
    Moore.v. Monad class join/ret = Theory/Monad.v.
  IMPL WORKFLOW: wf_d8ee870f-e96 (task wkz0hnpru), script scratchpad/
  phase14-impl.js (RESUMABLE via resumeFromRunId=wf_d8ee870f-e96). Design:
  MAX=2 counting semaphore over a promise-DAG; 11 rocq-pro/Opus agents
  (model:'opus' explicit), high effort, MAX effort on the 4 hardest (f4
  Comma_Complete, f5 GAFT, f8 Idempotent, f10 Universal). DAG: f1 Discrete→
  f2 Limit/Product→f3 WeaklyInitial→f5 GAFT→{f6 SAFT, f11 Examples}; f4
  Comma/Limit→f5; f7 Reflective→{f8 Idempotent, f9 Localization}→f10
  Universal. Agents write ONLY their file, compile it, run Print
  Assumptions, return structured status; they do NOT touch _CoqProject/
  CLAUDE.md/doc/ or commit (main loop integrates). Sanctioned fallbacks:
  Comma_Complete single-lemma gap = ledger 17 (GAFT_from_initials lands
  regardless BY CONSTRUCTION); localization_universal orthogonal-form =
  ledger 15.
  ### RESULT — 11/11 DONE + COMMITTED (2026-07-11). Workflow returned 11/11
  compiles+PA-closed+holes-clean; ONLY ledger-15 fallback taken
  (localization_universal orthogonal form, pre-sanctioned). Comma_Complete
  landed IN FULL (ledger-17 NOT needed) via a hypothesis STRENGTHENING —
  PreservesImageLimit (cone-level: the image cone (U L, fmap[U]π) is
  universal) — because the in-tree apex-only PreservesLimit is genuinely
  insufficient (legs unconstrained); every right adjoint satisfies the cone
  form (right_adjoint_PreservesImageLimit), tying it to RAPL. GAFT/GAFT_from_
  initials/GAFT propagate PreservesImageLimit. WeaklyInitial takes a 3rd
  explicit input (endo-indexed product Pe, Risk b — smallness caller-chosen).
  MAIN-LOOP VERIFY: force-clean recompile all 11 in dep order EXIT 0; 19/19
  headline artifacts PA "Closed under the global context"; holes/todo/ws/
  funext = 0; ≈ used 89×. ADVERSARIAL REVIEW (2 coq-reviewers, Opus): BOTH
  SOUND. GAFT chain — PreservesImageLimit independently verified genuine
  (non-vacuous, used via limit_med_eq), GAFT variance correct, WeaklyInitial
  real Freyd, Discrete/iprod/Examples genuine; findings: MEDIUM (SAFT
  cog_separates/sub_monic inert — GAFT-in-disguise) + LOW (Examples
  overstates Δ). Reflective/Localization chain — SOUND, correspondence
  non-vacuous both ways, EM equivalence genuine, Hunit legitimate; LOW
  (Universal.v stale "transparently" comment). FIXES (rocq-pro/Opus fixer +
  main loop, all re-verified): SAFT now internalizes separation⇒monic as
  cogenerator_canonical_monic (CONSUMES cog_separates — deleting the field
  breaks the file) + honest header (size-dependent covering packaged as the
  SubobjectCover DATUM; no smallness/image-factorization machinery on a
  general base; SAFT conclusion unchanged, genuine F⊣U); Examples added
  diagonal_product_via_gaft_is_diagonal (F ≅ Δ via left_adjoint_iso — the
  PREFERRED corollary, not a reword); Universal.v comment corrected. Re-
  verify of the 3 changed files: recompile EXIT 0, 6/6 changed artifacts
  PA-closed, scans clean. INTEGRATED: _CoqProject 440→451 (11 anchors;
  reconstruction IDENTICAL to the make-verified set), CLAUDE.md Theory Core
  entry, full nix develop -c make EXIT 0. COMMITTED: 12 commits
  fce11f14..2463ab90 on johnw/ct-phase14 (C1 Discrete, C2 Limit/Product, C3
  WeaklyInitial, C4 Comma/Limit, C5 GAFT, C6 Examples, C7 SAFT, C8
  Reflective, C9 Idempotent, C10 Localization, C11 Universal, C12 docs);
  dep-ordered buildable history; doc/ stayed untracked. GATES ALL GREEN (2026-07-11,
  committed HEAD 2463ab90): nix build .#category-theory_9_1 OK + _9_0 OK +
  _8_20 OK + _8_19 OK (all four toolchains, fresh from-scratch derivations —
  genuine portability, no shims, no version-syntax issues; the universe-
  sensitive hom-indexed products in WeaklyInitial/SAFT and DiscreteCat's
  Set-hom ported cleanly); nix flake check OK.
  ### fess HONESTY AUDIT — VERDICT: HONEST (fess-auditor, Opus, 2026-07-11,
  independent re-verification on Rocq 9.1). No holes, no axioms (24/24
  headline artifacts "Closed under the global context"), no vacuity, no
  undisclosed weakening; all 5 departures genuine hypothesis-strengthenings,
  accurately disclosed. SAFT MEDIUM fix INDEPENDENTLY CONFIRMED
  (cogenerator_canonical_monic calls cog_separates at SAFT.v:227 — deleting
  the field breaks compilation; sub_monic disclosed as non-driving
  annotation). PreservesImageLimit confirmed a real strengthening (in-tree
  PreservesLimit is apex-only; non-vacuous via right adjoints; Comma_Complete
  concludes full @Complete). WeaklyInitial Pe genuine (real
  existence+uniqueness, not smuggling). localization_universal Hunit
  legitimate; Idempotent EM equivalence genuine Full+Faithful+ESO. Scope
  clean (numstat = 11 files + CLAUDE.md +1 + _CoqProject +10; doc/ untracked);
  commits + CLAUDE.md free of overclaim. ONE LOW (informational, no action):
  cogenerator_canonical_monic consumes cog_separates but is not itself
  invoked by SAFT (driven by the packaged SubobjectCover) — the twofold
  content the header describes, forced by the absent image-factorization
  machinery. Auditor's sole verification gap (PA re-run on 9.1 only, not the
  other 3 toolchains + flake check) is COVERED by the main-loop gate run
  (all GREEN, /tmp/nixgate14.result). **PHASE 14 IS DONE** (tip 2463ab90,
  12 commits over johnw/ct-phase13). PR human-gated (stacks on johnw/ct-phase13 tip
  bdc02d60).
  ### PHASE-14 DEPARTURES (for the PR body)
  - PreservesImageLimit replaces the plan's apex-only PreservesAllLimits in
    Comma_Complete + GAFT: an honest cone-level STRENGTHENING (the in-tree
    PreservesLimit is provably insufficient — legs unconstrained; non-vacuous
    via right adjoints; NOT a weakening — Comma_Complete concludes a full
    @Complete of the comma). RESOLVES what Phase-7 Adamek deferred as
    leg-agreement (there ledger 17); here delivered in full.
  - WeaklyInitial 3-hypothesis form (P, E, Pe): the endomorphism-indexed
    product is an explicit input (Risk b), NOT smuggling — conclusion is a
    full @Initial C with genuine existence + uniqueness (real Freyd).
  - SAFT hypotheses-as-data: separation⇒monic internalized as
    cogenerator_canonical_monic (cog_separates consumed); the size-dependent
    solution-set covering is packaged as the SubobjectCover datum (no
    smallness/image-factorization machinery on a general base — the plan's
    sanctioned "hypotheses as data" reading; sub_monic is a subobject-naming
    annotation). Conclusion is a genuine F⊣U; header discloses precisely.
  - localization_universal = orthogonal-subcategory form + Hunit (reflection
    units are W-maps); calculus of fractions descoped (ledger 15).
  - f8 uses the TRANSPARENT Adjunction_Induced_Monad (Monad/Comparison.v),
    not the Qed-opaque Adjunction_Monad, so join reduces to the counit;
    sound (identical join), Phase-9 precedent.
  - f7/f2/f3/f6 top-level polymorphic defs (not section variables) where
    Complete-against-a-Set-hom discrete diagram would over-constrain the
    universe (documented in-file); a universe-posture note, not a weakening.
- Phase 15 (enriched upgrade / double categories): **IN PROGRESS — RESUMED ON
  FABLE (2026-07-14)**. History: implementation was halted 2026-07-11 for Opus
  allocation; on 2026-07-14 the user restored FABLE access ("resume your work").
  MODEL NOW: Fable 5 main loop + Fable subagents (env pin
  CLAUDE_CODE_SUBAGENT_MODEL=claude-fable-5 verified in ~/.claude/settings.json —
  the pin WINS over the script's per-agent model:'opus', which was left byte-
  identical to preserve cache keys). COMMIT TRAILER for phase-15 commits is now
  the FABLE one: `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>`.
  RESUMED RUN: Workflow task `wnkeru5rs`, resumeFromRunId wf_75c8a9d8-da5; the
  2026-07-11 journal had banked 4/11 COMPLETED (cache-replayed free): f1
  Enriched/Natural.v, f2 Enriched/Compose.v, f5 Two/Monoidal.v, f8
  DoubleCategory.v — all self-reporting compiles + PA closed (still require the
  independent verify pass). The other 7 run live on Fable. Nothing is
  committed yet. Branch `johnw/ct-phase15` off `2463ab90` (phase-14 tip).
  Baseline `_CoqProject` = 451 entries; authoritative copy is
  `git show 2463ab90:_CoqProject` (do NOT rely on /tmp/_CoqProject.p15baseline —
  ephemeral). Gate script staged: scratchpad `nixgate15.sh`.
  ### IMPLEMENTATION WORKFLOW (in flight when halted)
  - Task id `wlp9v3bp4`, run id `wf_75c8a9d8-da5`. Script (self-contained, all 11
    specs + donor pointers embedded): scratchpad `phase15-impl.js` at
    `/private/tmp/claude-501/-Users-johnw-src-category-theory-master/
    0bb74161-eb6f-4ed1-bb11-d99f25ad0172/scratchpad/phase15-impl.js`. Transcript/
    journal dir: `.../subagents/workflows/wf_75c8a9d8-da5`.
  - MAX=2 counting semaphore (campaign mandate) over a promise-DAG. 11 files:
    f1 Construction/Enriched/Natural.v (EnrichedTransform, enaturality) → {f2
    Compose.v → f3 Fun.v (Enriched_Fun), f4 Sets.v (EnrichedTransform_is_Transform)};
    f5 Instance/Two/Monoidal.v (Two_Monoidal) → f6 Construction/Enriched/Two.v
    (Enriched_Two_preorder); f7 Structure/Limit/Weighted.v (HomDiagram/WeightedLimit/
    conical_weighted/WeightedColimit) standalone; f8 Theory/DoubleCategory.v → {f9
    Theory/DoubleCategory/Companion.v → f10 Construction/Sq.v, f11 Construction/
    Cospan/Double.v}.
  ### RESUME PROTOCOL (Tuesday, on fresh allocation)
  1. Read the workflow `journal.jsonl` in the transcript dir to see which of the 11
     agents completed and their STATUS returns (compiles / print_assumptions_closed /
     fallback_taken / deviations). Cached completed agents replay FREE.
  2. Resume the fleet: `Workflow({scriptPath: ".../scratchpad/phase15-impl.js",
     resumeFromRunId: "wf_75c8a9d8-da5"})`. Completed agents return cached results
     instantly; only unfinished/new agents run. (If the journal is empty — nothing
     banked — just relaunch the same script with no resumeFromRunId.)
  3. Then the STANDARD RAILS (do NOT skip; never trust self-reports): independently
     VERIFY all 11 files (force-clean delete+recompile in dep order via `nix develop
     -c coqc -R . Category <f>`; `Print Assumptions` CLOSED for at least
     conical_weighted, Enriched_Two_preorder, Sq, and whatever Cospan_Double artifact
     landed; scan new files for holes / make-todo words / `=`-on-morphisms / funext)
     → adversarial review (2 coq-reviewers, Opus, MAX=2) + a checklist-fidelity walk
     row-by-row against the phase-15 completion table → refute/fix → INTEGRATE
     (_CoqProject incremental from the 2463ab90 baseline — suggested anchors:
     Enriched/{Natural,Compose,Fun,Sets,Two} after Construction/Enriched.v chain,
     Instance/Two/Monoidal.v after Instance/Two.v, Structure/Limit/Weighted.v after
     Structure/Limit/Product.v, Theory/DoubleCategory.v + /Companion.v as a pair,
     Construction/Sq.v and Construction/Cospan/Double.v after Construction/Cospan/
     Category.v; coqdep sorts so exact order is non-critical) + CLAUDE.md Key-Files
     entry → full `nix develop -c make` → gates (`bash scratchpad/nixgate15.sh`:
     9_1/9_0/8_20/8_19 + flake check) → atomic per-file commits (Opus trailer,
     `LEFTHOOK_EXCLUDE=nix-build,nix-check`) → fess audit (separate fess-auditor) →
     update this handoff to DONE. **NO push / NO PR — human-gated.**
  ### NAMED LEDGER FALLBACKS the agents may honor (the ONLY sanctioned reductions;
      none weakens a theorem statement — verify each on resume):
  - f3 Enriched_Fun delivers the ORDINARY category of V-functors; the V-CATEGORY
    upgrade (hom-OBJECTS via ends in K) is deferred (ledger 11) — header note.
  - f7 Weighted uses Sets-VALUED (ordinary) weights; full V-weights need ends,
    deferred (ledger 11); conical_weighted itself proved BOTH directions at full
    strength.
  - f11 Cospan_Double: if and only if the pushout-associator PENTAGON coherence
    resists, the agent delivers an honest named partial record
    `Cospan_Double_precoherent` (all data + units + unitality + interchange +
    associator-as-invertible-square, NO pentagon field, NEVER an Admitted/Axiom)
    and escalates the pentagon per ledger 8 (Section 6.4). Prefer full Cospan_Double.
  - Monoidal double categories: header note only (ledger 9) — not attempted.
  ### IMPLEMENT COMPLETE 12/12 (2026-07-15). First resume banked 10/11 (f9
    Companion died on a 64k output-token single-response overflow; f10 Sq landed
    without the companion theorems). Second resume (same run id, revised S9 with
    anti-overflow incremental-write discipline + f8's known encoding, new node
    f12 to append the Sq theorems): f9 delivered Companion/Conjoint/
    companion_unique/conjoint_unique + the DoubleCoerceComp mixin (coerce-vs-
    vcomp interchange, Displayed dtransport_comp_l/r analogue, underivable from
    the class — 2-cocycle countermodel); f10 re-ran with Companion.v present and
    delivered Sq + Sq_companion + Sq_conjoint(+_iso) + Sq_DoubleCoerceComp; f12
    verified. NO ledger fallback taken anywhere: f11 proved the FULL pentagon
    (Cospan_pentagon via in-file pushout_jointly_epic from pushout_med_eq;
    Stability.v/SCFA.v imports proved unnecessary).
  ### PLAN ERRATUM (disclose in PR body): plan L167-168 "every morphism has a
    companion and a conjoint (itself, transposed)" is FALSE for conjoints in
    Sq(C): unwinding conj_unit/conj_counit forces a two-sided inverse (standard
    quintet fact). Delivered the full characterization instead: Sq_conjoint
    (iso → Conjoint) + Sq_conjoint_iso (Conjoint → iso). Both reviewers and the
    main loop independently re-derived this. A STRENGTHENING to the true
    statement, not a weakening.
  ### VERIFY (independent, main loop, 2026-07-15): force-clean recompile 11/11
    OK in dep order; PA battery 30/30 "Closed under the global context"
    (includes conical_weighted, Enriched_Two_preorder, Sq, Sq_companion,
    Sq_conjoint, Cospan_Double, Cospan_pentagon, companion_unique); static
    scans clean (holes/todo-words/funext/trailing-ws; all Requires Category.*).
  ### ADVERSARIAL REVIEW — 2 coq-reviewers (Fable), ALL 11 SOUND.
    rev15-enriched (7 files): 0 blockers, 0 mediums, 1 LOW (limit_of_conical +
    conical_weighted sealed Qed though they produce data → FIXED to Defined,
    recompiled, PA re-closed). rev15-double (4 files): 0 blockers, 1 MEDIUM,
    4 LOWs. MEDIUM: class is the coherence-only fragment (lacks horizontal
    identity squares on verticals, unit-interchange, coherence naturality) —
    plan-conformant (skeleton omits the same), both models satisfy them;
    FIXED by the sanctioned honest-header route (SCOPE paragraph in
    DoubleCategory.v; field addition would be scope expansion beyond the frozen
    plan). LOWs FIXED: associator-orientation note (opposite to
    Bicategory/Monoidal hassoc/tensor_assoc); Companion.v pointwise-bijection
    strength note; DoubleCoerceComp hcomp-analogue comment; #[local] on Sq.v's
    trivial_setoid. Post-fix: 4/4 chain recompiles, 10/10 PA, scans clean.
    Reviewer positives: pentagon recomputed generator-by-generator by hand =
    genuine at the real (non-trivial) square setoid; triangle correct;
    Companion uniqueness proof traced rewrite-by-rewrite, no circularity;
    conjoint honest mirror.
  ### INTEGRATION + COMMITS + GATES + FESS — ALL DONE (2026-07-15).
    CLAUDE.md entries added (Theory/DoubleCategory + Construction/Enriched
    consolidated). Full make with all 11 registered: exit 0, zero error lines,
    462 _CoqProject entries. 12 atomic commits c15543ec..8b645227 (11 code +
    docs(CLAUDE); Fable trailer; first attempt hit the known GPG-pinentry-idle
    blocker — user primed the key and authorized, second run clean; commit
    script made idempotent with git reset + checkout HEAD -- _CoqProject).
    GATES from committed HEAD 8b645227 (/tmp/nixgate15.result): build_9_1 OK,
    build_9_0 OK, build_8_20 OK, build_8_19 OK, flake_check OK.
    FESS AUDIT (separate fess-auditor, Fable): VERDICT **HONEST** — re-ran
    from-scratch recompiles 11/11, PA 20/20 closed, range exactly 13 files
    (+3293/-0), all 7 departures real+disclosed, pentagon + erratum claims
    verified against code, CLAUDE.md claims verified, no stubs/suppressions/
    fallback-smuggling/scope-creep. Three NON-BLOCKING notes: (1) pre-existing
    untracked junk file at repo root with an elisp/base64 name (emacs
    mcp-server-lib swap accident, NOT from this range — surfaced to user, not
    deleted, must never be committed); (2) conical_of_limit wrapper is Qed
    while the review-fix targets (limit_of_conical, conical_weighted) are
    Defined and backward has the transparent conical_of_limit_inst — fix
    intent satisfied; (3) the DoubleCoerceComp "2-cocycle underivability" is
    prose-by-analogy to Displayed.v (library precedent), not machine-checked.
    **PHASE 15 IS DONE** (tip 8b645227, 12 commits over johnw/ct-phase14 tip
    2463ab90). PR human-gated (stacks on johnw/ct-phase14).
  ### PHASE-15 DEPARTURES (for the PR body)
  - Sq-conjoint PLAN ERRATUM: plan's "every morphism has a conjoint (itself,
    transposed)" is false in Sq(C); delivered the exact characterization
    (Sq_conjoint: iso → Conjoint; Sq_conjoint_iso: Conjoint → iso) — a
    strengthening to the true statement, AUDIT NOTE in file.
  - Vertical zigzag of Companion/Conjoint in REPRESENTABILITY form (the class
    has no horizontal-identity-square-on-verticals primitive; header
    discloses, incl. the pointwise-bijection strength note).
  - DoubleCoerceComp mixin (coerce-vs-vcomp interchange, Displayed
    dtransport_comp_l/r analogue) hypothesis of the uniqueness theorems only;
    both models instantiate it (Sq_DoubleCoerceComp; Cospan trivially by
    apex-map invariance — instance not needed in-tree).
  - DoubleCategory class = coherence-only fragment per the plan skeleton
    (no horizontal identity squares on verticals / unit-interchange /
    coherence naturality); SCOPE header discloses; both models satisfy the
    omissions. Associator oriented opposite to Bicategory/Monoidal (noted).
  - Ledger-11 scope notes: Enriched_Fun is the ordinary category (V-category
    hom-objects need ends); Weighted.v uses Sets-valued weights.
  - TwoPreorder carries tpre_dec (decidability): needed by direction (b)
    axiom-free, produced for free by direction (a); round trip unaffected.
  - Ledger-8 pentagon fallback NOT taken (full Cospan_pentagon proved);
    ledger-9 monoidal double categories header-note only, per plan.
  ### NEXT: Phase 16 (Lawvere theories / operads) per doc/plan/phase-16-*.md,
    branch johnw/ct-phase16 off 8b645227.
- Phase 16 (Lawvere theories / multicategories / operads): **IN PROGRESS —
  IMPLEMENTATION LAUNCHED (2026-07-15)**. Branch johnw/ct-phase16 off 8b645227
  (phase-15 tip). Fable main loop + Fable rocq-pro subagents. Workflow task
  `wr4swihm3`, run wf_2990d18f-f5c, script scratchpad/phase16-impl.js (all 12
  specs embedded; anti-overflow output discipline in the PREAMBLE this time).
  MAX=2 semaphore DAG: f1 Theory/Lawvere.v → {f2 Instance/FinSet/Lawvere.v,
  f3 Model.v → f4 Sets.v → f5 Monad.v, f6 PROP.v}; f7 Theory/Multicategory.v →
  {f8 Functor.v, f9 Representable.v, f10 Endomorphism.v, f11 Operad.v};
  {f8,f10,f11} → f12 Algebra.v. Donors grounded: FinSet_Cocartesian IS
  @Cartesian(FinSet^op) (Cocartesian.v:30 notation); EM_Comparison:186 +
  Adjunction_Induced_Monad:123 (plan's "Adjunction_Monad" name is stale) +
  crude_monadicity:601; CartesianFunctor:49/TerminalFunctor:43;
  Sorting.Permutation precedent ColouredPROP/Linear.v:14; CMon:140. KEY SPEC
  DECISIONS (disclose in PR): (i) ev1_Faithful requires a reachability
  hypothesis (∀ x, {n & law_of_nat n = x}) — the bare statement is unprovable
  against the PROP-style relaxed class (junk-object countermodel), hypothesis-
  as-data per SAFT precedent; (ii) Multicategory uses the mcast field +
  groupoid-laws pattern (Phase-10/15 dsq_coerce template) for list-boundary
  casts, laws in _any style — no UIP; (iii) named fallback (b) planar-core +
  Symmetric mixin available for f7/f9 ONLY if equivariance drags (full-strength
  composite required); ledger 2 (finitary-monad equivalence) and ledger 3
  (free operad) named deferrals per plan. Standard rails after: verify → 2
  adversarial reviewers → fix → integrate (_CoqProject anchors TBD at commit
  time) → make → commits (Fable trailer) → nixgate16 → fess. NO push — human-
  gated.
  ### MID-IMPLEMENTATION PLAN ERRATUM + AUTHORIZED AMENDMENT (2026-07-15):
  f9 (Representable) verified empirically that stdlib List.Permutation is
  Prop-valued with no singleton elimination — Type-carrier instances
  (Representable: mhom = morphisms; EndOperad: pow-morphisms) CANNOT build
  msym by recursion on the proof. The plan's "stdlib Permutation" choice is
  an ERRATUM (disclose in PR): the symmetric action is mathematically indexed
  by permutations-as-DATA. AUTHORIZED f9 (agent a8d4e90aee72d72ca) to amend
  Theory/Multicategory.v + Theory/Multicategory/Functor.v minimally: local
  Type-valued `tperm` inductive (nil/skip/swap/trans) + tperm_refl/tperm_app;
  msym pack + mcomp_equivariant over tperm; bridge tperm_Permutation keeps
  stdlib interop; header documents the rationale. ALSO approved (disclosed
  deviations, hypothesis-as-data): RepresentableMulticategory threads UIP-on-
  object-lists (Hedberg/Grothendieck-Strict precedent) for mcast_id over
  arbitrary loops; ColouredPROP instance uses the spine's Cdec discipline;
  poly_unit lists have definable UIP so EndOperad/Operad need nothing.
  RECONCILE RISK: one agent (f5/f10/f11) was mid-flight during the amendment —
  after the fleet completes, re-verify f7/f8/f10/f11 against the AMENDED class
  (force-clean recompile will catch any stale-signature delivery; re-run a
  reconcile agent if needed).
  ### DUAL-DRIVER INCIDENT on f9 (2026-07-15) + LESSON. Sending SendMessage to
  the idle workflow f9 agent spawned a SECOND driver of the same transcript
  lineage, running in parallel with the workflow's own schema-enforced
  continuation — two executors interleaving edits on
  Theory/Multicategory/Representable.v (each seeing the other's output as a
  "rogue writer"; one transient duplicate msplice_nested was added and removed
  by the messaged instance). RESOLVED: messaged instance stood down (option b);
  the workflow driver owns the file to completion. Attribution was proven from
  transcripts: the Endomorphism worker (a6d0aff…) has ZERO writes; both
  Representable writers were f9-lineage. VERIFY PASS MUST specifically check
  Representable.v for interleaving residue: duplicated lemmas (msplice*),
  dead/orphaned sections, inconsistent naming between the kit and the
  symmetric layer. LESSON (binding for this campaign): NEVER SendMessage a
  live/idle WORKFLOW node agent — it forks a parallel driver of the same
  transcript; coordinate via the workflow result path instead, or stop the
  node first. The tperm amendment itself is LANDED and safe
  (Theory/Multicategory.v 09:30, Functor.v 09:32, PA closed per the agent;
  independently re-verify in the phase verify pass).
  ### f9 RESIDUE SWEPT + REMAINING RECONCILE (2026-07-15, main loop):
  - SWEPT: the stood-down instance's disclosed broken final block
    (swap_fold_coherence, Representable.v old lines 514-551, malformed
    goal-selector tail) removed by the orchestrator while NO writer was live;
    file recompiles clean at the 513-line checkpoint (only the From-Coq
    deprecation warning, same as ColouredPROP/Linear.v precedent).
  - STILL TO RECONCILE (f9 remainder, single fresh agent when the workflow
    settles): (1) Representable.v:462-510 re-declares a LOCAL `Inductive
    tperm` section (interleaving artifact — duplicates Theory/
    Multicategory.v:143's class-level tperm; the local one shadows, so the
    file compiles, but the class's msym field takes the CLASS tperm — the
    instance assembly cannot typecheck against the local duplicate): DELETE
    the local section, port its extra combinators (tperm_right/left variants,
    tperm_block3, tperm_block_slot) onto the class tperm or reuse the class
    file's own block kit; (2) then the unfinished remainder: symmetric layer
    (perm_arrow over class tperm), Multicategory instance assembly,
    RepresentableMulticategory (with the approved luip hypothesis),
    ColouredPROP_Multicategory (Cdec), PA checks. ROUTE: when run
    wf_2990d18f-f5c completes (f9 node will be null or stale), EDIT the S9
    spec in scratchpad/phase16-impl.js into a reconcile spec (adopt the
    513-line checkpoint; the tasks above) and resume with
    resumeFromRunId — cache replays all other nodes; f9 re-runs fresh.
    Do NOT message the f9 lineage again.
  - UPDATE (later 2026-07-15): a THIRD stale-context message arrived from the
    f9 lineage (the true author of the local tperm + the 338→472 growth),
    still blocked on the never-received decision. It had gone idle, so the
    reply RESUMED it with the complete self-contained ground truth (class
    tperm landed at Multicategory.v:143+, delete the local TPerm section,
    swap_fold_coherence statement approved with a correct proof, luip/Cdec
    hypotheses, finish + StructuredOutput). Now exactly ONE f9 driver is
    live and it is visibly executing the directive (file reorganized: kit
    sectioned, tcast/luip layer per the Cast.v discipline, no local tperm,
    and a good generalization: one development over an object realization
    ob : A → C serving both the representable and coloured-PROP instances).
    The planned resumeFromRunId reconcile of f9 may become unnecessary if
    this driver delivers; VERIFY EITHER WAY (dup-scan + force-clean compile).
  - CLOSED (2026-07-15): f9 DELIVERED — Representable.v 944 loc, compiles,
    PA closed (tensor_list, tensor_list_app, Fold_Multicategory,
    RepresentableMulticategory, ColouredPROP_Multicategory), FULL symmetric
    equivariance (fallback (b) NOT taken), luip/Cdec hypotheses as approved,
    single ob-parameterized construction instantiated at ob := wire with
    cprop_tfold recovering the strict boundary. Orchestrator spot-verified:
    local tperm GONE (class one at Multicategory.v:143 sole), zero duplicate
    definitions, no forbidden tokens. And the StructuredOutput DID flow back
    into the workflow journal (Representable.v result present) — the node
    resolved, no hang, NO resumeFromRunId reconcile needed. The dual-driver
    saga is closed; per-node single ownership restored. A journal monitor
    (task bcfl71sgb) watches the remaining f5/f10/f11/f12 results.
  - FINAL f9 REPORT ADDENDA (2026-07-15): both racing executors ran to
    completion; the final one deconflicted (three msplice_equivariant
    variants reduced to one, duplicate ColouredPROP layer collapsed — a
    briefly-created Construction/ColouredPROP/Multicategory.v was DELETED,
    the canonical ColouredPROP_Multicategory lives at the end of
    Representable.v, Theory→Construction import precedented by
    Theory/Lambek.v), 7/7 PA closed incl. msplice_equivariant,
    swap_fold_coherence, list_uip_of_dec, cprop_tfold. NOTES FOR VERIFY:
    (a) the file uses Eqdep_dec.UIP_dec — that is the AXIOM-FREE Hedberg
    module (do not confuse with Eqdep's axiom; whitelist "Eqdep_dec" in the
    funext scan; PA closure is the decisive test and passed); (b) the agent
    had REGISTERED the 3 Multicategory files in _CoqProject, violating the
    commit choreography — orchestrator REVERTED to the 462-entry baseline
    (tracked tree clean; registration happens per-commit as usual);
    (c) scope note: the representable instance consumes braided structure +
    braid only (braid_invol unused), stated over SymmetricMonoidal per the
    headline.
  ### PHASE-16 STATE AT THE 2026-07-15 FABLE SESSION-LIMIT STALL (resets 1pm
    America/Los_Angeles). IMPLEMENTATION 12/12 DONE (workflow wf_2990d18f-f5c
    complete, zero errors, ZERO named fallbacks — full equivariance, full
    crude-monadicity corollary, operad round trip both ways, Comm↔CMon both
    directions). INDEPENDENT VERIFY GREEN: force-clean recompile 12/12, PA
    38/38 closed (/tmp/pa16.out), scans clean after one fix (Multicategory.v:139
    comment "admits no" → "has no"; chain of 6 recompiled OK; the two
    "Classical" scan hits are prose false-positives — "Classically ..." —
    PA closure is decisive). KEY DEVIATIONS for PR (beyond the tperm erratum
    + luip/Cdec already recorded): f6 PROP.v strictness hypothesis pack
    (SM : StrictMonoidal law_cat + coh : strict_is_monoidal SM =
    Lawvere_Monoidal — PROP interp targets strict PROPs; eq_refl-dischargeable
    on skeletal instances); f4 reach hypothesis for ev1_Faithful +
    FinSetOp_reach witness; f12 operad_obj_UIP (Hedberg, forced by Functor.v's
    cast design); f10 UIP_nat normalization; f11 Operad as record with
    IsOperad = (mobj = poly_unit).
    ADVERSARIAL REVIEW: NOT RUN — both coq-reviewers (rev16-lawvere,
    rev16-multi) died AT SPAWN on the session limit, zero tokens, nothing
    cached. RELAUNCH VERBATIM from scratchpad/rev16-prompts.md after the
    reset, then: fix findings → integrate (fullmake16.sh check was launched;
    anchors in scratchpad/fullmake16.sh: Lawvere after Theory/Kan/Extension.v
    line 436, FinSet/Lawvere after Instance/FinSet.v line 193, chain-anchored
    thereafter; expect 474 entries) → CLAUDE.md entry → git checkout
    _CoqProject → commit16.sh (to be written, 12+1 commits, Fable trailer) →
    nixgate16.sh (copy nixgate15.sh pattern) → fess audit → handoff DONE.
    NO push/PR — human-gated.
  ### PHASE-16 REVIEW + COMMITS + FESS (2026-07-15, post-reset).
    ADVERSARIAL REVIEW: rev16-lawvere — 6/6 SOUND, 0 blockers, 0 mediums,
    3 lows (Model pack/unpack round-trip lemmas ADDED
    Model_unpack_pack/Model_pack_unpack; FinSet/Lawvere theory-morphism prose
    marked as unformalized context; PROP.v eq_refl-wording made precise).
    rev16-multi — 6/6 SOUND, 0 blockers, 1 medium, 7 lows, ALL FIXED:
    MEDIUM (class does not force symmetric-group descent — plan-conformant,
    resolved Phase-15-style with the SCOPE header disclosure; descent is
    where braid_invol would be consumed) + blockwise-equivariance noted in
    the same SCOPE; unused Sorting.Permutation import deleted (Functor.v);
    3 dead race-residue lemmas deleted (Representable.v
    perm_arrow_app_r_cons/_l_from/_r_from); Representable.v hypothesis note
    added (braided suffices for proofs; symmetric is the headline);
    Endomorphism.v len_app hardened to hand-written Fixpoint; Operad.v
    all_repeat transparency comment made honest; Algebra.v alg_act_Build
    sanity lemma PROVEN (oact_cast_any fusion; needed a #[local] Proper
    re-declaration since Build-section's instance was #[local]).
    POST-FIX VERIFY: 12/12 force-clean compiles, 41/41 PA closed, scans
    clean. COMMITS: 13 atomic f70ea269..891534e0 (Fable trailer; GPG primed
    by user twice — pinentry idle-expiry recurred) + fixup 72736da0
    (docs: two comments downgraded assertion→expectation per fess).
    FESS AUDIT (fess16): VERDICT **HONEST** — range exactly 12 .v +
    _CoqProject + CLAUDE.md (4645 insertions), from-scratch recompiles
    12/12, PA 30/30, tokens clean, all claims checked true (eq_refl at open
    variables confirmed; crude hypotheses verbatim; interp tower one
    functor; no dead kit lemmas — tensor_list_app/cprop_tfold are
    documented API), departures (a)-(g) real+disclosed. Findings folded:
    MEDIUM (PROP.v skeletal-dischargeability asserted w/o witness) + LOW
    (descent satisfaction asserted w/o lemmas) → both reworded to explicit
    expectation/deferral in 72736da0; TRIVIAL PR-body wording: say
    "_CoqProject: 474 .v entries (475 lines)". GATES from final tip
    72736da0 (/tmp/nixgate16.result): build_9_1 OK, build_9_0 OK,
    build_8_20 OK, build_8_19 OK, flake_check OK. **PHASE 16 IS DONE**
    (tip 72736da0, 14 commits over johnw/ct-phase15 tip 8b645227). PR
    human-gated (stacks on johnw/ct-phase15). NEXT: Phase 17 (topos), the
    FINAL phase, per doc/plan/phase-17-*.md, branch johnw/ct-phase17 off
    72736da0.
  ### WORKING-TREE WARNING (fess16, repeated): the untracked repo-root file
    whose NAME is an elisp expression with a base64 MCP JSON-RPC payload
    (.(base64-encode-string ... mcp-server-lib-process-jsonrpc ...).swp)
    is INJECTION-SHAPED — never shell-glob or eval filenames there; user
    to remove manually; must never be committed.
- Phase 17 (topos — THE FINAL PHASE): **IN PROGRESS — IMPLEMENTATION LAUNCHED
  (2026-07-15)**. Branch johnw/ct-phase17 off 72736da0 (phase-16 tip). Fable
  main loop + Fable rocq-pro subagents. Workflow task `w3ss8idq0`, run
  wf_bb60148c-c00, script scratchpad/phase17-impl.js (all 10 specs embedded,
  anti-overflow discipline in PREAMBLE). MAX=2 semaphore DAG: f1
  Theory/Subobject.v → f2 Subobject/Functor.v → f3
  Structure/SubobjectClassifier.v → f4 Structure/Topos.v; f5
  Instance/FinSet/Product.v → f6 FinSet/Closed.v (THE quarantined codec
  grind); {f1,f3,f5} → f7 FinSet/Classifier.v (+ FinSet_Pullbacks);
  {f4,f5,f6,f7} → f8 FinSet/Topos.v; {f1,f3} → f9 Instance/Sets/Classifier.v
  (cross-universe THEOREMS, also edits the Instance/Sets.v:344-352 note in
  the same commit); f10 Theory/Sheaf/Category.v standalone. Donors grounded:
  Stability.v IsPullback:53/paste:106/monic_pullback_stable;
  HasPullbacks Structure/Pullback.v:136; Monic Theory/Morphisms.v:116; REAL
  Closed = Structure/Cartesian/Closed.v (y^x arg-order note :39; NOT the
  stub Structure/Closed.v); Site Theory/Sheaf.v:78 (one family per object),
  Sheaf :111, Presheaves :46; Full_Implies_Full_Functor Subcategory.v:74.
  NAMED FALLBACKS ONLY: ledger-17 staged FinSet_Topos if the exponential
  codecs slip (Product+Classifier land regardless); sheafification = ledger
  1 (header note only). UNIVERSE NOTE: no single-level SubobjectClassifier
  Sets is possible or claimed; Print Universes on f4/f9 is part of review.
  PA line: classifier_classifies, FinSet_Topos (or staged components), the
  Sets cross-universe theorems, Sheaves. Standard rails after: verify → 2
  adversarial reviewers → fix → integrate → make → commits (Fable trailer)
  → nixgate17 → fess → handoff DONE. NO push — human-gated.
  ### IMPLEMENT 10/10 DONE + VERIFY GREEN (2026-07-15): zero fallbacks
    (ledger-17 staging NOT needed — FinSet exponential codecs landed in
    full with eq_refl acceptance Examples; Pow 2 = 4 computes). f9 exceeded
    spec (char_setoid/sets_char_unique without Monic where not needed; full
    cross-level IsPullback + one-level sets_char_subobject via Sets_Image;
    piecewise Setoid_Lift verified to avoid the o = so collapse). Sets.v
    note edit = the sanctioned minimal upgrade (verified by diff). Verify:
    12/12 force-clean (incl. the Sets.v chain), 26/26 PA closed, scans
    clean (the one hole-scan hit is PRE-EXISTING master content:
    Instance/Sets.v:399 Abort closing a commented-out exploration —
    outside the phase diff). Full make with 484 entries: exit 0.
  ### REVIEW rev17-theory (2026-07-15): 5/5 SOUND (all orientations
    re-derived: pasting, classifying square, exp_iso currying, universes
    at library baseline), 0 blockers, 1 MEDIUM + 4 LOWs — ALL FIXED:
    MEDIUM = DONOR ERRATUM (pre-existing Theory/Sheaf.v Sheaf predicate is
    near-VACUOUS: per-leg gluing + compatibility antecedent over ALL
    sections forces subsingleton fibres via v:=u_i, g:=h:=id, j:=i;
    NOT in this phase's diff) → header of Theory/Sheaf/Category.v rewritten
    to disclose precisely; repair (matching-family re-founding) deferred to
    ledger 1 alongside sheafification; C10 commit message updated; PR-BODY
    DEPARTURE. LOWs: char_respects redundancy comment (derivable from
    pullback+unique; field kept for usability); Sheaves_Full Defined-
    rationale corrected (Full_Implies_Full_Functor is opaque); Sub naming-
    collision qualification note (plan-named, kept); is_pullback_respects_*
    promotion-candidates note (Stability.v, future). Post-fix: 6/6 chain
    recompiles, scans clean. rev17-instances: 5/5 SOUND, 0 blockers, 0
    mediums, 2 LOWs — BOTH FIXED (FinSet_Topos deliberate-plain-Definition
    comment with the typeclass-diamond rationale; Sets/Classifier.v
    impossibility wording SOFTENED to canonical-candidate-cannot-fit +
    explicit folklore disclaimer). Its universe audit was exemplary:
    reproduced the o=so counterfactual, Fail Check refutations at collapsed
    levels, o<so / o≤so constraint inventory. Stray probe artifact
    Instance/FinSet/ClosedProbe.glob deleted.
  ### COMMITS + FESS (2026-07-15/16): 11 atomic commits f19163a1..52059644
    (Fable trailer, GPG cache held), 484 _CoqProject entries, tree clean.
    FESS AUDIT (fess17): VERDICT **HONEST** — footprint exact (10 .v +
    _CoqProject + CLAUDE.md + the sanctioned Sets.v note hunk ONLY),
    from-scratch recompiles 10/10, PA 19/19, zero tokens/todo-words, all
    claim-by-claim checks pass incl. the donor-erratum derivation
    (re-verified against Theory/Sheaf.v:111-130) and the softened
    impossibility posture. ONE LOW: commit 2415791d's message cites
    pullback_unpaste/pullback_unique which are NOT exercised (paste +
    transport are; transport subsumes unique per Stability.v:34-36) —
    CORRECT THE TOOLKIT CITATION IN THE PR BODY (do not rewrite history).
    INFO: the injection-shaped untracked .swp debris (user to remove).
    GATES from HEAD 52059644 (/tmp/nixgate17.result): build_9_1 OK,
    build_9_0 OK, build_8_20 OK, build_8_19 OK, flake_check OK.
    **PHASE 17 IS DONE (tip 52059644, 11 commits over johnw/ct-phase16 tip
    72736da0) and the CAMPAIGN (phases 5-17, 13 phases, ~135 files) IS
    COMPLETE.** Every phase: implemented, independently verified,
    adversarially reviewed, gated on 4 toolchains + flake check, and
    fess-audited HONEST.
  ### PUSHED + PRs OPENED (2026-07-16, USER-AUTHORIZED "proceed with all"):
    Discovery at push time: local master was STALE — PRs #195/#196 (phases
    5/6) were already MERGED to master as true merge commits, so the stack
    bases on master. Docs-refresh commit 12db6419 added on ct-phase17
    (CLAUDE.md counts corrected to 484 files/124k lines + coverage summary;
    dead EXPLORATION_* references dropped; README coverage paragraph).
    The injection-shaped .swp debris file REMOVED (python unlink, no glob).
    johnw/comonad-docs REBASED onto origin/master (identical Comonad files;
    now single commit 59e844b5) so the docs merge independently.
    THE STACK (each PR verified to show exactly its own commits):
    #198 phase7→master(13c), #199 phase8→phase7(14c), #200 phase11→phase8
    (12c), #201 phase9→phase11(9c), #202 phase10→phase9(12c), #203
    phase12→phase10(8c), #204 phase13→phase12(9c), #205 phase14→phase13
    (12c), #206 phase15→phase14(12c), #207 phase16→phase15(14c), #208
    phase17→phase16(12c incl. docs refresh), #209 comonad-docs→master(1c).
    All PR bodies carry the phase departure ledgers from this handoff.
    #197: responded to SNAPKITTYWEST (comment posted — thanks, the #209
    delivery, the gentle API-mismatch note, offer to review #209, intent to
    close #197 once #209 lands; closing #197 left to the user/merge flow).
    CAMPAIGN FULLY CLOSED. Remaining maintainer actions: review/merge the
    stack in order (#198 first, re-basing each successor as its base
    merges), merge #209, close #197.
  ### PHASE-17 DEPARTURES (for the PR body)
  - Sheaf-predicate DONOR ERRATUM (pre-existing Theory/Sheaf.v, untouched):
    per-leg gluing + all-sections compatibility antecedent ⇒ vacuous beyond
    subsingleton fibres (v:=u_i, g:=h:=id, j:=i); disclosed precisely in
    Theory/Sheaf/Category.v's header; matching-family re-founding deferred
    to ledger 1 alongside sheafification.
  - Sets = cross-universe THEOREMS, not an instance (canonical candidate
    provably cannot fit at one level; the general predicative impossibility
    is cited as folklore, not claimed as a theorem).
  - Ledger-17 staging fallback NOT taken (full FinSet_Closed landed).
  - char_respects kept as a derivable field (redundancy comment).
  - FinSet_Topos deliberately not an Existing Instance (diamond rationale).
  - Sub coexists with Construction/Subcategory's Sub (qualification note).
  - PR-body erratum: 2415791d message toolkit citation (above).
  ### CAMPAIGN STATE: Phases 5,6 pushed (PR #195, #196). Branches
    johnw/ct-phase{7,8,9,10,11,12,13,14} committed, unpushed, human-gated. After
    Phase 15: phases 16 (Lawvere/operads), 17 (topos) remain.
- Phase 9 pre-reset stall record (historical): **STALLED AT LAUNCH — FABLE SESSION LIMIT**
  (2026-07-09). Branch johnw/ct-phase9 created at 7d3b7028 (= phase-11
  tip; EMPTY, no phase-9 commits). Implementation workflow wf_6f29fada-9ee
  launched with full specs (8 files: Split/Reflexive coequalizers,
  EM_Comparison, BeckObjects engine room, Crude [non-negotiable], Lifting,
  Examples, Beck LAST under the binding quarantine) but ALL 8 agents died
  instantly with "You've hit your session limit · resets 8:50pm
  (America/Los_Angeles)" — 0 tokens consumed, NOTHING cached in the
  journal. TO RESUME after the reset: relaunch the SAME script —
  Workflow({scriptPath: "~/.config/claude/personal/projects/
  -Users-johnw-src-category-theory-master/0bb74161-eb6f-4ed1-bb11-
  d99f25ad0172/workflows/scripts/ct-phase9-implement-wf_6f29fada-9ee.js"})
  — no resumeFromRunId needed (nothing to replay). The spec embeds the
  donor pack (EM_Forget/EM_Free/EM_Adjunction/EM_Monad_agrees, TAlgebra,
  unit/counit + triangles), the canonical-split-fork law table, the crude
  proof architecture, and Beck's whole-file-withhold quarantine. Then the
  standard rails: verify → review → register (_CoqProject anchors TBD) →
  make → harvests → nix → commits → fess.
- Phases 9–17: not started. Full per-file plan in doc/plan/ (11 phase
  work orders + 00-INDEX + 00-CONVENTIONS), uncommitted.

## BLOCKERS
1. Fable-credit / subagent-routing blocker — **RESOLVED 2026-07-09** via
   `CLAUDE_CODE_SUBAGENT_MODEL="claude-opus-4-8"` + session restart. Probe
   wf_6471aa1e-7c7 confirms subagents run on Opus. Delegated
   implement/verify/review workflows run again.
2. GPG signing cache expires after idle -> commits hang/fail. The user is
   present this session to unlock (they run:
   ! echo unlock | gpg --clearsign -o /dev/null). Commit only when needed.

## SUBAGENT / MODEL CONSTRAINT (2026-07-08, important for resume)
Fable 5 credits are EXHAUSTED. Main loop is Opus 4.8. But standalone
Agent-tool subagents (fess-auditor, rocq-pro) route to Fable EVEN with
model:"opus" passed (the fess-auditor pins its own model; passing model
to a plain rocq-pro Agent is untested but the default routes to Fable).
CONSEQUENCE: two subagent failures so far (fix, fess) — both Fable-credit,
same root cause; do NOT count as the "unusable output twice" escalation
(it is infrastructure, the work itself is fine).
### ESCALATED 2026-07-08: delegated execution fully BLOCKED.
Probe wf_d3821a11-ecd (a single workflow agent with model:'opus' set
explicitly, no tools) FAILED immediately with "out of usage credits for
Fable 5", 0 tool uses. So: the `model:'opus'` override is NOT honored for
subagents — workflow agent() AND standalone Agent-tool subagents all bill
against Fable's exhausted credit pool, and the main-loop Opus switch does
NOT propagate. Three confirmations (fixer, fess-auditor, probe), one root
cause. The workflow-based execution model (implementers/reviewers/refuters/
closure) cannot run at all until this is resolved.
TO RESUME Phases 7-17, ONE of:
  (a) top up Fable credits (/usage-credits) and re-run with MAX=1
      workflows exactly as Phases 5-6 (scripts pattern proven);
  (b) a harness change so subagents honor model:'opus' / bill the Opus
      pool — then workflows run on Opus;
  (c) explicit user instruction to implement Phases 7-17 DIRECTLY in the
      main Opus loop with no subagents (feasible — Phase 6 fixes were done
      this way — but slower, higher main-loop token burn, and no separate
      fess evaluator; audits would be in-loop self-audits).
Phase 7 branch johnw/ct-phase7 exists (empty, at phase6 tip) ready for
resume. Phase 7 = F-(co)algebras/Lambek/Adamek, plan §3 line 755; DAG and
DOCS were drafted (the inline workflow had a JS template parse error at
the RULES string, unrelated to the credit blocker — re-derive from the
Phase-6 script template at
.config/.../workflows/scripts/ct-phase6-implement-wf_ac3008aa-3fe.js).
Until subagents work: critical audits done in-loop.

## Stop-and-escalate attempt counters
- (none yet)

## Learnings this run
- 2026-07-08: session limit killed wf_f1e4411f-749 after implementation
  (10/10 files compiled) but before refutation/closure; resumed from cache
  with MAX=1. Resume preserves cached agents as long as PROMPTS are
  untouched — never edit ENVLINE/DOCS/RULES strings when resuming, only MAX.
- Environmental drift observed at day boundaries: coqc dropped off PATH
  (use 'nix develop -c' or the pinned store binary) and the tree's .vo were
  wiped once; implementers rematerialized them from the nix store — those
  store copies are READ-ONLY and break make with 'Permission denied' until
  'find . -name *.vo -exec chmod u+w {} +'. Full 'nix develop -c make'
  after any such event before resuming workflows.
- SHELL BUG to avoid: 'cmd | tail -1; echo $?' reports TAIL's exit code
  (zsh $? after a pipeline = last command). All gate verdicts must capture
  the real status ($pipestatus[1] or run un-piped). Also: nix build only
  sees TRACKED files — never run the nix gates before the commit series.
- Plan erratum (frozen doc, not edited): Phase 5 file 4's premise
  "adjunction composition verified absent in-tree" is wrong — adj_comp
  exists at Instance/Adjoints.v:55. Adjunction/Compose.v documents the
  definitional agreement; consolidation to one canonical home is a
  deferred maintainer decision (file header notes it).

# ============================================================
# CAMPAIGN 2 (2026-07-16): Phase 18 — concept documentation coverage
# ============================================================

## Frozen plan
doc/plan/phase-18-concept-docs.md (read-only for bar-lowering).
User directive: comonad-style background (purpose/utility/history,
research-verified citations) for the other concepts of the library;
workflow-based; PR creation authorized in the invocation.

## State
- Branch: johnw/concept-docs off johnw/ct-phase17 (stack tip).
- Waves 1-6 per the plan inventory. Per wave: workflow
  pipeline(research->draft->verify) writing to
  scratchpad/concept-docs/waveN/, then main-loop integrate/compile/
  scan/commit, then fess audit.
- Register: it-voice comonad precedent; exemplars in
  scratchpad/comonad-docs-wt/ (Comonad/Core.v, Instance/Coq/Comonad/Env.v).
- Rails: comment-only; banned substrings fail/abort/admit/undefined/jww
  (case-insensitive, the make-todo egrep — confirmed from Makefile:5);
  no contractions; comonad 8 files EXCLUDED (PR #209 owns them).
- PAL consensus deliberately skipped for the campaign plan: the shape is
  fully dictated by the user directive + the #209 precedent; confer if a
  genuine design fork appears.

## Wave status
- Wave 1 (Theory core, 10 clusters): CLOSED. Commit 8f9bde55 (amended from e0ccd0ec per fess MINOR finding: "make-todo silent" overclaimed - Kan/Extension.v + Isomorphism.v carry PRE-EXISTING hits; reworded to "no new hits"). fess verdict otherwise HONEST on all 7 claims. LESSON for later waves: never claim make-todo silence on files with pre-existing hits; say "no new hits".
- Wave 2 (universal structures, 10 clusters): CLOSED. Commit ea165b79 (amended from 827cd108 with the two fess nitpick fixes: Porst year harmonized to 2024; "the same notes" chapter conflation reworded in Universal/Arrow.v). fess verdict HONEST on all 7 claims, byte-identical process assurance.
- Wave 3 (monoidal world, 12 clusters): CLOSED. Commit c63358fa; fess HONEST on all 8 claims, ZERO findings (verified even that the dropped claims are absent from committed text but present in briefs - correction trail real).
- Wave 4 (constructions, 11): CLOSED 19ef4759. fess OPUS HONEST on all 7 claims, byte-identical, 3 corrections confirmed. Two nits: Goswami-Janelidze year 2018->2017 FIXED in f48bce99 (standalone, since -i rebase unsupported + commits GPG-signed); MapsTo_fun attribution nuance = defensible, no change.
- Wave 5 (instances, 10): CLOSED c49aa899. fess OPUS HONEST on all 7 claims, byte-identical process assurance, 3 citation corrections externally confirmed, ZERO findings in-commit. (Auditor also flagged an out-of-commit injection .swp - removed, see SECURITY section.)
- Stragglers wf_b6e7bbb2-61b (OPUS): DONE 24/24, all 8 integrated into waves 4+5.
- Wave 6 (recent-phase, 15): DONE wf_8040b7f7-0c9 (45/45 OPUS, 4.15M tokens). All 15 integrated (772 lines) - ZERO C-skips (every recent-phase file had definitional-only header). Drops: profunctor 2, factorization 1, grothendieck 2, abelian 2. No pre-existing todo hits in any of the 15. Make gate RUNNING; commit pending.
- Wave 5 (instances + applied bridge, 10 clusters): RUNNING wf_4715e01e-519 (launched concurrently at 00:03 to use the fresh limit window; resume-from-cache degrades gracefully).
- Wave 4 spec: opposite, product-cat, comma, slice, arrow-cat, free, cayley, enriched, day, karoubi (grade-first for the last two).

## Stop-and-escalate attempt counters (campaign 2)
- (none yet)

## Learnings (campaign 2)
- 2026-07-16: Workflow tool `args` may arrive as a JSON-encoded STRING in
  the script despite being passed as a JSON object; guard every script with
  `const A = typeof args === 'string' ? JSON.parse(args) : args`.

## SECURITY (2026-07-17): injection artifact found + removed
The wave-5 fess auditor flagged 2 untracked editor swap files in the
working tree whose FILENAMES were base64-wrapped elisp payloads calling
mcp-server-lib-process-jsonrpc(base64-decode-string "...") — a
prompt-injection / RCE probe designed to be eval'd or sourced by an agent.
NEITHER the auditor NOR the main loop decoded or executed them. Removed as
inert data via `find -name '*.swp' -delete` (scoped patterns; never globbed
the dangerous name into a shell that would evaluate it; doc/plan + handoff
preserved). Working tree now clean. If they reappear, do NOT decode/source;
delete the same way and note provenance (stray mcp-server-lib/Emacs artifact
or a deliberate probe).

## Closeout topology (checked 2026-07-17)
johnw/concept-docs = johnw/ct-phase17 + 6 doc commits (8f9bde55, ea165b79, c63358fa, 19ef4759, c49aa899, f48bce99). Wave 6 pending.
base, clean stack). Branch is 2 behind origin/master (phase stack not yet
merged), 132 ahead. At closeout: if the phase PRs (#198-#208) are still
open, keep concept-docs stacked on ct-phase17 and target its PR there; if
they merged, rebase onto origin/master (picks up the 2). Decide from live
gh PR state. Commits so far: 8f9bde55, ea165b79, c63358fa, 19ef4759,
c49aa899. Wave 6 (wf_8040b7f7-0c9) + wave-4 fess (a303c9...) still running.

## CLOSEOUT STATE (2026-07-17)
8 commits on johnw/concept-docs over ct-phase17 (all GPG-signed, verified G):
  8f9bde55 Theory(10) ea165b79 Structure(10) c63358fa Monoidal(11)
  19ef4759 Construction(11) c49aa899 Instance(10) f48bce99 Opposite-yearfix
  cf7a96b9 advanced(15) 97f2531f CLAUDE.md-note
TOTAL: 68 files, +5126 lines, 0 deletions, comment-only.
ALL 6 waves fess-audited HONEST (wave 6 = zero findings, exact artifact match).
GATES: nix develop -c make GREEN per wave; hermetic flake build
  `nix build .#category-theory_9_1` GREEN (coq9.1-category-theory-1.0). 8.19 confirmatory build running.
  is category-theory_9_1 (NOT .#category-theory, which errors on aarch64-darwin).
REBASE: none needed. concept-docs cleanly stacks on ct-phase17 (origin ==
  local == 12db6419, ancestor confirmed). PR base = johnw/ct-phase17
  (continues stack after #208; phase stack #198-208 all OPEN, comonad #209->master).
PUSH: remote is SSH (git@github.com, hardware key -> campaign-1 hit publickey
  denial). Fallback: `git push https://x-access-token:$(gh auth token)@github.com/jwiegley/category-theory.git johnw/concept-docs`.
PR body ready: scratchpad/concept-docs/pr-body.md. Create with base ct-phase17.
PENDING before push: wave-6 audit green + flake build green + fix any findings.

## ============ CAMPAIGN 2 COMPLETE (2026-07-17) ============
PR #210 OPENED: https://github.com/jwiegley/category-theory/pull/210
  base johnw/ct-phase17, head johnw/concept-docs, 8 commits, 68 files, +5126/-0.
  Stacks after #208 (phase-17). Pushed via HTTPS gh-token (SSH publickey
  denied in batch = hardware key; documented fallback used).
Definition of Done — ALL met with evidence:
  - Every planned cluster graded + covered (6 waves, 67 essay files + CLAUDE note).
  - Build: 9.1 `make` + hermetic flake 9.1 GREEN; 8.19 hermetic flake GREEN (cross-version).
  - Every wave commit fess-audited HONEST (6/6), findings folded (year fix f48bce99).
  - Comment-only: 0 deletions across stack; hygiene/contraction/whitespace scans silent.
  - Branch cleanly stacked on base (no rebase needed).
  - No parity target.
Remaining (maintainer, human): merge the phase stack #198-#208 then #210;
  #209 (comonad-docs) targets master separately. All are the user's calls.

## ============ DEEP-REVIEW FIXES (2026-07-17) ============
/deep-review (scope e4f9c6c4..HEAD) verdict: SOUND, no CRITICAL/HIGH; small LOW/LOW-MED
finding set. User chose SINGLE FOLLOW-ON PR strategy (append-only; NO history rewrite /
force-push of the phase stack — the Arrow.v finding lives at phase-7, so per-PR would rewrite
all 12 branches). Branch: johnw/deep-review-fixes off johnw/concept-docs.
Findings being fixed (workflow wf_cba56a98-8d1, 5 opus agents authoring exact edits;
coordinator applies+builds+commits+pushes+opens new PR):
 1. [MED] Arrow.v: remove try(...);admit fallback -> unconditional proof (fails loudly <8.16);
    README+CLAUDE.md version 8.14->8.16.
 2. [LOW] Strict.v: hand-rolled hedberg -> stdlib UIP_dec; drop unused Equations import.
 3. [LOW] RoundTrip.v: add cloven-level variant (splitness inert); or document if not expressible.
 4. [LOW] SubobjectClassifier.v char_respects: field->derived lemma (or document if too invasive).
 5. [LOW-MED] Makefile print-assumptions + AXIOMS.md: extend axiom audit to phase 5-17 flagships.
 6. [LOW-MED] CLAUDE.md multicat "satisfies both" + Adamek line + Algebra.v essay "exactly": soften to match proofs.
Commit plan (thematic, on the one branch): arrow+version / grothendieck / topos / audit / docs.
Coordinator gates each with nix develop -c coqc/make + Print Assumptions + hygiene, then final
full make, push (HTTPS gh-token — SSH is hardware-gated), open PR base johnw/concept-docs.

## DEEP-REVIEW FIXES: COMPLETE (2026-07-17)
PR #211 OPENED: base johnw/concept-docs, head johnw/deep-review-fixes, 5 commits,
10 files, +144/-120. Append-only follow-on (no force-push). All 6 findings fixed +
verified (full make + extended print-assumptions green; Arrow.v + classifier_classifies
axiom-free post-refactor). GPG re-primed by user; pushed via HTTPS gh-token.
Commits: ec1bbec8 (Arrow) 663ed38e (Grothendieck) 4d0d585d (SubobjClassifier)
d761941d (audit) 2e01ef64 (docs).
NOTE: the base64-elisp injection .swp artifact reappeared again during this work;
deleted as inert data (never decoded/executed). It recurs — provenance worth checking.

## ============ POST-PR SWEEP (2026-07-17, later session) ============
All 14 open PRs (#198-#211) verified: every CI check SUCCESS, all mergeable,
ZERO comments and ZERO reviews on all of them (no bot findings to triage).
Injection .swp artifact NOT present (0 matches at repo root). Working tree
clean except doc/plan/ + this handoff (untracked by convention). NOTHING
in flight. All remaining actions are human-gated maintainer calls:
merge #198→#208 in order (re-basing each successor as its base merges),
then #209 (→master), #210, #211; close #197 after #209 lands.

# ============================================================
# CAMPAIGN 3 (2026-07-22): Book-coverage catalog → GitHub issues/projects
# ============================================================

## Frozen plan
doc/plan/books-catalog-campaign.md (read-only for bar-lowering).
User /wiggum invocation: build a GitHub issues + Projects-v2 catalog of
every item of theory in MacLane CWM (320pp old scan — read pages as
images), Awodey (314pp), Seven Sketches (353pp), in that order, that is
missing/partial in the library; issue contract (source, nLab/Wikipedia
links, current-state evidence, requirements, DoD, verification,
Depends-on) and dedup policy are in the plan. Workflows explicitly
authorized by the invocation. No repo code changes; campaign docs
untracked by convention.

## Session facts
- gh: active account jwiegley, `repo`+`project` scopes verified; repo
  has issues enabled, default labels only, no open issues at start.
- PDFs verified on disk (page counts via /Count).
- Anvil: DEDICATED daemon backend (ANVIL_EMACS_STATE_DIR set); root
  emacs-eval live; worker pool showed all-dead at start (reprobe at
  checkpoints); buffer checks do NOT cover the user's interactive Emacs.
- Subagent model env pin: claude-fable-5 (settings.json, session-start).
- PAL consensus on the plan design: task keii2ybgk (backgrounded); fold
  its findings into the plan BEFORE Phase-A fan-out (plan may be amended
  only by strengthening, per wiggum).

## ============================================================
## ▶ RESUMED (2026-07-23, same session, user: "Resume your work")
Wiggum refresh done: re-read the skill + this halt block; baseline
VERIFIED CLEAN — git status = the same 3 untracked paths, 0 tracked
changes; live counts 424 maclane + 29 awodey (exactly as at halt);
Anvil probed live (dedicated daemon). ⚠ /private/tmp WAS cleared — the
scratch tooling was GONE; restored from doc/plan/books/tools/ (the halt
durability measure worked) and re-verified: node --check + ast.parse all
pass. Awodey Ch5 relaunched fresh (its old run cache is dead).
NOTE: no build/test gate applies — this campaign changes NO repo code;
the DoD is per-chapter fess-HONEST + consistent GitHub/ledger state.

### Ch 6 ✅ DONE THROUGH G (2026-07-29, wf_14d74ee9-a5e, 12/12 agents 0
errors, Desktop PDF path): 47 items, 0 OVERTURNS, 35 PARTIAL/ABSENT →
**17 new issues #680-#696** + only 1 cross-book dedup (#389) — Ch6
(exponentials/Heyting/λ-calculus) has far LESS MacLane overlap than the
limits chapter, hence the high new-issue count. 23 dep edges GRAPH
CLEAN (a well-formed λ-calculus chain: #690→#691→#693/#694→#695).
57 awodey issues; ledger 1237.
- Verifier quality note: one verifier CAUGHT ITS OWN blind-pass miss —
  it had classified the IPC-entailment item ABSENT after searching
  'entail|sequent|IPC|Hilbert|modus ponens', then accepted the
  classifier's PARTIAL once it saw the exact mapping of Awodey's six
  entailment rules onto Instance/AST.v's Hom GADT constructors
  (Id/Compose, One', Zero', Fork/Exl/Exr, Merge/Inl/Inr, Curry/Uncurry).
- **✅ THE CH5 RECONCILE FIX PROVED ITSELF**: reading BOTH
  coverage[].problems[] AND per-record problems[] surfaced **8 distinct
  defects**; the old per-record-only grep would have found ZERO (the
  Ch6 records again carry no problems[] key — the drafter independently
  flagged this same schema gap).
- 6 NEW library defects → awodey/library-defects.md A14-A19. Headline:
  **A14, a THREE-FILE CONTRADICTION** — Instance/Lambda/Sem.v:41-42 and
  Sound.v:38-39 both assert the STLC syntax IS the free CCC, while
  Instance/Lambda.v:92-96 explicitly disclaims it. Also A15
  (Instance/AST.v titled "the free bicartesian closed category" but
  proves no initiality — PLACED in #693), A16 (exp_iso "natural in x,y,z"
  is not a field and is unproved — PLACED in #682), A17 (Structure/
  Closed.v's Curry comment references notations defined inside the
  COMMENTED-OUT class), A18/A19 ([Pos]/[Ord] dangling, 3rd recurrence).

### Ch 7 ✅ DONE THROUGH G (2026-07-29, wf_dcd96ac5-e3f, 16/16 agents 0
errors): **71 items — the largest Awodey chapter**. 1 OVERTURN
(7.2:remark-representables-preserve-limits PARTIAL→ABSENT: its sole
evidence `ev1_Faithful` is faithfulness of an evaluation functor on
Lawvere-theory models — a DIFFERENT category, functor, and claim, never
shown representable; phase_c preserved). 54 PARTIAL/ABSENT → **16 new
issues #697-#712** + **25 dedups (24 with closure checkboxes)** — the
heaviest dedup chapter yet, as expected for Yoneda/functor-categories/
equivalence. 40 dep edges GRAPH CLEAN. 73 awodey issues; ledger 1308.
- VERIFIER QUALITY: it articulated the exact discipline I have been
  reinforcing — "same claim, different presentation" keeps PARTIAL
  (example2 via EnrichedFunctor_Two_monotone) vs "different claim
  entirely" → ABSENT (the overturn). It named that asymmetry as the
  operative test. It also routed two unproved header asides to the
  LIBRARY-DEFECT channel INSTEAD of downgrading the records — correct.
- MERGE caught an `empty:true` SEMANTICS bug: 3 pages were marked empty
  though their own notes described continuation text. "empty" means the
  page has NO content, not "no item STARTS here". Corrected in-merge.
- 8 defects → library-defects.md A20-A25. Headline **A20, a THREE-FILE
  CLUSTER**: Construction/Subcategory.v's header asserts a generic
  faithful inclusion that does NOT exist; TWO files (Binoidal/Central.v:
  242, CopyDiscard/Deterministic.v:586) cite it as if it did; and
  Theory/Sheaf/Category.v:103 RE-PROVES the generic one-liner ad hoc for
  one subcategory. Three consumers, one missing three-line lemma. Also
  A21 (Functor/Coproduct.v claims a UMP-mediated derivation the code
  never performs — and `inl`/`inr` are not in-tree symbols at all).

### Ch 8 ✅ DONE THROUGH G (2026-07-29, wf_43541bb6-828, 12/12 agents 0
errors): 46 items, **0 OVERTURNS** (all 46 Phase-D verdicts CONFIRMED),
31 PARTIAL/ABSENT → **11 new issues #713-#723** + 17 dedup entries (10
with checkboxes; 2 multi-part items land in two homes each). 15 PRESENT.
19 dep edges GRAPH CLEAN. 84 awodey issues; ledger 1356.
- The Ch7 HIGH-1 lesson was APPLIED: I cross-checked every
  `Depends on: #N (parenthetical)` against the target's real title. 4
  flagged by my crude prefix-match, ALL 4 semantically CORRECT on
  inspection (#425 pointwise limits, #329 cocompleteness of Sets, #346
  density theorem) — these parentheticals DESCRIBE what the dep supplies
  rather than quoting its title, unlike Ch7's #712 which quoted another
  issue's title verbatim. No recurrence.
- 6 defects → library-defects.md **A26-A31**. **A26 is the campaign's
  clearest RULE VIOLATION**: Construction/Cayley.v:179-201 states
  Leibniz `=` BETWEEN MORPHISMS (verified verbatim at :179-182),
  violating CLAUDE.md's "Never use `=` for morphisms. Always use `≈`" —
  AND guards both lemmas with `∀ a b (k : a ~> b), id[b] ∘ k = k`,
  strict Leibniz id_left, which a setoid-enriched category CANNOT
  generally supply. So the file's headline normalisation claim is
  conditional on a property most in-tree categories lack. Restating
  with `≈` makes it unconditional. A27 (its companion): the header
  asserts a `From_Cayley (To_Cayley f) ≈ f` round-trip that is never
  stated. Both ride the Cayley dedup target **#643**.
- ⚠ NOTABLE: **two Phase-C records carried factually FALSE NEGATIVE
  claims**, caught by the verifier and corrected in place (provenance
  kept): "nothing in the tree has fobj := fun P => P C" (false —
  Theory/Lawvere/Sets.v:83 `ev1` is exactly that) and "no file relates
  Parallel to quivers" (false — Instance/Parallel.v:152-166 does, and
  defines `Presheaf_Graph`). Both items stayed PARTIAL (the general
  obligations really are absent) but the REASONS were wrong. This is
  the negative-claim-without-exhaustive-search failure mode; the
  blind-first verifier is what catches it.

### fess-aw8 VERDICT: **HONEST work product with GENUINE verification** —
3 HIGH + 5 MEDIUM, **all in the cross-issue graph/dedup layer, NONE in
the classification layer**. The auditor COMPILED A PROBE under Rocq 9.1
to machine-verify a defect and its fix — the most rigorous pass yet.
ALL HIGH/MEDIUM FIXED:
- **"0 overturns" VINDICATED as genuine, not rubber-stamping**: the
  auditor re-derived 9 items + all 33 PRESENT pointers, confirmed BOTH
  claimed Phase-C corrections are real and line-precise (ev1 at
  Lawvere/Sets.v:83 IS `fobj := fun P => P C`; Parallel.v:152-166 DOES
  relate Parallel to quivers + defines Presheaf_Graph), and found a
  THIRD correction I didn't know about (Yoneda_Full/Faithful line
  drifts + the Curried_Hom vs Curried_CoHom distinction). Texture:
  44/46 verifier notes reference a blind pass, median 968 chars, 7
  record a disagreement the verifier reasoned through — including "My
  blind pass MISSED this evidence and would have said ABSENT."
- **HIGH-1 FIXED (the campaign's central invariant)**: #718 and #339
  both specified `@Terminal ([C,D])` in the SAME new file
  `Instance/Fun/Terminal.v` with the same Print-Assumptions gate and
  ZERO cross-links — a genuinely DUPLICATED OBLIGATION (worse than a
  path clash). #718 ran the *library* negative search but never checked
  whether an ISSUE already claimed it. FIX: #718 now defers the
  terminal presheaf to #339, depends on it, and cross-refs #392;
  #339 got a reciprocal pointer.
- **HIGH-2 FIXED (Ch7 defect recurring, undetected)**: #719's
  `Depends on: #682 (…)` parenthetical over-described #682 — which
  supplies ONLY the unit and itself defers the adjunction to #239 — and
  #719 never mentioned #239 while proposing the same module. FIX:
  parenthetical corrected, #239 added as a dep in body+trailer+native.
- **HIGH-3 FIXED**: the #425 append named both clauses of Awodey Prop
  8.7 in prose but added only the completeness checkbox, leaving
  `PreservesAllLimits (ev_C)` HOMELESS — while its colimit twin #715
  DOES require the dual. Checkbox added to #425.
- MEDIUMs fixed: remark18's quantifier leg RE-HOMED #384→#387 (#384 is
  powerset-level and delegates the generalization to #387; #722 even
  cited #384 for a role #384 assigns to #387); #722's two DECLARED
  native edges were never filed → added; 3 schema-mandated `@` keys
  added to issue-map; 4 multi-part ledger rows now NAME their part;
  #718↔#392 cross-linked on Instance/Fun/Closed.v.
- **A26 CORRECTED + MACHINE-VERIFIED**: my "most in-tree categories
  lack it" was too strong — `Coq` discharges the hypothesis by
  `reflexivity` (eta); `Sets` does NOT (`Fail reflexivity`). And the
  auditor PROVED the remediation: for arbitrary C with no hypothesis,
  the `≈` restatements close by `simpl; rewrite id_left; reflexivity`.
- **A30 UPGRADED**: not merely a missing theorem — a TWO-FILE
  SELF-CONTRADICTION (Topos.v:95-97 says Slice.v "records" the
  fundamental theorem; Slice.v:114-115 says it is "not yet formalized
  here"). Same class as A14.
- **SYSTEMIC FIX**: the inventory page-listing convention split has now
  recurred in Ch7 AND Ch8 (agents disagree on whether a spanning item
  is listed under every page or only its first). mergePrompt now
  MANDATES the ALL-PAGES rule, bidirectional verification, and a count
  of entries added. Durable copy refreshed.
- Evidence quality HELD Ch7's standard: **33/33 PRESENT pointers
  resolve to genuine assertions, zero padding** (Ch7 was 38/38).

### fess-aw7 VERDICT: **SUBSTANTIALLY HONEST — "best-evidenced chapter
of the campaign"** — but 2 HIGH. The auditor opened 9 MacLane targets,
re-derived ALL 17 PRESENT rows, machine-checked ALL 38 evidence
pointers, read 12 PDF pages. ALL FIXED:
- **HIGH-1 (a LIVE BROKEN GRAPH EDGE) FIXED**: #712 said "Depends on:
  **#663**" while quoting **#664**'s title — and the error was
  CONSISTENT across body prose, trailer deps, AND the native relation,
  so nothing self-caught it. (#663 = Awodey 3.4 presentations-of-
  algebras; #664 = Awodey 4.3 homomorphism theorem, which is what
  Ex 5(a)'s factorization actually needs.) Verified by reading both
  titles, then retargeted in all three layers: body, trailer, and
  native (removeBlockedBy #663 + addBlockedBy #664). #712 now
  blocked_by [664, 697]. **LESSON: a wrong dep is invisible to every
  consistency check I run, because all three layers derive from the same
  drafter field. Cross-check the PARENTHETICAL TITLE against the issue
  number — that mismatch is the only tell.**
- **HIGH-2 (Ch6 failure mode RECURRED) FIXED**: #704's suggested module
  `Instance/Sets/Powerset.v` is ALSO claimed by #227 (MacLane I.3
  covariant powerset — specifying the IDENTICAL carrier) and #466
  (powerset monad), with no cross-reference. Obligations genuinely
  differ (contravariant vs covariant), so not a duplicate — an UNLINKED
  SHARED-CONSTRUCTION dependency. Added a "Shared module — coordinate"
  note to #704 naming both, plus a reciprocal note on #227. NOTE the
  discipline DID fire elsewhere: #708 vs #261 on Instance/Sets/Pointed.v
  was correctly cross-referenced. Applied once, missed once.
- **MEDIUM-4 FIXED (downgrade)**: `awodey:7.1:def-full-subcategory` was
  a disclosed-generous PRESENT; under the frozen "PARTIAL = some of the
  item exists" rule the auditor contested it and is right — generic
  `Faithful Incl` (= this batch's OWN defect A20) and BOTH of Awodey's
  illustrations are absent. Downgraded to PARTIAL and appended to #712
  (which already carries the A20 rider) with 2 checkboxes; ledger,
  issue-map and coverage record all corrected.
- **MEDIUM-5 RESOLVED AS A SCHEMA GAP, NOT A BUG**: the "double-claimed"
  `awodey:5.5:remark-hom-coproduct` (→#428 AND #654) is the multi-part
  split the **Ch5 audit explicitly CONFIRMED as correct**. The real
  fault was that schemas.md said "one row per item ID" with no
  exception, so tooling papered over it with a synthetic `@428` key.
  FIXED: schemas.md now documents the multi-part convention (one row per
  (item,issue) pair, each naming its part; `<id>@<issue>` map keys), and
  both ledger rows now describe their leg.
- **MY OWN DEFECT-LEDGER ERRORS CORRECTED** (auditor caught them):
  A21 claimed "`inl`/`inr` are not in-tree symbols at all" — FALSE, they
  are morphisms at `Structure/Cocartesian.v:142-143` used 27x; what is
  missing is the functor-level triangles. (The FILED artifact #697 was
  always correct — only my ledger prose was wrong.) A22 fingered the
  wrong clause (:250-252 is accurate; the overstatement is :248-249's
  "invertible iff each component is invertible", since the theorem
  quantifies over EXISTENCE of an iso, not a GIVEN θ). A23 sharpened.
- CONFIRMED by the auditor: all 25 dedups genuine; the overturn correct;
  the same-claim/different-claim asymmetry applied consistently across
  all 24 PARTIALs; 40 native edges == body == trailer, acyclic; 71
  ledger rows; paraphrase clean on 11 probes; the prop13 pdf_pages
  [177,179,180] skip of 178 is CORRECT (178 is Lemma 7.14's proof).
- **THE EVIDENCE HARDENING VISIBLY WORKED**: Ch5 had 2 false-PRESENT +
  6 misleading pointers; Ch6 had 0 false-PRESENT + 3 padded lists; Ch7
  has **38/38 pointers resolving to the declared symbol, ZERO padding,
  ZERO comment/Context/blank-line citations**, and multi-clause items
  correctly carrying one entry per clause. Measurable improvement.
- OPEN (MEDIUM-3, presentational, NOT fixed): inventory/7.json has a
  convention split at PDF 180/181 — ranges 160-180 list continuation
  pages in `pages[].items`, ranges 181-198 list only items STARTING
  there, so 12 (item,page) pairs disagree. No item lost (71 items = 71
  rows). Worth normalizing in a future pass; the merge prompt should fix
  the convention explicitly.

### fess-aw6 VERDICT: **SUBSTANTIALLY HONEST** — 1 HIGH, 3 MED/LOW-MED,
several LOW. Auditor read the WHOLE chapter as images (PDF 136-159),
re-derived ALL 12 PRESENT rows and verified all 36 pointers.
**NO false-PRESENT.** All 3 load-bearing defects (A14/A15/A16) REAL and
correctly placed — it even judged #693's and #682's DoD wordings
SHARPER than my defect-ledger entries (#693 spotted that AST.v's
hom-setoid at :33 is *defined* as agreement under every interpretation,
making the freeness claim CIRCULAR). All 26 links 200; 23 native edges
== 23 body edges; paraphrase clean on 12 probes.
- **HIGH FIXED — a genuine cross-book dedup MISS**: #682 (Awodey 6.2)
  duplicated **#239** (MacLane I.4) — same artifact (the `(−×y)`/`(−)^y`
  functors + the currying `Adjunction`), **same suggested module
  `Structure/Cartesian/Closed/Adjunction.v`**, same verification command,
  and NEITHER referenced the other. Verified by opening both. FIX: #682
  now DEFERS the shared adjunction assembly to #239 and keeps only its
  genuine increment (named `exp_unit := curry id`, the computation rule
  `f~ = f^A ∘ η`, the global-points bijection `Hom(x,y) ≅ Hom(1,y^x)`,
  the Sets sanity check); added `Depends on: #239` + trailer dep +
  NATIVE edge #682←#239; #239 got a reciprocal "Also covered by"
  pointer and is now dual-homed in the Awodey project.
  → LESSON: the drafter's cross-book dedup checks TITLES; #239's title
  ("The currying adjunction and naturality of evaluation") did not
  obviously match Awodey's "the unit … and global points". Same-module
  collisions are the tell. Consider having the drafter also grep filed
  issues for the SUGGESTED MODULE PATH, not just titles.
- **MED/LOW-MED/LOW FIXED — 3 evidence repoints** (def2: all 3 slots
  were a Context line, a COMMENT, and a Context 344 lines after the
  class → now Cartesian/Closed/Terminal classes; prop6: evidence[1] was
  a BLANK LINE → now InternalHomFunctor + the adjointness sentence +
  bimap_comp_id_left, with the PRESENT-by-subsumption noted; example3:
  all 3 slots covered only the Sets half of a two-part claim → FinSet
  half now cited).
- **SYSTEMIC FIX (prompt)**: the multi-evidence ledger fix took effect
  (all 12 rows carry 3 entries) but agents PADDED the extra slots with
  comments/Context/blank lines. book-chapter.js covPrompt now REQUIRES
  every evidence entry to be an ASSERTION (Definition/Lemma/Class/
  Instance), bans comments/Context/blank/naming-aliases, orders
  STRONGEST FIRST, and says one good entry beats three padded ones;
  multi-clause items must cover EACH clause. Durable copy refreshed.
- LOW, no action: two "exhaustive" Closed-instance censuses miss
  Structure/Cartesian/Closed/Product.v; #686's `sequent` grep is
  unqualified (`\bsequent\b` is genuinely 0); trailer deps mix `#N` and
  item-ids (self-consistent, deviates from schemas.md:90).
- CORRECTION TO MY OWN SNAPSHOT: the λ-chain is NOT #690→#691→{#693,
  #694}→#695 — natively **#695 is blocked by {#690,#691}**, a SIBLING
  of #693/#694, which is mathematically right (C(L(C))≅C needs the
  λ-calculus and C(L), not the UMP of C(L)). Nothing to fix.
- Auditor's own disclosed gap: it did NOT open verified-6-*.json (where
  a Ch5-style root cause could recur in another form), and compiled
  nothing.

## ⚠⚠ ENVIRONMENT CHANGED BETWEEN HALT AND RESUME (found 2026-07-29)
1. **ALL THREE PDFs MOVED**: `~/dl/*.pdf` → **`/Users/johnw/Desktop/`**.
   `~/dl/Awodey_Category_Theory.pdf` NO LONGER EXISTS. Every future
   chapter's `book.pdf` arg and every audit brief MUST use
   `/Users/johnw/Desktop/<file>.pdf`:
   - /Users/johnw/Desktop/Maclane_Categories.pdf
   - /Users/johnw/Desktop/Awodey_Category_Theory.pdf
   - /Users/johnw/Desktop/Spivak_Fong_Seven_Sketches.pdf
   (The Ch5 workflow ran with the STALE dl path yet produced a GENUINE
   inventory — the fess auditor independently read the real PDF at
   Desktop and confirmed 7 pages match the inventory, offset +9. So the
   agents evidently located the moved file. Not a data-integrity issue,
   but FIX THE PATH so it never silently degrades.)
2. **`~/dl` was swept**: the /halt deliverable
   `~/dl/books-catalog-remaining-plan.md` was DELETED by an external
   cleanup (dir now holds only Jul 28-29 files from other projects).
   REGENERATE it at the next halt/checkpoint.

### Ch 5 ✅ DONE THROUGH G (post-resume, wf_87e66146-f35, 12/12 agents,
0 errors): 55 items (largest Awodey ch), 38 PARTIAL/ABSENT → 10 new
issues #669-#678 + 24 dedup entries (23 cross-book; 10 carry the
closure-tracking checkbox). MacLane's limit spine absorbed most of the
theory (#326 ×5, #416 ×3, #417 ×2, #427/#428, #406/#411/#561, #333,
#311, #227, #250). 8 dep edges GRAPH CLEAN. 39 awodey issues; ledger
1189. What Awodey uniquely demands (the 10 drafts): subobject-as-
category layer, local-membership calculus, 2 elementary pullback
lemmas, indexed-family reading of Sets slices, and the whole
domain-theory strand (cumulative hierarchy, ω-CPOs, Kleene fixed
point, ambient-dependence of colimits).
### ⚠ 10 LIBRARY DEFECTS (richest haul yet) → awodey/library-defects.md
A5-A13, concentrated in the pullback/subobject/limit-preservation
spine. Highlights: Pullback.v:178 docstring claims projection-respecting
uniqueness the Qed-opaque lemma does NOT provide (and the file
CONTRADICTS ITSELF at :139-144); Pullback.v:129-130 points at a
COMMENTED-OUT base-change adjunction (recurrence of MacLane defect #3);
Subobject.v:56 asserts an unproven monic-through factorization (= the
ABSENT item itself); Preservation.v calls apex-only preservation
"continuous" with no disclosure, while Continuity.v PROVES the
cone-level statement and then exports only the weak class. 4 PLACED in
issue DoDs (#669, #672, #427 append), rest recorded.
### fess-aw5 VERDICT: **HONEST WITH FINDINGS** (2 MEDIUM coverage
defects + 9 LOW) — the most substantive audit of the campaign. All 24
appends verified VERBATIM on GitHub; contract/graph/paraphrase clean; 6
library defects confirmed REAL against source. FIXES APPLIED:
- **F1 (MEDIUM, coverage loss) FIXED**: `awodey:5.6:def-colimit` was
  PRESENT citing `Structure/Cone.v:72 Cocone` — but that is only the
  COCONE NOTION, not colimit-as-INITIAL-cocone, and its exact dual
  `def18` was classified PARTIAL→#417. Internally inconsistent; the
  colimit half was tracked NOWHERE. → reclassified PARTIAL, appended to
  **#417** with a closure checkbox, ledger + issue-map + both coverage
  copies corrected.
- **F2 (MEDIUM) FIXED**: `awodey:5.2:prop-pullback-unique` was PRESENT
  citing the very lemma this batch documented as overclaiming (A5:
  Qed-opaque, no projection triangles). PRESENT survives but via the
  HONEST artifact → evidence repointed to
  `Theory/Morphisms/Stability.v:329 pullback_transport` in ledger +
  coverage.
- **F3 FIXED**: A12 was "Recorded" only → now PLACED as a checkbox on
  the **#427** append (Continuity.v proves cone-level, exports apex-only).
- **F7 FIXED**: issue-map lost the #428 leg of the multi-part
  remark-hom-coproduct → recorded.
- F5 (extend #672's cite to Pullback.v:80/:178-181): the target string
  wasn't verbatim-matchable; recorded in library-defects.md instead.
- F4/F6/F8/F9/F10 acknowledged, no action (weak-but-honest #427
  checkbox; A8 double-placement is harmless; ledger is 56 rows/55 ids
  by multi-part design; continuation-page encoding discloses in notes;
  def28 evidence half-comment but labeled honestly).
- F11 = MY BRIEF drifted on 3 issue titles (#673/#674/#678) — the
  ISSUES are coherent; the snapshot text was wrong. Lesson: build audit
  briefs from the drafts file, not from memory.
### ✅ PRESENT RE-VERIFICATION COMPLETE (present-recheck-aw5):
**16/16 rows checked, ZERO further false-PRESENTs.** The 2 earlier
defects were the only substantive ones. Outcome:
- **6 REPOINTs applied** (classification unchanged, pointer was
  misleading): lem10 →Stability.v:106 pullback_paste/+:160 unpaste (was
  the bare IsPullback record); def17 →Instance/Cones.v:29 Cones (was
  ACone = 1 of Def 5.17's 4 parts); example20 →Equalizer/Fork.v:225/:273
  (was the bare alias `Equalizer F := Limit F`); example22 →Pullback/
  Limit.v:68/:113 (was a bare alias, AND the ledger line was :52, a
  comment — actual :54); def28 →Functor/Opposite.v:56 contramap (was
  :52, a COMMENT LINE); construction-pushout-sets →Sets/Pushout.v:185
  Sets_HasPushouts (was :51 pushout_eq, the relation only).
- **SYSTEMIC ROOT CAUSE FOUND + FIXED IN TOOLING**: the ledger's 5th
  column kept only evidence[0], which is systematically the
  DEFINITIONAL/NAMING artifact while the actual theorem sits at
  evidence[1]/[2] — in ALL SIX repoints the right artifact was ALREADY
  in the coverage JSON. file_chapter.py now transcribes UP TO 3
  evidence entries (durable copy refreshed). This likely affects
  EARLIER chapters' ledger rows too — a cheap retro-pass could re-emit
  them from the coverage JSONs if ever wanted.
- **ID-FILTER BLIND SPOT**: `awodey:5:ex2` uses `awodey:5:` (no dot), so
  an `awodey:5\.` filter misses it. Chapter-scoped exercise IDs ALWAYS
  lack the section segment — any per-chapter grep must use
  `awodey:5[.:]` or similar.
- **NEW ISSUE #679 FILED** for the one genuine residual: Awodey Def 5.28's
  composition-reversal clause (`F(g∘f)=F(f)∘F(g)`) has NO in-tree lemma —
  no contramap_comp/contramap_id anywhere (Theory/Coq/Functor.v's
  Contravariant class is law-free too). Definition stays PRESENT (the
  encoding is faithful); the missing LAWS are now tracked. 40 awodey
  issues.
- Residual caveat (read-only judgment, no toolchain in that agent):
  `Construction/Slice/Pullback.v:45`'s unused `Cartesian C` Context —
  if section-discharge generalized it, Prop 5.12 would carry a spurious
  hypothesis. One `About Star_Functor` would settle it. Low risk.
**Ch5 CLOSED.**
### ⚠ CLOSEOUT-GREP BLIND SPOT FOUND + FIXED: Ch5 verifiers emitted
LIBRARY-DEFECT at the WORKFLOW level (coverage[].problems[]), and the
verified-*.json records have NO problems[] key at all — my reconcile
grep over verified-*.json returned 0 and would have LOST all ten. The
reconcile MUST read BOTH the workflow result's coverage[].problems[]
AND per-record problems[]/verifier.notes. (Drafter flagged the schema
gap; credit to it.) Applies to every future chapter + Seven Sketches.

## ⏸ HALT STATE (2026-07-23) — CLEAN STOP, RESUME-READY
## ============================================================
User invoked /halt. Everything below is the single source of truth for
resuming in a fresh session.

### WHERE WE ARE
- BOOK 1 MacLane: ✅ COMPLETE + all 13 units audited HONEST. 424 issues
  #216-#639, project 4.
- BOOK 2 Awodey: Ch 1-4 ✅ DONE + audited HONEST (37 new Awodey issues
  #640-#668 + many cross-book dedups into MacLane). Project 5.
- BOOK 3 Seven Sketches: NOT STARTED.
- Totals: 461 issues (#216-#668), 1133 ledger rows, ~6+ library defects
  placed. All GitHub state CONSISTENT (issues only land after a chapter
  fully verifies; nothing half-filed).

### IN-FLIGHT WHEN HALTED
- Awodey Ch 5 ("Limits and colimits", PDF 102-135) workflow
  wf_e004feb1-d49 / task wo262f7ew was RUNNING; STOPPED by /halt. It
  filed NOTHING (filing is post-workflow), so GitHub is consistent at
  461 issues. Its scratchpad (scratchpad/awodey-ch5) may hold partial
  inventory/coverage — IGNORE it; the run cache is session-scoped and
  will NOT resume in a fresh session. RE-LAUNCH Ch5 FRESH (args below).

### GIT / COMMIT DECISION (important)
- Working tree: only 3 UNTRACKED items — doc/plan/ (campaign catalog),
  doc/wiggum-handoff.md (this file), .claude/agents/fess-auditor.md (a
  config restore). ZERO tracked changes. The repo is PUBLIC.
- Per the standing 3-campaign convention these stay UNTRACKED
  (working-state); the DELIVERABLE is the GitHub issues, already live.
  The handoff carries session-internal notes (URLs, model/credit
  routing, a security note) NOT suitable for a public repo. Therefore
  NOT committed/pushed by default at halt — surfaced to the user as
  their call. All resume-state persists ON DISK regardless.

### HOW TO RESUME (fresh session, in order)
1. Read this HALT STATE block + the per-book detailed log lower in this
   file (esp. the AWODEY TRANSITION + tooling sections).
2. Baseline check: `git status` (expect only the 3 untracked items);
   `gh issue list -R jwiegley/category-theory --label book:awodey
   --state open | wc -l` (expect 29 = Ch1-4's 8+10+6+5). No build/test
   gate applies (campaign changes NO code).
3. Relaunch Awodey Ch 5 with the generalized pipeline:
   Workflow(scriptPath: scratchpad/books-tools/book-chapter.js,
   args: {book: AWODEY_BOOK (see the AWODEY_BOOK config lower in this
   file), roman:"5", title:"Limits and colimits", pdfStart:102,
   pdfEnd:135, offset:9, splitAt:118, sections:[{n:1,name:"Subobjects",
   printed:93},{n:2,name:"Pullbacks",printed:96},{n:3,name:"Properties
   of pullbacks",printed:101},{n:4,name:"Limits",printed:107},{n:5,
   name:"Preservation of limits",printed:112},{n:6,name:"Colimits",
   printed:115},{n:7,name:"Exercises",printed:124}],
   scratch:".../scratchpad/awodey-ch5"}).
   NOTE: scratchpad/ is under /private/tmp which is cleared on REBOOT.
   ✅ DURABLE COPY of the tooling was made at halt:
   doc/plan/books/tools/{book-chapter.js, maclane-chapter.js,
   file_chapter.py, resolve_chapter_deps.py, validate_drafts.py}
   (on the user's disk, survives reboot). To resume: copy these back to
   a scratch dir (e.g. scratchpad/books-tools/) and run from there, or
   run in place. book-chapter.js is the book-general workflow (Awodey +
   Seven Sketches); maclane-chapter.js is the frozen MacLane one.
4. Per-chapter cadence (established, unchanged): workflow returns →
   validate_drafts.py <R> <SCRATCH> awodey → eyeball "drafts/covered"
   line → spot-read 1-2 drafts → file_chapter.py <R> <SCRATCH> awodey →
   refresh awodey/filed-issues.tsv → resolve_chapter_deps.py <R>
   <SCRATCH> awodey → persist to doc/plan/books/awodey/ → fess-auditor
   audit ALONE (MAX-2 serial rule; INCLUDE the absolute PDF path
   /Users/johnw/dl/Awodey_Category_Theory.pdf in the brief so the
   auditor can do primary-source completeness) → fold findings → next
   chapter.
5. Remaining Awodey chapters (all +9): Ch5 102-135; Ch6
   "Exponentials" 136-159; Ch7 "Functors and Naturality" 160-199; Ch8
   "Categories of Diagrams" 200-221; Ch9 "Adjoints" 222-273; Ch10
   "Monads and algebras" 274-303. Section printed-pages: pull from
   doc/plan/books/awodey/pagemap.md TOC (subtract 9 from the PDF anchors
   the pagemap lists in parens).
6. After Awodey Ch10: SEVEN SKETCHES. FIRST run its A0 calibration
   (never done — sketches-a0 was stopped at campaign start). PDF
   /Users/johnw/dl/Spivak_Fong_Seven_Sketches.pdf (353pp). Then per-
   chapter pipeline with book:{id:"seven-sketches",name:"Seven
   Sketches",project:6, priorBooks:["maclane","awodey"], scan:false,
   ...}. Create doc/plan/books/seven-sketches/{filed-issues.tsv (empty),
   issue-map.json ({}), inventory,coverage,issues dirs} + a pagemap.
7. FULL remaining-scope roadmap + verification: ~/dl/books-catalog-remaining-plan.md
   (written at halt).

## Status (campaign 3) — TOP-LEVEL BOOK PROGRESS
- BOOK 1 MACLANE: ✅ DONE — 424 issues #216-#639, all 13 units audited
  HONEST, 970 ledger rows, 6 library defects placed. Project 4.
- BOOK 2 AWODEY: IN PROGRESS. Ch 4 ✅ DONE THROUGH G (Groups and
  categories): 27 items, 5 new #664-#668 + 11 cross-book dedups (Grp-
  heavy → #343/#313/#301/#299/#234/#341), 6 dep edges (transient
  #665<-#664 confirmed present). CLOSURE-TRACKING RULE live: 7/11
  appends carry the new "- [ ]" checkbox. Schema enum extended with
  'example' (Awodey uses it as a first-class numbered env) — stops the
  recurring inventory flag. No new library defects. 461 issues, 1133
  ledger.
  ### fess-aw4 VERDICT: **HONEST**, all 6 claims confirmed. CLOSURE-
  TRACKING rule verified correct (7 checkboxes each a genuine DoD-absent
  increment — cleanest: cor5→#313 adds the FIRST iso theorem G/ker≅im
  which #313's DoD lacked; 4 omissions correct exact folds). Internal
  GroupObject vs concrete-Grp handled correctly (#667/#668 depend on
  #343 which will assemble Grp(C)). 3 LOW: L2 edge count is 5 DISTINCT
  native (6 trailer lines — #665's 2 item-id deps both → #664 collapse);
  L3 def-representation→#234 checkbox thin (overlaps #234 DoD, hedged —
  left as-is); L4 def-kernel PRESENT generous-but-defensible (kernel=
  equalizer-of-zero, definition item). ⚠ L1 PROCESS FIX: the auditor
  could NOT read the Awodey PDF for primary-source completeness — I
  omitted the absolute path from the brief and it searched the repo
  (PDF is at /Users/johnw/dl/Awodey_Category_Theory.pdf; the path IS in
  the pagemap header but the auditor didn't extract it). FIX: every
  future audit brief MUST state the absolute PDF path explicitly for the
  page-image completeness check. Ch4 CLOSED. Ch5 LAUNCHING.
  Ch5 args: roman "5" title "Limits and colimits" PDF 102-135 offset 9
  splitAt 118 sections [5.1 Subobjects pr93, 5.2 Pullbacks pr96, 5.3
  Properties of pullbacks pr101, 5.4 Limits pr107, 5.5 Preservation of
  limits pr112, 5.6 Colimits pr115, 5.7 Exercises pr124]. BIG chapter
  (~34 PDF pages) — expect many items; the library has strong limits/
  pullbacks/colimits coverage so heavy PRESENT/PARTIAL + dedups.
- BOOK 2 AWODEY: Ch 3 ✅ DONE THROUGH G (Duality): 36
  items, 6 new #658-#663 + 18 cross-book dedups (all MacLane — duality
  chapter overlaps heavily), 6 dep edges, only re-flagged [Ord] defect
  (A2, already recorded). 456 issues, 1106 ledger. Full agent set
  RESTORED globally (fess-auditor etc. back).
  ### fess-aw3 VERDICT: **HONEST**, all 8 claims confirmed. DUALITY/
  VARIANCE FOLDS LEGITIMATE — auditor opened #422, confirmed its body
  scopes "and dually for colimits", so the coproduct-in-poset→product-
  in-preorder fold is correct + variance-aware. MULTI-PART held. #658 =
  genuine COPRODUCT bifunctor (InternalCoproductFunctor 0 hits in-tree).
  0 false-PRESENT. 2 LOW: L1 label/project brief-wording (benign). L2
  SYSTEMIC (acted on): "new aspect" folded as append-prose isn't in the
  target's DoD checklist → could be lost if the host issue closes on its
  original DoD. FIX: added CLOSURE-TRACKING RULE to book-chapter.js
  draftPrompt (Ch4+) — appends adding a NEW formalizable aspect must
  include a "- [ ] (from Book §sec) <aspect>" checkbox unless the target
  DoD already scopes it. Ch1-3 appends stay prose-only (LOW, disclosed,
  non-fault per auditor; retrofit is an optional scripted pass later).
  Ch3 CLOSED. Ch4 LAUNCHING.
  Ch4 args: roman "4" title "Groups and categories" PDF 88-101 offset 9
  splitAt 94 sections [4.1 Groups in a category pr79, 4.2 The category
  of groups pr83, 4.3 Groups as categories pr86, 4.4 Finitely presented
  categories pr89, 4.5 Exercises pr91].
- BOOK 2 AWODEY: Ch 2 ✅ DONE + fess HONEST (zero
  findings): 51 items, 10 new #648-#657 + 10 cross-book dedups (all
  obligation-matched), MULTI-PART RULE HELD (ex2 a-d, ex7 a-b all land
  in real obligations), 6 dep edges, 2 defects placed (A3→#247, A4
  recorded). 450 issues total, 1070 ledger rows. fess-auditor RESTORE
  confirmed hot-reloading. Ch3 LAUNCHING.
- BOOK 2 AWODEY: Ch 1 ✅ DONE THROUGH G (2026-07-23,
  wf_c16a1644-008): 49 items, 0 OVERTURNS, 21 PARTIAL/ABSENT → 8 NEW
  issues #640-#647 + **12 CROSS-BOOK dedups to MacLane** (validating the
  whole cross-book premise: matrix#221, monoid-1obj#220, group-hom Grp
  #255, free-monoid#296×3, foundations#253×2, pointed-sets#262, etc.);
  each MacLane target ALSO added to project 5 (GitHub dedups cards by
  URL — 17 items in proj 5, no dupes). 28 PRESENT. 3 dep edges (incl.
  cross-book #643→#255, #644→#263) GRAPH CLEAN. Ledger 1019. fess-aw1
  launching ALONE.
  ### TOOLING FIXES this chapter (all pre-filing, caught by validate):
  * validate_drafts.py: project check was hardcoded "4" → now PROJECT
    map per book; filed-deps check now unions ALL books' filed-issues
    (cross-book deps reference prior books).
  * file_chapter.py: added `associated` set so a cross-book target hit
    by MULTIPLE items this chapter is added to the project ONCE (GitHub
    dedups anyway, but avoids wasted API calls).
  * resolve_chapter_deps.py bare-item-id token-replace (App #638 fix)
    confirmed working on Awodey #645.
  2 LIBRARY-DEFECTS (dangling [Pos]/[Ord] refs in Instance/Poset.v:21,
  Proset.v:19) → doc/plan/books/awodey/library-defects.md; [Pos] rides
  #641 (builds Pos). Drafter under-counted the scan again (MacLane-ChV
  pattern) — closeout grep caught them.
  Project 5. 10 chapters, uniform +9, born-digital, no appendix.
  ### fess-aw1 VERDICT: **HONEST**, all 8 claims confirmed. CROSS-BOOK
  DEDUP (the priority) SOUND — auditor opened all 9 target MacLane
  issues, confirmed genuine obligation-match (not title-match), live
  appends, dual project association. Pos new-issue call sound. 2 LOW
  carry-forwards for Awodey Ch2-10: (L1) drafter defect-scan
  under-counts → the closeout grep over verified-*.json IS the source of
  truth (keep doing it). (L2) multi-part items deduped into single-topic
  issues leave non-matching parts as prose-only → ADDRESSED: added a
  MULTI-PART RULE to book-chapter.js draftPrompt (non-matching
  formalizable parts get their own small issue or deps_pending, never
  append-only prose). Ch1 CLOSED.
  ### Awodey Ch 2 LAUNCHING (audit done): "Abstract structures", PDF
  40-65, offset +9, splitAt 52, sections printed [2.1 Epis/monos 31,
  2.2 Initial/terminal 35, 2.3 Generalized elements 37, 2.4 Sections/
  retractions 40, 2.5 Products 42, 2.6 Examples of products 45, 2.7
  Categories with products 50, 2.8 Hom-sets 52, 2.9 Exercises 55]. Same
  AWODEY_BOOK config. On return: cadence (validate w/ book=awodey, file,
  refresh awodey/filed-issues.tsv, resolve, persist, general-purpose
  audit alone).
- BOOK 3 SEVEN SKETCHES: NOT STARTED (A0 calibration not yet run —
  MUST run sketches-a0 first; project 6; priorBooks maclane+awodey).

## Status (campaign 3)
- [x] Infra DONE: 6 labels (book:maclane/awodey/seven-sketches,
      coverage-gap, kind:theory, kind:exercise) + Projects v2 created:
      MacLane=#4 (PVT_kwHNIQzOAXhnTQ), Awodey=#5 (PVT_kwHNIQzOAXhnUA),
      Seven Sketches=#6 (PVT_kwHNIQzOAXhnUw), all under users/jwiegley.
- [~] MacLane: Ch I PILOT COMPLETE THROUGH G (2026-07-22), H (fess) in
      flight (agent fess-ch1). Results: wf_88ef8089-28b (24 agents, 0
      errors, 3.3M tokens): 116 items inventoried (per-page accounting
      clean), 10/10 coverage batches verified (2 overturns: I.6:def3→
      PRESENT via Instance/Comp.v:382 Group; I.4:ex1 PRESENT→PARTIAL),
      final split 83 PARTIAL/ABSENT → 50 issues FILED #216-#265, all in
      project 4, labels set, 61 links verified, deps resolved to #N (38
      edges, graph clean) + native blocked-by mirrored, ledger rows for
      all 116 items. Artifacts persisted: doc/plan/books/maclane/
      {inventory/I.json, coverage/verified-I-*.json, issues/I-drafts.md}.
      Filing/dep scripts (idempotent, reusable for Ch II+):
      scratchpad/maclane-ch1/{file_issues.py,resolve_deps.py} + issue-map.json.
      BONUS findings for later triage: vacuous identity_law TODO in both
      Metacategory files (captured in #217); dangling [Ord]/[Pos] prose
      refs (Proset.v:19, Poset.v:22) — doc hygiene, not filed as issues.
      Drafter judgment calls accepted + disclosed in-issue (Lie-algebra
      descope #232, Freyd non-concreteness scope-out #263, choice-free
      constructive scoping #245/#246, doc-grade #253, umbrella #226).
      fess AUDIT PASSED (2026-07-22): VERDICT HONEST — all 7 claims
      confirmed (contract/graph/ledger/project/links exhaustively;
      classification/evidence/paraphrase/completeness at-or-above sample
      sizes); zero blocking findings. Folded: ledger PRESENT rows now
      carry evidence pointers (finding 2, 33 rows fixed). DECIDED
      (finding 1): keep the single dominant-kind label — contract reads
      singular; consistency over relabeling. doc/observations/ empty.
      **PILOT CLOSED — rails validated.**
      SAME-BOOK DEDUP RULE for Ch II+ (obligation-normalized, plan §Dedup
      extended in spirit): the drafter consults ledger.tsv + issue-map +
      filed titles; an item whose obligation is already covered by a
      filed issue is NOT re-drafted — it returns a duplicates list
      (item-id → issue# + a source block to append); the main loop
      appends the source ref to the existing issue body, extends its
      trailer ids, adds the ledger row with that issue#. Cross-chapter
      deps on FILED issues are written directly as "Depends on: #N";
      same-chapter deps stay item-ids for Phase G.
      NEXT: scale A→H chapter-by-chapter (II, III, ..., XII, App) — one
      generalized workflow per chapter (scripts/maclane-chapter.js via
      args), F/G/H in main loop between chapters, per-chapter fess.
- Ch II ✅ COMPLETE THROUGH G (2026-07-22, resumed run wf_376d6626-6d6
  finished 20/20 agents, 0 errors): 98 items (merge fixed an inventory
  ID collision II.5:construction1 A-vs-B, renamed B→construction2 +
  cross_refs), 96 records verified ALL CONFIRMED (0 overturns), 64
  PARTIAL/ABSENT → 36 issues FILED #266-#301 + 4 dedup append-blocks
  applied to #221/#227/#237/#260 (consensus amendment 2 in action), 28
  dep edges resolved+mirrored (incl. cross-chapter deps on Ch I issues,
  e.g. #280 R-Mod → #256 Ab, #264 Ab-categories), GRAPH CLEAN. Ledger
  215 rows; issue map 147 items; filed-issues.tsv 86. Artifacts
  persisted (inventory/II.json, coverage/verified-II-*, issues/
  II-drafts.md + II-duplicates.json). fess audit PASSED: HONEST with
  ONE MEDIUM (5 dep body lines unrewritten — drafter appended trailing
  prose after the item-id, rewrite regex required EOL; FIXED: #271→#277,
  #286→#285, #288→#285, #289→#277, #300→#299, all verified; script
  regex hardened to `\b.*$` in resolve_chapter_deps.py) + one INFO
  (record count is 98, not 96 — narrative slip, artifacts consistent).
  Native relations + trailers were complete throughout (verified via
  REST dependencies endpoint by the auditor). Do NOT re-audit the fix.
- Ch III ✅ COMPLETE THROUGH G (2026-07-22, wf_fc79c381-ba1, 22/22
  agents 0 errors): 104 items (merge folded a range-B ID collision into
  III.3:remark4), 103 CONFIRMED + 1 OVERTURNED (III.6:ex4
  PARTIAL→ABSENT, internally inconsistent record), 65 PARTIAL/ABSENT →
  45 issues FILED #302-#346 + 1 append to #254 (III.4:ex2 Top
  extension), 46 dep edges resolved+mirrored GRAPH CLEAN (hubs emerging:
  #345 category-of-elements ← #319/#346; #339 pointwise products ←
  #341/#342; Ch-I host-category deps heavily reused). Ledger 319 rows;
  212 items mapped; 131 filed issues. Drafter replaced two 404 nLab
  slugs with a verified Wikipedia link (link discipline working).
  Artifacts persisted (inventory/III.json, coverage/verified-III-*,
  issues/III-drafts.md + III-duplicates.json). Validator factored to
  books-tools/validate_drafts.py <R> <SCRATCH>. fess PASSED: HONEST,
  ZERO findings (8/24 pages re-read incl. both collision pages; 6
  PRESENT re-derived in code incl. the aggressive III.3:ex6 dual-reading
  call — upheld; dep-line regression ZERO hits; #344 overturn applied
  correctly; #254 append intact; graph/native exact 46/46 match; the
  early regression-scan alarm was STALE SCRATCHPAD FILES, fresh fetches
  clean). One informational note folded forward: drafter prompt now
  bans bare item IDs in issue PROSE (script edited post-audit — safe,
  Ch IV is a fresh run so no cache impact).
  Ch III audit CLOSED — do not re-audit.
## ⚠ MODEL SWITCH (2026-07-22): Fable 5 credits EXHAUSTED
- Ch IV run wf_5655b02f-ca5 got 21/22 agents through; ONLY [draft:IV]
  failed: "You're out of usage credits ... Fable 5". All inventory/
  coverage/verify artifacts (107 records) are on disk + cached.
- User switched the MAIN LOOP to claude-opus-4-8[1m] via /model and
  directed: **use claude-opus-4-8 for all future sub-agents**.
- Script now sets `const MODEL = 'opus'`; applied to the draft call
  (cache-safe: last agent) for the Ch IV resume w9ocbo832. EXTEND
  `model: MODEL` to EVERY agent() call before launching Ch V (fresh
  run, no cache to protect).
- ✅ ANSWERED (2026-07-22): the user edited
  /Users/johnw/.claude/settings.json to CLAUDE_CODE_SUBAGENT_MODEL=
  claude-opus-4-8, and agents picked it up **LIVE, WITHOUT A RESTART**
  — every agent spawned from 12:23 onward logs
  "model":"claude-opus-4-8", including coverage/verify agents that carry
  NO per-agent override. **This CONTRADICTS the campaign-1 lesson**
  ("env pin read at startup only; per-agent model: ignored"). Harness
  behavior has changed: the pin is re-read live and governs. Practical
  consequence: no restart needed to switch subagent models; the
  explicit `model: MODEL` in opts is now belt-and-braces, not required.
- ⚠ RESUME LESSON (costly, record for every future resume of this
  pipeline): resuming wf_5655b02f-ca5 replayed ONLY the 3 pre-pipeline
  agents (inv A, inv B, merge — files untouched since 10:50-10:52) and
  RE-RAN the whole coverage+verify pipeline on Opus (coverage-IV-5..8
  and verified-IV-0..3 rewritten 12:23-13:05). Cause: the workflow
  cache matches a PREFIX of agent() calls by invocation order, and the
  MAX=2 semaphore + pipeline() interleaving makes that order
  nondeterministic between runs — once the order diverges, everything
  after re-runs. So a resume of a chapter that died late costs roughly
  a full re-run of the pipeline stages. Budget for it; prefer letting a
  chapter finish over resuming mid-pipeline. (Artifacts stay coherent:
  all 18 coverage/verified files are rewritten before the draft runs.)
## ⚠ MODEL-QUALITY FACT (user correction, 2026-07-22)
**Fable 5 is the STRONGER model; Opus 4.8 is the weaker one.** So the
forced switch (Fable credits exhausted) is a DOWNGRADE for the
classification/verification stages, not an upgrade. Ch I-III were
verified on Fable; Ch IV onward, and both remaining books, will be
Opus — a provenance difference to disclose, not paper over.
- SALVAGE DONE: Fable-era Ch IV artifacts preserved in
  scratchpad/maclane-ch4/fable-era-backup/ — inventory (A/B/merged, all
  3 still Fable on disk since the cache replayed them), coverage-IV-0..4,
  and verified-IV-0/3/5 (5 survived on disk; 0 and 3 RECOVERED from the
  agent transcripts' Write tool calls). verified-IV-1/2/4/6/7/8 were
  overwritten and are NOT recoverable (those agents built their JSON via
  helper scripts rather than a single Write, so no full content blob is
  in the transcript).
- CROSS-MODEL QA OPPORTUNITY: batches 0, 3, 5 now exist in BOTH Fable
  and Opus versions over identical items. At Ch IV closeout, diff the
  classifications to measure whether the downgrade changes verdicts;
  report the agreement rate to the user as evidence for how much to
  trust Opus-era chapters. If material divergence appears, raise it
  before filing more chapters.
## Ch IV ✅ COMPLETE THROUGH G (2026-07-22, wf_5655b02f-ca5 resumed,
22/22 agents 0 errors, Opus-era coverage/verify)
- 107 items; 3 OVERTURNS, ALL false-PRESENT catches (IV.1:construction3,
  IV.1:ex1, +1) → the weaker model still hunted false-PRESENTs well.
- 82 PARTIAL/ABSENT → 59 issues FILED #347-#405 + 5 append-blocks
  (#239, #266, #305, #310, #312). 24 PRESENT + 1 OUT_OF_SCOPE issue-free.
- 90 dep edges resolved + native-mirrored, GRAPH CLEAN (largest yet;
  heavy cross-chapter blocking on the Ch-I concrete categories
  #255-#259 — a big Ch IV sub-cluster stays blocked until those land;
  worth reflecting in project ordering).
- **CROSS-MODEL RESULT: 36/37 (97%) identical final classifications**
  between Fable- and Opus-verified versions of batches 0/3/5. The ONE
  divergence (IV.1:construction3) went Fable PRESENT → Opus PARTIAL —
  i.e. the weaker model was STRICTER, erring toward cataloguing work
  rather than silently dropping it (the safe direction). Evidence that
  continuing on Opus is acceptable; fess-ch4 is independently checking
  the batches with no Fable counterpart.
- ⚠ TOOLING DEFECT CAUGHT PRE-FILING (would have silently voided 47
  issues' dependency graphs): this drafter emitted BULLETED
  "- Depends on: #N" lines; Ch I-III used the bare form, and both
  validate_drafts.py and resolve_chapter_deps.py matched only `^Depends
  on:`. Both regexes are now bullet-tolerant (and the resolver
  preserves the bullet when rewriting). LESSON: drafter output format
  drifts between runs — always confirm the validator's "filed deps
  referenced" count is non-zero and plausible BEFORE filing.
- Artifacts persisted incl. coverage/fable-era-ch4/ (the salvaged
  stronger-model set, for future cross-model QA).
- ✅ fess-ch4 VERDICT: **HONEST**, all 7 claims confirmed, findings all
  LOW/INFO. It independently recomputed the cross-model figure (36/37)
  AND extended it: Phase-C fable vs Opus final = 61/63 (96.8%), and
  **across all 63 comparable items Opus was stricter 3×, looser 0×** —
  the failure mode a downgrade would cause does not occur. It
  re-derived ALL SIX PRESENT items in the unmeasured batches 6/7/8 and
  all held. **JUDGMENT: continue the campaign on Opus.**
  Mechanical sweeps: 198 citations 0 bad, 48/48 symbols at cited lines,
  90/90 native edges = body edges, 294/294 map/ledger agreement,
  0 contract failures in 59, 5 appends byte-identical apart from the
  trailer ids. The lone OUT_OF_SCOPE (Pontryagin/Gelfand-Naimark) was
  judged correct and sparing.
  ### Findings FOLDED THIS TURN
  - LOW-1 (real library defect, independently re-verified by me):
    Instance/Adjoints.v:32-36 + :82-83 claim the LEFT adjoint is the
    forward direction, but adj_morphism:84-88 has free_functor : D ⟶ C
    and forgetful_functor : C ⟶ D, so arrows run along the RIGHT
    adjoint. APPENDED to issue #395 as a defect note + DoD item.
  - LOW-2: verified-IV-7.json's "all disclosed in-file" was the one
    factually wrong sentence in the Ch IV artifacts — CORRECTED in both
    the scratch and persisted copies.
  - LOW-3 (campaign-wide, fixed FORWARD): overturns overwrote
    `classification`, destroying Phase-C provenance (Ch IV's third
    overturn IV.7:ex4 is now unrecoverable). verPrompt now requires
    `phase_c_classification` on every overturn.
  - LOW-4 (fixed FORWARD): trailers held only intra-chapter deps
    (41/90 for Ch IV), so a trailer-only validator sees a partial
    graph. draftPrompt now requires the trailer deps array to carry
    cross-chapter "#N" edges too. Body lines remain source of truth
    per the frozen plan, and I validate from bodies.
  - STRUCTURAL BLIND SPOT the auditor named (fixed FORWARD): "defects
    discovered while confirming a PRESENT have no issue to ride on."
    verPrompt now has a LIBRARY-DEFECT channel; draftPrompt must place
    each one in a DoD or report it as UNPLACED.
  - INFO-1 — CORRECTION TO MY OWN EARLIER SUMMARY: I wrote "three
    documentation overclaims". Accurate count is **one** genuine false
    claim (Structure/Pullback.v:129-130 says the base-change adjunction
    is built in Construction/Slice/Pullback.v; that code is commented
    out AND mis-oriented) plus **two** accurate-but-unproved prose
    statements (Construction/Slice.v:88-90, Instance/Fun.v:104-106).
    The filed issues #387/#392 word it correctly; only my summary was
    inflated.
  ### ✅ Ch V HALT RESOLVED — ROOT CAUSE WAS A STALE MODEL PIN
  (2026-07-22). Diagnosis: during the failed run, settings.json STILL
  read CLAUDE_CODE_SUBAGENT_MODEL="claude-fable-5" (the earlier edit had
  not landed). Agent transcripts prove SPLIT ROUTING: the 6 agents that
  completed logged claude-opus-4-8; the 10 that failed are <synthetic>
  failure records carrying the Fable out-of-credits message. So this was
  NOT account-level exhaustion — it was some agents still being routed
  to the credit-dry Fable pool. The user re-edited settings.json (now
  "claude-opus-4-8", verified by grep) and said to continue.
  RELAUNCHED as resume wf_769e04f9-439 / task wxa6srqkc — resume chosen
  over fresh because it can only save work (the 3 page-image inventory
  agents + merge cache; coverage/verify re-run either way).
  LESSON: when subagents fail with an out-of-credits message naming a
  model you believe is unused, VERIFY the pin with grep on
  /Users/johnw/.claude/settings.json and check per-agent "model" fields
  in the workflow transcripts BEFORE concluding the account is dry — a
  stale pin looks exactly like exhaustion, and the tell is split
  routing (some agents succeed on the intended model).
  ### Ch V ✅ COMPLETE THROUGH G (2026-07-22, resume wf_769e04f9-439
  task wxa6srqkc, 24/24 agents 0 errors, Opus)
  - 116 items; 1 OVERTURN (carries phase_c_classification ✓ — hardened
    behavior A works). 104 PARTIAL/ABSENT → 57 issues FILED #406-#462 +
    3 append-blocks (#239, #329, #353). 12 PRESENT, 0 OUT_OF_SCOPE.
  - 87 dep edges (CORRECTED from my "88" per fess F1 — the resolver
    printed "edges: 88" but one was the false-alarm retry double-count;
    GitHub blocked_by shows 87 relations from the 57 new issues, +3
    pre-existing on append targets = 90 total). GRAPH CLEAN, native =
    trailer edges exactly. ~30 issues gated on the Ch-I host categories
    #255-#259; all of V.9 (topology) waits on Top #259.
  - HARDENED PROMPTS — all 3 behaviors verified live: (A) overturn
    carries phase_c_classification; (B) LIBRARY-DEFECT channel produced
    23 flags collapsing to 2 distinct defects — the Comma "creates the
    limits" overclaim folded into #438's DoD (drafter: "No UNPLACED"),
    but the drafter UNDER-COUNTED and MISSED the 3rd (Omega.v:13 garbled
    xref, trivial cosmetic); (C) trailers carry cross-chapter #N deps.
  - LIBRARY-DEFECTS LEDGER started: doc/plan/books/maclane/
    library-defects.md — 3 defects recorded (Adjoints.v→#395,
    Comma→#438, Omega.v:13→no home/cosmetic) + the Ch IV prose-claim
    notes. These are side-findings, NOT coverage-gap issues; filing them
    is a maintainer call. LESSON: the drafter's LIBRARY-DEFECT scan can
    under-count when defects appear in only one batch's problems[];
    at closeout, grep verified-*.json for LIBRARY-DEFECT and reconcile
    against what landed (I do this into library-defects.md).
  - Artifacts persisted. Ledger 542 rows; 398 items mapped; 247 filed.
  - fess-ch5 VERDICT: **HONEST**, all 8 claims verified, all 3 hardened
    behaviors CONFIRMED working. AFT/SAFT honesty (the priority risk)
    SOUND — issues correctly separate GAFT sufficiency (PARTIAL) from
    missing necessity/characterization (the real gap); no GAFT misread.
    3 findings, all LOW/INFO, folded: F1 edge count 88→87 (corrected
    above); F2 a 4th library defect (Equalizer.v:78-92 "both arguments
    run in this library" over-claim) added to library-defects.md +
    #416's DoD citation widened :80→:78-92; F3 (#436 loose connective
    prose, classification correct) — ACKNOWLEDGED, left as-is (cosmetic
    prose in a filed issue, not worth a gh round-trip; noted here). The
    auditor independently re-derived the substantive-defect handling as
    COMPLETE (Comma→#438, Equalizer→#416, Omega→doc; the other
    defect-keyword hits correctly judged non-defects). Ch V CLOSED.
- Ch VI ✅ COMPLETE THROUGH G (2026-07-22, wf_bc1f425a-846, 16/16
  agents 0 errors, Opus): 69 items, 0 OVERTURNS (all 6 batches
  blind-confirmed), 53 PARTIAL/ABSENT → 27 issues FILED #463-#489, 0
  dups (first monad chapter). 36 dep edges + native mirror GRAPH CLEAN.
  16 PRESENT, 0 OUT_OF_SCOPE. Ledger 611; 451 mapped; 274 filed.
  Monadicity flagship theorems verified genuinely proven (verifiers:
  no Admitted/Axiom in Monad/Monadicity/*), classified as sufficiency
  with the missing pieces (absolute clause, iso-not-equiv conclusion,
  general converse, CTT/VTT/PTT vocab) honestly gapped. NO library
  defects this chapter (headers held).
  ### SCAN-ARTIFACT RECOVERY (VI.6:ex2 → #480): inventory flagged the
  item statement-illegible (garbled Beck contractible-pair 2nd equation
  as non-composable "d1.t=d0.d1"). MAIN LOOP re-read PDF 159, recovered
  the real statement (∂₀t=1, ∂₁t∂₀=∂₁t∂₁; contractible pair, parts (a)
  split-fork⇒contractible, (b) contractible+has-coeq⇒split), EDITED the
  draft to state it precisely + removed the "confirm against clean
  source" hedges before filing. ABSENT is correct (no in-tree
  contractible-parallel-pair notion). This is the illegibility re-read
  protocol working end to end. LESSON: when inventory flags
  statement-illegible, the main loop MUST re-read that PDF page before
  filing that item's issue — the flag propagates but the fix is
  main-loop-only (agents can't re-read reliably enough).
  ### TOOLING: 2nd drafter format drift — BARE YAML headers (no ```yaml
  fence, fields until a blank line then body). Made all 3 tools
  (validate/file/resolve) tolerant of BOTH fenced and bare via a shared
  split_draft() helper. Drift history: Ch IV bulleted deps; Ch VI bare
  YAML. ALWAYS run validate_drafts.py and eyeball the "drafts:N /
  covered:M" line before filing — a parse regression shows up there as
  0 covered.
  fess-ch6 VERDICT: **HONEST**, all 8 claims confirmed. Monadicity
  honesty CLEAN — auditor re-derived 5 VI.6-VI.8 gaps against
  Monad/Monadicity/* (all real: no Absolute* predicate, beck_monadicity
  concludes Equivalence not iso, converse only at U^T, no CTT/VTT/PTT
  vocab), grepped ZERO Admitted/Axiom/Parameter across all monadicity/
  EM/Kleisli/Coequalizer files, no proven theorem mis-marked ABSENT, no
  false-PRESENT in 7 re-derived. #480 CONFIRMED matches PDF 159 verbatim
  (auditor read the page). Bare-YAML parse: 0/27 YAML leak, 0/27
  residual maclane dep-lines. 3 findings: F1 LOW (inventory VI.json:74
  still had the garbled equation + stale illegible flag — the recovery
  reached draft/#480 but not the intermediate artifact) → FIXED, both
  the persisted and scratch inventory-VI.json patched with the recovered
  equation, illegible flag cleared. F2/F3 INFORMATIONAL (Monadic=
  equivalence-variant, defensible + iso-gap tracked by #484; def3/def4
  share the SplitCoequalizer witness) — no action. Ch VI CLOSED.
  LESSON: the illegibility re-read fix must ALSO back-propagate to
  inventory/<R>.json, not just the draft — add to closeout when any
  statement-illegible flag was resolved.
- Ch VII ✅ COMPLETE THROUGH G (2026-07-23, wf_0bf12a4b-5d2, 18/18
  agents 0 errors, Opus, offset +8): 89 items, 0 OVERTURNS. Tally
  (fess-corrected): 67 ABSENT + 10 PARTIAL = 77 non-PRESENT → 76 by
  the 40 issues #490-#529 + 1 (VII.1:remark1) by the #265 append; 12
  PRESENT, 0 OUT_OF_SCOPE; 6 verifier OOS→ABSENT overturns in VII.8/9
  (all issued). 47 DISTINCT native edges (48 dep-LINES — #507 lists
  #505 twice; GitHub dedupes) + native mirror GRAPH CLEAN (transient
  #507<-#505 false alarm, confirmed present). Ledger 700; 528 mapped;
  314 filed.
  ### SCAN-ARTIFACT RECOVERY #2 (VII.9:ex3 → #527): inventory flagged
  smash-vs-product ambiguity; main loop re-read PDF 198 → operator is
  × (cartesian product, "- × Y in Top_* has no right adjoint, fails to
  preserve coproducts"), NOT smash ∧. Draft edited to name - × Y + the
  ×-not-∧-is-closed contrast; inventory back-propagated (flag cleared,
  BOTH scratch + would-persist). Also fixed 2 broken cross_refs at
  merge (VII.5:thm1→VII.5:prop1). No hard library defects (the
  Structure/Monoid.v:73-74 "provable at this generality" essay is
  conditional prose, verifier judged non-defect).
  ### fess-ch7 VERDICT: **HONEST**. Coherence honestly ABSENT (proven
  Kelly/pentagon lemmas are consequences, not the general theorem —
  auditor drew the same line, confirmed VII.1:ex1 PRESENT vs VII.2:cor1
  ABSENT is the right split); monoid PRESENT calls real; #527 ×-not-∧
  verified against PDF 198. 0 false-PRESENT in 12 re-derived. All 3
  findings COSMETIC count nits (F1 77 not 76; F2 47 distinct edges not
  48; F3 6 overturns not 7) — corrected in the tally above; NO issue/
  graph/classification change warranted. Ch VII CLOSED.
  ### Ch VIII: 13/14 agents done + cached (wf_fdc9b927-d49); 63 items,
  all inventory/coverage/verify complete on disk. ONLY [draft:VIII]
  failed — TRANSIENT API error ("Connection closed mid-response"), NOT
  credits/model. RESUMED as wh142f1cn (draft re-runs; coverage/verify
  may re-run per the prefix-cache lesson — harmless, outputs exist).
  Notable coverage: library additive spine is real (6+ PRESENT in
  VIII.1-2: pzero_zero_mor, Additive class, biproduct_addition), gaps
  honestly stated (no additive-functor notion anywhere; no
  cocartesian⇒biproduct leg; no n-ary biproduct; VIII.4 diagram lemmas
  = the honesty crux). LIBRARY-DEFECT flagged (minor): Construction/
  Enriched.v:107-108 calls Preadditive "Ab-enriched" but it is
  CMon-enriched (negatives omitted; only Additive is Ab-enriched) —
  capture in library-defects.md at closeout. VIII.4:remark-embedding
  (Lubkin-Freyd-Mitchell) surfaced from the Notes block, flagged
  candidate-not-firm.
  ### Ch VIII ✅ COMPLETE THROUGH G (2026-07-23, resumed
  wf_fdc9b927-d49→wh142f1cn after a transient API drop on draft:VIII):
  63 items, 0 OVERTURNS, 53 PARTIAL/ABSENT → 29 issues FILED #530-#558
  + 2 append to #264 (VIII.2:def1/def4 additive-functor). 10 PRESENT,
  0 OUT_OF_SCOPE. 29 dep edges + native mirror GRAPH CLEAN. Ledger 763;
  581 mapped; 343 filed. DIAGRAM-LEMMA CRUX resolved honestly: the whole
  member calculus (exactness, chain complexes, homology, Ext,
  Freyd-Mitchell embedding, 5/snake/3x3 lemmas) is ABSENT; thm3 PARTIAL
  (2 of 6 member rules have faithful shadows monic_iff_kernel_pzero +
  Monic). Abelian class PRESENT-as-definition but never instantiated
  (INHABITATION note). LIBRARY-DEFECT #5 (Enriched.v:107 "Ab-enriched"
  misattribution) → library-defects.md.
  ### 3rd DRAFTER FORMAT DRIFT + ROBUST FIX: this drafter wrote deps as
  BACKTICK-wrapped item-ids, MULTIPLE per "Depends on:" line, MIXED with
  parenthetical forward-refs (`item-id`) that are NOT deps. The prose
  regex was becoming unmaintainable (drift: IV bulleted, VI bare-YAML,
  VIII backtick+multi+refs). FIX: resolve_chapter_deps.py and
  validate_drafts.py now read the AUTHORITATIVE dep set from the catalog
  TRAILER's `deps` array (structured JSON); the prose rewrite is scoped
  to the "## Dependencies" SECTION with trailer deps as a whitelist
  (forward-refs left untouched). Drift-proof — the trailer is
  machine-emitted. Regression: 0 genuinely-unresolved item-id deps
  across #530-#558. LESSON: TRAILER is the dep source of truth now, not
  the prose line.
  ### fess-ch8 VERDICT: **HONEST**. Both priorities clean: additive
  spine honest (Abelian defined-but-never-instantiated caveat correctly
  surfaced in #548/#543; 0 false-PRESENT in 8 re-derived); diagram
  lemmas genuinely ABSENT (member calculus, 5/snake/9 lemmas, homology,
  Ext all confirmed absent by grep+PDF; thm3 PARTIAL cites ONLY the 2
  real shadows, epic_iff_cokernel correctly flagged a DIFFERENT
  statement). TRAILER-DRIVEN DEP RESOLUTION VERIFIED CORRECT: native ==
  trailer == body for all 29; the 5 real forward-refs (#534/#535/#536/
  #544/#550) correctly EXCLUDED from the graph; no bare unresolved deps.
  remark-embedding Notes-extraction judged reasonable (PDF 209 states
  it). 2 cosmetic nits FIXED: #558 "Heron"→"Haron" (match Mac Lane
  p.209 + inventory — book fidelity); library-defects #5 line cite
  :22-23→:20-21. Ch VIII CLOSED.
  ### Ch IX LAUNCHED (audit done): roman IX "Special Limits", PDF
  218-239, offset 7 (+7 BLOCK), splitAt 228, 8 sections. Library HAS
  the coend calculus (Structure/Coend.v, Instance/Sets/{End,Coend}.v,
  Theory/Coend/{Yoneda,Fubini}.v, Profunctor, Day) + filtered/final
  functor material — expect ends/coends PRESENT-heavy with the
  Sets-scoped-vs-abstract nuance (ledger 6 in the phase campaign). On
  return: cadence, then Ch X (Kan Extensions, +7, PDF 240-257).
  ### Ch IX ✅ COMPLETE THROUGH G (2026-07-23, wf_850cd782-c99, 16/16
  agents 0 errors, offset +7): 70 items, 0 OVERTURNS, 65 PARTIAL/ABSENT
  → 26 issues FILED #559-#584 + 5 appends (#450, #396, #514, #420 —
  wait, 5: #450×2, #396, #514, #420). 5 PRESENT, 0 OUT_OF_SCOPE. 28 dep
  TOKENS = 27 DISTINCT native edges (#560←#559 stated twice, GitHub
  dedupes; fess-corrected) + native mirror GRAPH CLEAN (transient
  #560<-#559 false alarm, confirmed present). Ledger 833; 646 mapped;
  369 filed. HONEST SPLIT
  confirmed: ends/coends DEFINITIONS PRESENT (End.v:35, Coend :58,
  inhabited by Sets_End/SetsCoend, wedges IX.4:def1/def3), general-base
  results PARTIAL (Yoneda reduction only representable case; Day DFG
  pieces present, general theorem unassembled), filtered/final-functor
  half entirely ABSENT (no filtered category, no cofinal functor — 1
  tree-wide "filtered" hit is a stream comment). No library defects
  (all IX headers accurate). fess-ch9 launching ALONE.
  ### Ch X args (after fess-ch9): roman X "Kan Extensions", pdfStart
  240, pdfEnd 257, offset 7, splitAt 249, sections (X.1 Adjoints and
  Limits 233; X.2 Weak Universality 235; X.3 The Kan Extension 236;
  X.4 Kan Extensions as Coends 240; X.5 Pointwise Kan Extensions 243;
  X.6 Density 245; X.7 All Concepts Are Kan Extensions 248). Library
  HAS Theory/Kan/Extension.v — expect Kan PRESENT/PARTIAL nuance.
  ### fess-ch9 VERDICT: **HONEST**. Both priority splits confirmed:
  ends/coends PRESENT genuinely inhabited (Sets_End/SetsCoend, no
  admits), 10 PARTIALs honestly Sets-scoped, filtered/final ABSENT
  reproduced (1 tree-wide "filtered" = stream comment). 0 false-PRESENT
  (all 5 re-derived), 0 false-ABSENT. 2 INFO (no action): edge count
  27-distinct-not-28 (fixed above); Dinatural class 0-instances but
  TRANSPARENTLY disclosed in #570 (a definition item; End/Coend/Wedge
  ARE inhabited so coend PRESENT not hollow). Ch IX CLOSED.
  ### Ch X LAUNCHED (audit done): roman X Kan Extensions, PDF 240-257,
  offset 7. On return: cadence, then Ch XI (Symmetry/Braiding, +7,
  PDF 258-273 — library HAS Braided/Symmetric monoidal + braid material)
  then Ch XII (Structures: 2-cats/bicats/internal cats, +7 PDF 274-294
  — library HAS Bicategory/DoubleCategory/Grothendieck) then Appendix
  (Foundations, +6, PDF 295-297).
  ### Ch X ✅ COMPLETE THROUGH G (2026-07-23, wf_03752bcf-41b, 18/18
  agents 0 errors, offset +7): 63 items, 1 OVERTURN (X.3:def2
  PRESENT→PARTIAL, phase_c_classification PRESERVED — hardened behavior
  works; the def hid the missing pointwise-colimit formula). 57
  PARTIAL/ABSENT → 21 issues FILED #585-#605 + 1 append (#353). 5
  PRESENT, 0 OUT_OF_SCOPE. 23 dep edges + native mirror GRAPH CLEAN (no
  transient error this time). Ledger 896; 704 mapped; 390 filed. KAN
  NUANCE honest: universal-property defs PRESENT (LocalRightKan/RightKan
  adjoint/LocalLeftKan/LeftKan, WeaklyInitial thm1), the coend-formula
  BRIDGE + pointwise/density/all-concepts PARTIAL/ABSENT (Kan↔coend
  "a bridge not yet formalized", Theory/Kan/Extension.v:76-79 — verifier
  confirmed honest, not a defect; left_adjoints_preserve Abort'd not
  Admitted). No library defects. fess-ch10 launching ALONE.
  ### Ch XI args (after fess-ch10): roman XI "Symmetry and Braiding in
  Monoidal Categories", pdfStart 258, pdfEnd 273, offset 7, splitAt 265,
  sections (XI.1 Symmetric Monoidal Categories 251; XI.2 Monoidal
  Functors 255; XI.3 Strict Monoidal Categories 257; XI.4 The Braid
  Groups B_n and the Braid Category 260; XI.5 Braided Coherence 263;
  XI.6 Perspectives 266). Library HAS Braided/Symmetric monoidal +
  braid material (Construction/PROP, Instance/.../Braid?) — expect
  PRESENT/PARTIAL; XI.6 Perspectives is prose (likely few/no items).
  ### fess-ch10 VERDICT: **HONEST**, all 8 claims confirmed, 0 defects.
  Kan split honest (5 PRESENT re-derived, all Qed/no-axiom;
  left_adjoints_preserve Abort'd not Admitted — 0 axioms); X.3:def2
  overturn CORRECT (pointwise colimit formula genuinely absent,
  Kan_Colimit 0 hits; phase_c_classification=PRESENT preserved);
  coend-bridge honesty confirmed (auditor read PDF 248 — Mac Lane's
  formula uses copowers, absent in-tree, so X.4 ABSENT is a true gap not
  a coend-infra misread). 1 LOW: X.3:thm1 + X.7:ex3 are generous-but-
  disclosed PARTIALs (both still issued; a strict reader could call
  ABSENT → 13 PARTIAL/45 ABSENT). No action. Ch X CLOSED.
  ### Ch XI ✅ COMPLETE THROUGH G (2026-07-23, wf_c8c77bed-fb2, 8/8
  agents 0 errors, offset +7): 26 items (small ch), 1 OVERTURN
  (XI.3:thm2 coherence PARTIAL→ABSENT — Kelly lemmas are derived
  corollaries of axioms, not the universal metatheorem; phase_c
  preserved), 18 PARTIAL/ABSENT → 11 issues FILED #606-#616 + 3 appends
  (#520 ×2 symmetric-coherence, #497 monoidal-coherence). 8 PRESENT, 0
  OUT_OF_SCOPE. 13 dep edges + native mirror GRAPH CLEAN. Ledger 922;
  722 mapped; 401 filed. HONEST split: symmetric/braided monoidal +
  monoidal-functor DEFS PRESENT; braiding-as-ISO / strictification /
  braid-groups / braided-coherence-theorem PARTIAL/ABSENT (library has
  NO group-by-generators machinery — braid cluster #612-616 all rest on
  that gap). LIBRARY-DEFECT #6 (Braided.v:131 comments braid as ≅ but
  field is bare ~>; LOAD-BEARING — it's why XI.1:def2 is PARTIAL) →
  channel worked END-TO-END: verifier flagged, drafter PLACED it in
  #606's DoD, reported placed. Recorded in library-defects.md.
  fess-ch11 VERDICT: **HONEST**, all 8 claims confirmed. Auditor read
  PDF 268 — Mac Lane's braid content (Artin presentation, B_2≅ℤ,
  Bₙ→Sₙ) genuinely exists → ABSENT is a true gap. XI.3:thm2 overturn
  CORRECT (not under-classification; folded to #497). defect #6 real +
  correctly placed in #606. Braid-group cluster genuinely ABSENT
  (FreeBraided PROP is secretly SYMMETRIC via braid_invol — correctly
  excluded). 2 INFO nits FIXED in #606: Braided/Proofs.v Context
  citation :506→:507; DoD item 4 broadened to also name the header
  essay :21-24 (not just the :132 field comment). Ch XI CLOSED.
  ### Ch XII ✅ COMPLETE THROUGH G (2026-07-23, wf_6c67c314-cdc, 10/10
  agents 0 errors, offset +7): 37 items, 1 OVERTURN (XII.7:construction1
  monoidal-as-one-object-bicat PRESENT→PARTIAL — only forward delooping,
  converse+coherence absent; phase_c preserved), 31 PARTIAL/ABSENT → 20
  issues FILED #617-#636 + 2 appends (#283 2-cat, #217 arrows-only). 6
  PRESENT, 0 OUT_OF_SCOPE. 26 declared deps = 25 DISTINCT native edges
  (#627's def3+def4 both → #626 collapse to 1 relation; fess-corrected)
  + native mirror GRAPH CLEAN (transient #627<-#626 false alarm,
  confirmed present). Ledger 959; 753 mapped; 421 filed. Merge resolved an ID COLLISION (both agents
  numbered XII.4 unnumbered defs from def1 for DIFFERENT items — 5
  distinct, renumbered B into sequence). HONEST: CAT-2-cat/BicatAdjunction/
  Modification/Enriched/OneObject-delooping PRESENT; strict 2-cat/
  2-functor/2-natural PARTIAL (only WEAK 2-structure in-tree); internal
  categories/nerve/simplicial/crossed-modules ABSENT. No library defects.
  **MACLANE MAIN TEXT I-XII COMPLETE.**
  ### fess-ch12 VERDICT: **HONEST**, all 8 claims + 4 priorities
  confirmed. Auditor read PDF 285/288 — offset +7, ID-collision
  resolution (5 distinct XII.4 defs) verified against the page reading
  order; all 6 PRESENT re-derived (Cat_Bicategory, Enriched,
  BicatAdjunction, Modification, Bicategory class, Span); weak-vs-strict
  PARTIALs honest (NO strict 2-cat/2-functor type — rg confirmed);
  XII.7 overturn CORRECT (only forward delooping); internal-cat/nerve/
  crossed-module ABSENT via independent grep (crossed-module = 0 hits).
  2 LOW: edge count 25-distinct-not-26 (fixed above); XII.4:def5
  modification PRESENT is softest-but-principled (notion whose datum is
  strict-or-weak identical, like def1 adjunction) — no action. **ALL 12
  MACLANE CHAPTERS AUDITED HONEST.** Ch XII CLOSED.
  ### APPENDIX ✅ COMPLETE THROUGH G (2026-07-23, wf_2db88a6e-8b5, 6/6
  agents 0 errors, offset +6; the first launch omitted args.scratch —
  caught + relaunched before any bad write): 11 items, 0 OVERTURNS, 7
  PARTIAL/ABSENT → 3 issues FILED #637-#639 + 2 appends (#404, #405
  topos issues). 4 PRESENT (category, ElementaryTopos,
  SubobjectClassifier, power object), 0 OUT_OF_SCOPE. 2 dep edges GRAPH
  CLEAN. Merge repaired 4 dangling cross_refs. No library defects.
  ETCS split honest: topos genus PRESENT, the ETCS differentiae
  (well-pointed/choice/NNO) PARTIAL/ABSENT + unbundled.
  ### fess-app VERDICT: **HONEST**, all 7 claims confirmed (offset +6
  re-verified on PDF 295-297, 4 PRESENT re-derived + FinSet_Topos-
  inhabited, ETCS/choice/NNO PARTIALs honest with precise gaps, 2 ABSENT
  grep-confirmed). 1 LOW defect FIXED: #638 Dependencies prose was
  GARBLED — the resolver's bare-item-id rewrite replaced to END-OF-LINE
  and stranded the trailing clause when the dep prose wrapped across
  physical lines (App-drafts had a multi-line Dependencies paragraph).
  Fixed #638's body; HARDENED resolve_chapter_deps.py: bare-item-id case
  now token-replaces "Depends on: <id>" → "#N (`<id>`)" preserving
  trailing prose (matches the backtick case). This was the auditor's
  explicit carry-into-Awodey risk — CLOSED before book 2. **ALL 13
  MACLANE UNITS AUDITED HONEST.** MacLane book DONE.
  ### ========================================================
  ### MACLANE BOOK ✅ COMPLETE — 424 issues #216-#639, 970 ledger rows,
  ### 760 items mapped, 13/13 units audited HONEST (App audit pending),
  ### 6 library defects placed. Project 4.
  ### ========================================================
  ### AWODEY TRANSITION — TOOLING GENERALIZED + INFRA READY (prepared
  during the fess-app run; no agents spent):
  * NEW book-general workflow: scratchpad/books-tools/book-chapter.js
    (node --check OK). Takes A.book config + per-chapter args. The
    MacLane maclane-chapter.js stays FROZEN (book done). book-chapter.js
    adds: cross-book dedup (drafter reads prior books' filed catalogs
    via BOOK.priorBooks), born-digital-vs-scan note, book-parameterized
    numbering/idnote/cite, labels book:${IDP}, projects [${BOOK.project}].
  * Python tools now take a 3rd BOOK arg (default maclane): file_chapter.py
    <R> <SCRATCH> <BOOK>, resolve_chapter_deps.py <R> <SCRATCH> <BOOK>,
    validate_drafts.py <R> <SCRATCH> <BOOK>. PROJECT map maclane→4,
    awodey→5, seven-sketches→6. issue-map + filed-issues are per-book
    (doc/plan/books/<book>/). file_chapter.py dup branch now ADDS
    cross-book dup targets to THIS book's project (gated on own_issues).
  * Awodey infra: doc/plan/books/awodey/{filed-issues.tsv (empty),
    issue-map.json ({})} created; inventory/coverage/issues dirs exist;
    scratchpad/awodey-ch1 ready. Pagemap: doc/plan/books/awodey/pagemap.md
    (1st-ed CMU pre-print, UNIFORM +9, born-digital, chapter-scoped
    shared counters, NO appendix, 10 chapters).
  ### AWODEY Ch 1 LAUNCH (after fess-app returns) — Workflow(scriptPath:
  books-tools/book-chapter.js, args: {book: AWODEY_BOOK, roman:"1",
  title:"Categories", pdfStart:10, pdfEnd:39, offset:9, splitAt:25,
  sections:[{n:1,name:"Introduction",printed:1},{n:2,name:"Functions of
  sets",printed:3},{n:3,name:"Definition of a category",printed:5},
  {n:4,name:"Examples of categories",printed:6},{n:5,name:"Isomorphisms",
  printed:13},{n:6,name:"Constructions on categories",printed:16},{n:7,
  name:"Free categories",printed:19},{n:8,name:"Foundations: large,
  small, and locally small",printed:26},{n:9,name:"Exercises",
  printed:29}], scratch:".../scratchpad/awodey-ch1"})
  AWODEY_BOOK = {id:"awodey", name:"Awodey", project:5, pdf:"/Users/
  johnw/dl/Awodey_Category_Theory.pdf", cite:"Awodey, Category Theory
  (1st ed., Carnegie Mellon pre-print, September 2005)", scan:false,
  numbering:"Awodey numbers Definition/Proposition/Lemma/Theorem/
  Corollary/Example in ONE shared counter PER CHAPTER (Proposition 2.7 =
  the 7th numbered environment of chapter 2, not section-relative);
  exercises collected in each chapter's final numbered section, numbered
  per chapter with lettered parts; displayed equations use a SEPARATE
  (chapter.number) counter — not item numbers.", idnote:"<chapter>.
  <section> locates the item by page via the pagemap; <kind><n> uses the
  printed kind + the CHAPTER-SCOPED number (Proposition 2.7 in §2.1 ->
  awodey:2.1:prop7). Exercises: awodey:<chapter>:ex<n>. §1.4 'Examples of
  categories' is a plain numbered list, NOT Example environments — record
  each as a construction with a slug id.", priorBooks:["maclane"]}
  After each Awodey chapter: file_chapter.py <R> <SCRATCH> awodey →
  refresh awodey/filed-issues.tsv → resolve_chapter_deps.py <R> <SCRATCH>
  awodey → persist to books/awodey/ → fess (alone). Awodey chapter args
  from pagemap (all +9): Ch2 pdf40-65 pr31-56; Ch3 66-87; Ch4 88-101;
  Ch5 102-135; Ch6 136-159; Ch7 160-199; Ch8 200-221; Ch9 222-273; Ch10
  274-303. Then SEVEN SKETCHES (calibration NOT yet run — must A0 first;
  sketches-a0 was stopped at campaign start; PDF Spivak_Fong, 353pp,
  project 6, priorBooks:["maclane","awodey"]).
  ### APPENDIX args (after fess-ch12): roman "App" — BUT the generalized
  script builds IDs as maclane:<roman>.<section>:... and the Appendix is
  a single unnumbered "Foundations" section whose content is a numbered
  AXIOM LIST (1..N: terminal object, pullbacks, truth, etc., printed
  289-291 = PDF 295-297, offset +6). Use roman "App", ONE section
  {n:1, name:"Foundations", printed:289}, pdfStart 295, pdfEnd 297,
  offset 6, splitAt 296. The inventory agents will produce
  maclane:App.1:* IDs — ACCEPTABLE (App is not a chapter roman but the
  ID scheme still works). Small: ~1 batch. After Appendix: MACLANE BOOK
  DONE → create Awodey filed-issues.tsv (empty), start Awodey Ch 1
  (pagemap: uniform +9, PDF 10-39 = printed 1-30; use a NEW
  awodey-chapter.js or generalize maclane-chapter.js with a book param).
  ### Ch XII args (after fess-ch11): roman XII "Structures in
  Categories", pdfStart 274, pdfEnd 294, offset 7, splitAt 284,
  sections (XII.1 Internal Categories 267; XII.2 The Nerve of a
  Category 270; XII.3 2-Categories 272; XII.4 Operations in
  2-Categories 276; XII.5 Single-Set Categories 279; XII.6 Bicategories
  281; XII.7 Examples of Bicategories 283; XII.8 Crossed Modules and
  Categories in Grp 285). Library HAS Bicategory/DoubleCategory/
  Grothendieck/Displayed — expect a rich PRESENT/PARTIAL mix; the
  bicategory-coherence + internal-category material is the crux.
  Then APPENDIX (Foundations, +6, PDF 295-297, splitAt 296, 1 "section"
  App — its content is a numbered axiom list; use ID maclane:App:*).
  Ch IX args next: roman IX, "Special Limits", pdfStart 218, pdfEnd
  239, offset 7 (NEW BLOCK: printed 211-287 = +7), splitAt 228,
  sections (IX.1 Filtered Limits 211; IX.2 Interchange of Limits 214;
  IX.3 Final Functors 217; IX.4 Diagonal Naturality 218; IX.5 Ends
  222; IX.6 Coends 226; IX.7 Ends with Parameters 228; IX.8 Iterated
  Ends and Limits 230). ⚠ IX is FIRST chapter of the +7 block.
  Ch VII args next: roman VII, "Monoids", pdfStart 169, pdfEnd 198,
  offset 8 (NOTE the block change: printed 161-190 = +8), splitAt 184,
  sections (VII.1 Monoidal Categories 161; VII.2 Coherence 165; VII.3
  Monoids 170; VII.4 Actions 174; VII.5 The Simplicial Category 175;
  VII.6 Monads and Homology 180; VII.7 Closed Categories 184; VII.8
  Compactly Generated Spaces 185; VII.9 Loops and Suspensions 188).
  ⚠ VII is the FIRST chapter in the +8 offset block — double-check the
  A0 pagemap block table when building its args (done above).
  ### PRIOR (superseded) diagnosis kept for the trail:
  ### Ch V HALTED — apparent OUT OF USAGE CREDITS (2026-07-22, ~15:10)
  wf_769e04f9-439 failed "no coverage batch survived": 6/16 agents done
  (inv V-A, inv V-B, merge, cover:V-0/1/2), then 10 agents ALL failed
  with "You're out of usage credits. Run /usage-credits to keep using
  Fable 5 or /model to switch models." NOTE the message names Fable 5
  even though this session's subagents had been running successfully on
  claude-opus-4-8 for all of Ch IV (22 agents, 2.7M tokens) — so read
  it as an ACCOUNT-LEVEL credit exhaustion, not a per-model routing
  regression. Do NOT thrash-retry; this is the standing halt condition.
  STATE IS CLEAN AND CONSISTENT:
   * GitHub: 190 issues (Ch I-IV only). Ch V filed NOTHING — filing
     happens only after drafting, which never ran. No partial issues,
     no orphan project items, no half-written dependency graph.
   * Ledger 426 rows (Ch I-IV complete). issue-map 294 entries.
   * On disk in scratchpad/maclane-ch5/: inventory-V-A/B + merged
     inventory-V.json (**116 items**, page accounting done) and
     coverage-V-0/1/2.json. Nothing persisted to doc/plan/books yet
     (that happens at chapter closeout) — the merged inventory is the
     valuable survivor.
  TO RESUME once credits are available:
     Workflow({scriptPath: '<books-tools>/maclane-chapter.js',
     resumeFromRunId: 'wf_769e04f9-439', args: <Ch V args below>})
   * EXPECT the coverage/verify stages to largely RE-RUN (documented
     resume-cost lesson: the prefix cache breaks on nondeterministic
     agent ordering under the MAX=2 semaphore). Budget ~a full chapter.
   * Alternative if credits stay tight: relaunch fresh rather than
     resume — the cached prefix is only 3 agents and the merged
     inventory already exists on disk.
  Ch V args (verbatim): {"roman":"V","title":"Limits","pdfStart":118,
  "pdfEnd":145,"offset":9,"splitAt":131,"sections":[{"n":1,"name":
  "Creation of Limits","printed":109},{"n":2,"name":"Limits by Products
  and Equalizers","printed":112},{"n":3,"name":"Limits with
  Parameters","printed":115},{"n":4,"name":"Preservation of Limits",
  "printed":116},{"n":5,"name":"Adjoints on Limits","printed":118},
  {"n":6,"name":"Freyd's Adjoint Functor Theorem","printed":120},
  {"n":7,"name":"Subobjects and Generators","printed":126},{"n":8,
  "name":"The Special Adjoint Functor Theorem","printed":128},{"n":9,
  "name":"Adjoints in Topology","printed":132}],"scratch":"/private/tmp/
  claude-501/-Users-johnw-src-category-theory-master/ccf260aa-13c7-4435-
  8156-ea832592c6d7/scratchpad/maclane-ch5"}
  (strip line-wrap whitespace from the scratch path when reconstructing)
  ### Ch V was LAUNCHED as: wf_769e04f9-439 (task wq1j58s7v), "Limits",
  PDF 118-145, offset +9, splitAt 131, 9 sections — the FIRST run with
  the hardened prompts (phase_c_classification, LIBRARY-DEFECT channel,
  complete trailer deps). On return, check those three new behaviors
  actually appear in the artifacts. LESSON: `node --check` the script
  after ANY prompt edit — backticks inside the template literals break
  the parse (hit this on the Ch V launch; cost one retry).
  Ch VI args next: roman VI, "Monads and Algebras", pdfStart 146,
  pdfEnd 168, offset 9, splitAt 157, sections (VI.1 Monads in a
  Category 137; VI.2 Algebras for a Monad 139; VI.3 The Comparison with
  Algebras 142; VI.4 Words and Free Semigroups 144; VI.5 Free Algebras
  for a Monad 147; VI.6 Split Coequalizers 149; VI.7 Beck's Theorem
  151; VI.8 Algebras Are T-Algebras 156; VI.9 Compact Hausdorff Spaces
  157).
  ### Residual risk the auditor named (NOT closed)
  Inventory completeness rests on the pipeline's own page accounting
  for 20 of Ch IV's 30 pages (it read 10). Same in kind for Ch I-III.
  Cheap mitigation if ever wanted: spot-read 3-4 pages of 88-102.
- SUPERSEDED NOTE (kept for the audit trail): the Fable-era Ch IV (107
  records, 9 batches, findings about Instance/Ens.v mis-citation and
  the parametric Idempotent_Reflective) is being SUPERSEDED by the
  Opus re-run. Read the FINAL workflow result before filing; do not
  carry the Fable-era numbers forward without re-checking.
- Ch IV was RUNNING as: wf_5655b02f-ca5 (task wnt0vk6bj), roman IV "Adjoints",
  PDF 88-117, offset +9, splitAt 102, 10 sections (args staged earlier,
  launched 2026-07-22). On return: established cadence. Ch V args next:
  roman V, title "Limits", pdfStart 118, pdfEnd 145, offset 9, splitAt
  131, sections (V.1 Creation of Limits 109; V.2 Limits by Products and
  Equalizers 112; V.3 Limits with Parameters 115; V.4 Preservation of
  Limits 116; V.5 Adjoints on Limits 118; V.6 Freyd's Adjoint Functor
  Theorem 120; V.7 Subobjects and Generators 126; V.8 The Special
  Adjoint Functor Theorem 128; V.9 Adjoints in Topology 132). Ch IV args
  will be: roman IV, title "Adjoints", pdfStart 88, pdfEnd 117, offset
  9, splitAt 102, sections from pagemap TOC (IV.1 Adjunctions 79; IV.2
  Examples of Adjoints 86; IV.3 Reflective Subcategories 90; IV.4
  Equivalence of Categories 92; IV.5 Adjoints for Preorders 95; IV.6
  Cartesian Closed Categories 97; IV.7 Transformations of Adjoints 99;
  IV.8 Composition of Adjoints 103; IV.9 Subsets and Characteristic
  Functions 105; IV.10 Categories Like Sets 106).
  Ch III launch args were: on fess pass → launch Ch III via maclane-chapter.js args:
  {"roman":"III","title":"Universals and Limits","pdfStart":64,
  "pdfEnd":87,"offset":9,"splitAt":76,"sections":[{"n":1,"name":
  "Universal Arrows","printed":55},{"n":2,"name":"The Yoneda Lemma",
  "printed":59},{"n":3,"name":"Coproducts and Colimits","printed":62},
  {"n":4,"name":"Products and Limits","printed":68},{"n":5,"name":
  "Categories with Finite Products","printed":72},{"n":6,"name":
  "Groups in Categories","printed":75},{"n":7,"name":"Colimits of
  Representable Functors","printed":76}],"scratch":".../scratchpad/
  maclane-ch3"} (create the scratch dir first; refresh filed-issues.tsv
  BEFORE launch — done at 86 rows).
  [prior halt record kept below for the audit trail]
- Ch II ⚠ HALTED BY SESSION LIMIT (2026-07-22, resets 5:20am
  America/Los_Angeles): wf_376d6626-6d6 failed with "no coverage batch
  survived" — NOT a pipeline defect; 8/16 agents completed (inv II-A,
  inv II-B, merge, cover:II-0/1/2/3/5) then every remaining agent
  (cover:II-4/6/7, verify:II-0/1/2/3/5) died on "You've hit your session
  limit". Completed agents are CACHED for resume. TO RESUME (after the
  reset, FIRST ACTION of the next iteration):
    Workflow({scriptPath: '/private/tmp/claude-501/-Users-johnw-src-
    category-theory-master/ccf260aa-13c7-4435-8156-ea832592c6d7/
    scratchpad/books-tools/maclane-chapter.js',
    resumeFromRunId: 'wf_376d6626-6d6', args: <the exact Ch II args
    object recorded below>}) — campaign-1 lesson applies: do NOT edit
    any prompt-producing string in the script before resuming (cache
    keys on prompts); scratch files inventory-II-*.json,
    inventory-II.json, coverage-II-{0,1,2,3,5}.json are on disk in
    scratchpad/maclane-ch2/.
  Ch II args (verbatim): {"roman": "II", "title": "Constructions on
  Categories", "pdfStart": 41, "pdfEnd": 63, "offset": 10, "splitAt":
  52, "sections": [{"n":1,"name":"Duality","printed":31},{"n":2,"name":
  "Contravariance and Opposites","printed":33},{"n":3,"name":"Products
  of Categories","printed":36},{"n":4,"name":"Functor Categories",
  "printed":40},{"n":5,"name":"The Category of All Categories",
  "printed":42},{"n":6,"name":"Comma Categories","printed":45},{"n":7,
  "name":"Graphs and Free Categories","printed":48},{"n":8,"name":
  "Quotient Categories","printed":51}], "scratch": "/private/tmp/
  claude-501/-Users-johnw-src-category-theory-master/ccf260aa-13c7-4435-
  8156-ea832592c6d7/scratchpad/maclane-ch2"}
  (NOTE: strip the line-wrap whitespace from the two paths when
  reconstructing the call; the canonical args also survive verbatim in
  the recovery block of task w99i28t17's notification and in
  workflows/scripts metadata.)
  Was RUNNING as: wf_376d6626-6d6 (task w99i28t17), generalized script
  scratchpad/books-tools/maclane-chapter.js invoked via scriptPath+args
  (roman II, PDF 41-63, offset +10, splitAt 52). REUSABLE TOOLING ready
  in scratchpad/books-tools/: file_chapter.py <R> <SCRATCH> (files
  drafts, handles duplicates-<R>.json append blocks + trailer extension,
  ledger evidence pointers, durable issue map) and
  resolve_chapter_deps.py <R> <SCRATCH> (item-id rewrite, native
  blocked-by mirror incl. pre-resolved #N cross-chapter deps, idempotent
  via existing-relation query). Durable issue map:
  doc/plan/books/maclane/issue-map.json (83 items after Ch I); filed
  snapshot doc/plan/books/maclane/filed-issues.tsv (refresh before each
  chapter's workflow launch). Per-chapter main-loop cadence after each
  workflow returns: structural-validate drafts (same python check as
  pilot) → spot-read 2-3 drafts → file_chapter.py → refresh
  filed-issues.tsv → resolve_chapter_deps.py → persist artifacts to
  doc/plan/books/maclane/{inventory,coverage,issues}/ → fess audit →
  fold findings → launch next chapter. Chapter args come from the
  pagemap TOC (offsets: II-III +10 ... see per-block table; VIII spans
  the +8 block boundary at printed 209/210 — CHECK: VIII is printed
  191-209 all +8; IX-XII +7; App +6).
- [ ] Awodey: same, with dedup vs MacLane catalog.
- [ ] Seven Sketches: same, with dedup vs both.
- Ledger: doc/plan/books/ledger.tsv (create at first filing).

## ⚠ AGENT AVAILABILITY CHANGE (2026-07-23) — fess-auditor RESTORED
The entire git-ai/nix agent set (fess-auditor + *-pro/*-reviewer +
rocq-pro) went unavailable mid-session (wholesale path deregistration,
not file loss — defs intact at ~/.config/claude/git-ai/agents/ AND the
nix source /Users/johnw/src/nix/config/ai/agents/).
**USER ASKED TO RESTORE fess-auditor → DONE:** copied the complete
definition (frontmatter + body) to the PROJECT-LOCAL path
/Users/johnw/src/category-theory/master/.claude/agents/fess-auditor.md
(untracked; the harness reads project .claude/agents/ regardless of the
global-path change). ✅ CONFIRMED HOT-RELOADED: fess-aw2 spawned successfully with
subagent_type:"fess-auditor" mid-session (no restart needed) — the
harness reads project .claude/agents/ per-spawn. Audits continue on the
proper fess-auditor. Global restore (all agents, all projects) remains
the user's call (promptdeploy/nix redeploy) — do NOT scatter copies
fighting their tooling; the project-local fess-auditor.md is enough for
this campaign.

## USER DIRECTIVE (2026-07-22, standing for this campaign)
- **MAX 2 concurrent subagents** at any time (token-allocation protection;
  reaffirms the campaign-1/2 directive). Workflow scripts must gate with a
  MAX=2 counting semaphore. sketches-a0 was stopped to comply (relaunch
  when its book starts); saved to persistent memory too.
- ⚠ CONCURRENCY DISCIPLINE CORRECTION (2026-07-23): a chapter workflow
  ALREADY uses the full MAX=2 budget (its internal semaphore). Therefore
  a fess audit (1 agent) must NOT run concurrently with a chapter
  workflow — that peaks at 3. The Ch VI→VII transition briefly did this
  (fess-ch6 + Ch VII workflow); a transient excursion, now corrected.
  NEW RULE: SERIALIZE — workflow N (MAX=2) → file/resolve/persist (0
  agents) → audit N (1 agent, ALONE) → fold findings → workflow N+1
  (MAX=2). Audits gate the next chapter (keeps the feedback loop that
  caught the dep-line/library-defect fixes). Cost: 1 idle slot during
  ~40min audits — acceptable for strict cap compliance.
- Ultracode is ON (system): workflow-orchestrate substantive tasks; the
  MAX=2 cap still governs concurrency within them.

## In flight (campaign 3)
- PAL consensus: COMPLETE (2026-07-22, continuation a72351ec-0018-4a89-
  b2c1-d4eff10a477c). Both models 8/10, no disagreements; 10 amendments
  folded into the frozen plan (§Consensus amendments): reusable-def
  splitting, obligation-normalized dedup, alias-expansion+statement-
  records+negative-search-logs, blind-verify discipline, per-page
  completeness accounting, copyright paraphrasing, catalog HTML trailer +
  dep-graph validation, idempotent ledger writes, MacLane-Ch.I pilot,
  schema validation. Plan is now FROZEN.
- A0 calibration COMPLETE for MacLane + Awodey (2026-07-22); reports
  persisted at doc/plan/books/{maclane,awodey}/pagemap.md; both agents
  stopped. KEY FACTS: MacLane = 2nd ed., NON-UNIFORM offset (9 blank
  versos dropped; per-block offsets +11..+3 — agents MUST use the block
  table); Ch I = PDF 17-40 (printed 7-30, offset +10). Awodey = 1st-ed
  CMU pre-print (2005), uniform +9, chapter-scoped shared counters, NO
  appendix. sketches-a0 still pending (stopped per cap; relaunch when
  book 3 starts).
- PILOT (plan amendment 9): workflow maclane-ch1-pilot RUNNING as
  wf_88ef8089-28b (task w9lf9todu; script at .config/.../workflows/
  scripts/maclane-ch1-pilot-wf_88ef8089-28b.js — resumable via
  resumeFromRunId) —
  Inventory(2 agents, PDF 17-28 / 29-40, 1-page read overlap) → Merge
  (page accounting 17-40) → Coverage (batches of 10-15, alias-expansion
  + statement records) → Verify (blind-first) → Draft (issue drafts to
  scratchpad). MAX=2 semaphore in-script. Main loop then: review drafts,
  file small batch (Phase F), fess audit (H) before scaling to Ch II-XII.
  Scratch namespace: scratchpad/maclane-ch1/.
- Native issue dependencies CONFIRMED available (GraphQL mutations
  addBlockedBy/removeBlockedBy/addSubIssue exist) → Phase G mirrors
  body-text Depends-on as real blocked-by relations.
- doc/plan/books/ tree + ledger.tsv header created.

## Stop-and-escalate attempt counters (campaign 3)
- (none yet)

## Learnings (campaign 3)
- mdls has no page counts for these PDFs; the /Count trick works.

## ============================================================
## AWODEY Ch9 "Adjoints" (2026-07-29) — FILED, AUDIT IN FLIGHT
## ============================================================
Args: roman "9" title "Adjoints" PDF 222-273 offset 9 splitAt 247,
sections [9.1 Preliminary definition pr213, 9.2 Hom-set definition pr218,
9.3 Examples of adjoints pr223, 9.4 Order adjoints pr227, 9.5 Quantifiers
as adjoints pr230, 9.6 RAPL pr234, 9.7 LCCC pr241, 9.8 Adjoint functor
theorem pr250, 9.9 Exercises pr262]. Workflow wf_72dc6de1-295.

- 70 items; 16 new issues **#724-#739** + **42 dedup appends** (36 with
  closure checkboxes). 1432 ledger rows; 100 awodey issues; **532 total**.
- **THE MERGE-PROMPT FIX FROM Ch8 WORKED ON FIRST USE**: the ALL-PAGES
  page-listing convention forced normalization of **23 (page,item)
  entries** and caught **4 `empty:true` misuses** (pages carrying real
  content marked empty because no item STARTED there). Bidirectional
  check then passed 0 violations both directions. The split that recurred
  in Ch7 and Ch8 is now caught mechanically at merge time.
- Verifier CONFIRMED 13/13 in batch 0 with **two recorded dissents it did
  NOT overturn** (`awodey:9.1:example2` Δ⊣×, `awodey:9.3:example8`
  terminal-as-right-adjoint) — each left a Phase-E scoping warning
  instead. That is the right move: the classification stands, the ISSUE
  gets narrowed.

### ⚠ REAL BUG FOUND BY FILING — `issue_map` OVERWRITE (fixed in tooling)
`file_chapter.py`'s duplicate pass did `issue_map[iid] = num`
unconditionally. `awodey:9.7:prop18` is a sanctioned MULTI-PART item
(new issue #730 for the dependent product; append to #387 for the
post-composition leg), so the dup pass **rewrote its primary 730 -> 387**.
Phase G looks a draft up by its first covered item, so it then resolved
**#730's OWN identity to #387** and:
  * emitted a self-cycle `#387 <- #387` (GitHub rejected it — this is the
    only reason the corruption was visible at all);
  * silently DROPPED #730's two real edges (<-387, <-731);
  * planted one **undeclared** edge `#387 <- #731` on a MacLane issue.
Graph repaired + verified (#730<-387,731; #732<-730; #739<-730; removed
#387<-731). **The lesson: a structural check that only counts edges would
have passed.** The self-cycle was the tell.
FIXES (durable copy `doc/plan/books/tools/file_chapter.py`, synced):
  1. dup pass now keeps the primary and records further legs under the
     schema's `<item-id>@<issue>` key instead of clobbering;
  2. multi-part ledger rows now NAME the part automatically, lifted from
     the drafter's `(first leg) — printed ...` parenthetical. Two guards
     were REQUIRED and both were found empirically: only for items with
     >1 target (else the same slot holds the item's NAME, e.g. "(natural
     numbers object)"), and anchored on "— printed" so it never matches
     the later "(item ...; the dual-image leg is recorded against ...)"
     paren — which names the OTHER leg and would INVERT the label.
     Replayed on Ch9 data: 7 named, 35 generic, 0 mislabelled.
  3. Ch9's 6 multi-part items back-filled by hand (12 ledger notes, 6
     `@` keys) since they were filed before the patch.
- GraphQL note: the mutation field is **`blockingIssueId`**, NOT
  `blockedByIssueId` (an ad-hoc repair script using the latter fails with
  `missingRequiredInputObjectAttribute` on every call).
- PRE-FILING COLLISION CHECK now standard and it PAID OFF: built a
  suggested-module index over all 529 issues; 3 collisions; 2 already
  correctly cross-linked (#347, #387), 1 genuine miss — the interior-
  operator draft proposed `Instance/Top/Opens.v`, the file **#685**
  creates. Patched the DRAFT before filing (cheaper than editing after).
  Restrict the index to `Suggested module` lines only — matching every
  backticked `.v` yields ~35 false positives.
- 13 library defects recorded as **A32-A43**; A32/A33 verified from source
  by me (not transcribed): `Adjunction/Natural/Transformation.v:23-24` and
  `Adjunction/Hom.v:36-37` both call `Theory/Adjunction.v` "the universal-
  morphism form", but that file self-describes at :46-47 as taking "Kan's
  hom-set form as primitive" and assigns the universal-arrow form to
  `Theory/Universal/Arrow.v` at :53-54. A33 is worse: the mislabel is baked
  into exported names `Adjunction_Hom_to_Universal`/`..._Universal_to_Hom`.
  A37/A38 deliberately SOFTENED from the verifier's framing — the file
  DOES disclose its own commented stub and even flags the stub's reversed
  direction itself, so "asserts as fact" was overstated.
- Coverage-record defect (verdict unchanged): `awodey:9.3:example10`'s
  negative log claims "polynomial -> 0 hits"; there are 6. Verdict still
  right; the LOG was wrong. Audit is checking whether other logs share it.

### NEXT: Awodey Ch10 "Monads and algebras" — args prepared (LAST Awodey ch.)
roman "10" title "Monads and algebras" pdfStart 274 pdfEnd 303 offset 9
splitAt 288, sections [10.1 The triangle identities pr265, 10.2 Monads and
adjoints pr268, 10.3 Algebras for a monad pr272, 10.4 Comonads and
coalgebras pr278, 10.5 Algebras for endofunctors pr279, 10.6 Exercises
pr290]. Offset verified on all six (265+9=274 ... 290+9=299).
⚠ 10.4 spans ONE printed page (278) before 10.5 opens at 279 — a merge
agent paging by section headings will be tempted to mis-assign it.
⚠ Expect an unusually high PRESENT rate: the tree carries a large monad/
comonad/Eilenberg-Moore/Kleisli/F-algebra development (see CLAUDE.md), so
the classifier must work HARDER to find genuine gaps, and the verifier
should be alert to PRESENT verdicts resting on a same-named weaker form.

### fess-aw9 VERDICT: **HONEST** — 3 HIGH, 3 MEDIUM, 6 LOW. ALL FOLDED.
Strongest audit of the campaign so far; it read 22/52 pages as images,
resolved all 111 file:line citations (0 mismatches), and pulled all 524
book-labelled issues to check every dependency parenthetical.
- **F1 (HIGH) — MY REPAIR FIXED THE MIRROR, NOT THE SOURCE OF TRUTH.**
  I repaired the native `blockedBy` edges and thought Ch9 closed. The
  contract (`books-catalog-campaign.md:85`) says **the BODY lines are the
  source of truth**; all three bodies were still wrong. #730 still carried
  a raw unresolved `Depends on: awodey:9.7:remark21`; #732 and #739 each
  listed `#387` TWICE and omitted #730 — and worse, both described #387 as
  `(awodey:9.7:prop18)` when #387 is only the **left-adjoint leg**, so a
  reader was told the dependent-product obligation lives at #387 when it
  lives at #730. FIXED: all three bodies + trailers now match native
  exactly (verified side by side).
  **LESSON: when a graph has a mirror and a source of truth, repairing the
  mirror is not repairing the graph. Fix the body FIRST, then re-derive.**
- **F2 (HIGH) — CHAPTER 8 HAD THE SAME BUG AND I NEVER CHECKED.** The
  auditor scanned every drafts/duplicates pair CAMPAIGN-WIDE for the
  hazard (a draft's `covers[0]` also appearing in that chapter's
  duplicates list) and found exactly TWO: Ch9's `awodey:9.7:prop18` (the
  one I repaired) and **Ch8's `awodey:8.8:remark-topos-properties`**.
  Same residue: `#405` (a MacLane issue) carried native `blockedBy`
  [384, 387] while its body declared only #358 — those are **#722's**
  deps, planted by the identical mis-resolution. FIXED: issue-map primary
  flipped to #722 with `@405` as the leg; both undeclared edges removed
  (#405 native is now [358], matching its body). Also fixed the adjacent
  `awodey:8.8:remark18` stale primary (384 -> 671, keeping `@387`).
  **LESSON: on finding a data-corruption bug, SWEEP ALL PRIOR UNITS for
  the same signature before declaring it fixed. I fixed the tool and the
  one instance I could see, and would have shipped Ch8 corrupted.**
- **F3 (HIGH) — module collisions recurred 3x, none cross-linked**:
  #724/#658 (`Functor/Coproduct/Internal.v`), #729/#320
  (`Structure/Limit/Coproduct.v`), #730/#333+#402
  (`Instance/Sets/Pullback.v`). **My own pre-filing check MISSED ALL
  THREE** — it indexed only lines containing the word "Suggested", and
  #658/#320 phrase their proposals differently. FIXED: Depends-on +
  native edge on each consumer, reciprocal "Downstream consumer" note on
  each producer.
  **TOOL BUILT: `doc/plan/books/tools/check_collisions.py`** — indexes
  every `.v` path in the Work-to-be-done/DoD/Verification sections of all
  filed issues, drops paths that already exist on disk (those are
  references, not proposals), excludes self-matches, and flags
  `[NO CROSS-LINK]`. Re-run on Ch9 it reproduces exactly the audit's
  findings. **Recall beats precision here: a false positive costs a
  glance, a false negative ships a duplicated obligation.** RUN IT
  PRE-FILING EVERY CHAPTER.
- **F4 (MED) — `awodey:9:ex7` PRESENT should be PARTIAL.** Its own
  `strength_comparison` disclosed that Exercise 7's closing question
  ("when does (-) ∧ p have a LEFT adjoint?") is unaddressed, `gap` was
  None, and the verifier wrote "PRESENT-leaning-PARTIAL". The parallel
  item `awodey:9.1:example2` was graded PARTIAL for the identical shape.
  FIXED: reclassified PARTIAL with an explicit gap; the residual clause
  (co-Heyting/bi-Heyting subtraction — no in-tree issue covered it, and
  the tree has no notion of it) placed on **#683** with 2 checkboxes;
  ledger + issue-map updated.
- **F5 (MED) — 4 false "0 hits" negative-search logs** (polynomial: 6;
  cocompletion: 3 x2; well-powered: 12). I re-ran all three greps and got
  the auditor's exact counts. All four VERDICTS survive (every hit is
  header prose, or well-poweredness packaged as data in SAFT.v). FIXED:
  logs corrected in the durable coverage JSONs with the real counts and
  why the verdict holds. Note one of these was caught by the verifier in
  a DIFFERENT record and never propagated — corrections must be applied
  tree-wide, not per-record.
- **F6 (MED)** defect-haul count said 13; there are 12 rows, 11 new (A40
  duplicates A1). FIXED.
- **F9 (LOW, systemic)** contract requires cross-book dedup targets to
  carry the later book's label; **91** issue-map targets lacked
  `book:awodey` (broader than the audit's Ch9-scoped estimate). FIXED:
  all 91 labelled; all 191 awodey targets now verified labelled.
- **F8/F12 (LOW)** line drift fixed (A41 is `:16` not `:17`; A34 spans
  `:79-82`); A36 widened — that ONE sentence at `Instance/Fun.v:59-63`
  carries THREE unbacked claims (objectwise colimits, cartesian closed,
  free cocompletion), and the same file hedges correctly at :104-105, so
  :61 contradicts its own file.
- **F10/F11 NOT fixed, deliberately.** F10 (append heading `### Also
  covered by` vs the contract's `## Also covered in`) is a ~500-append
  systemic deviation; churning every issue to match the doc is worse than
  the deviation — recorded as an accepted deviation. F11 (frozen plan
  cites the old `~/dl` PDF path) stays an ERRATUM: the plan is frozen and
  the correct Desktop path is already in this handoff's ENVIRONMENT
  CHANGED section.
- Audit's own disclosed gaps (good practice, recorded): 30/52 pages not
  read as images; the "23 entries added / 4 empty-flips" delta could not
  be verified because the pre-normalization inventory is not on disk and
  `doc/plan/` is untracked; 39/42 dedup appends checked structurally only;
  no Coq compiled.
**Ch9 CLOSED.** 532 issues, 1432 ledger rows, 100 awodey issues.

### INDEPENDENT RE-VERIFICATION OF THE F2 SWEEP (main session, not the auditor)
I did not take "exactly two hits" on faith — the whole claim that the rest
of the campaign is uncorrupted rests on it. Re-ran the sweep myself over
every drafts/duplicates pair in BOTH books. Result: the auditor's count is
right, and the bug's trigger is now characterized EXACTLY:

  **The hazard is not "a covered item is also a duplicate target".
  It is "covers[0] is also a duplicate target".**

Phase G resolves a draft's OWN issue number by looking up `covers[0]` in
issue-map, so only the FIRST covered item can corrupt the source identity.
  * `awodey:9.7:prop18` — covers[0] of its draft -> #730 mis-resolved to
    #387. CORRUPTED (repaired).
  * `awodey:8.8:remark-topos-properties` — covers[0] of its draft.
    CORRUPTED (repaired).
  * `awodey:9:ex3` — my broader sweep flagged it, but it sits at covers[1]
    behind `awodey:9.1:example2` (never a dup target), so #724's identity
    resolved correctly. VERIFIED CLEAN: #724 body {351,353,658} == native
    {351,353,658}; #353 native {351} == its body, no planted edges.
My sweep over-approximates (safe direction); the auditor's predicate was
the precise one. Either way: **no third instance exists.** Campaign-wide
graph corruption from this bug is fully accounted for and repaired.

## ============================================================
## AWODEY Ch10 "Monads and algebras" (2026-07-29) — FILED; AUDIT IN FLIGHT
## ============================================================
Workflow wf_a1af76ac-8ed. 46 items; 14 new issues **#740-#753** + 12 dedup
appends. **546 issues; 1476 ledger rows.** AWODEY BOOK COMPLETE (10/10
chapters filed). Inventory clean on first pass: page accounting tiled
274-303 exactly, numbering continuous 10.1..10.14 + exercises 10.6.1..10,
ALL-PAGES normalization added 10 entries, bidirectional check 0 mismatches.
Phase G: **18 edges, GRAPH CLEAN** (no cycles, no failures).

### ⚠ THE OVERWRITE BUG HAD A SECOND HOME — caught BEFORE filing
`awodey:10:ex7` is split across **two NEW DRAFTS** (draft 1 = the general
comonad-from-adjunction construction; draft 3 = part (c)). My Ch9 patch
fixed only the DUPLICATE pass; the **draft loop had the identical
`issue_map[c] = num` clobber**. Left alone it would have rewritten ex7's
primary 740 -> 742 — the exact Ch9 corruption, one loop earlier. Patched
both loops; verified post-filing: `ex7 -> 740` + `ex7@742`, `ex1 -> 637` +
`ex1@252`. **LESSON: when fixing a bug, fix every site with the same
shape, not the one that bit you.** (This is the second time this chapter's
work has restated that lesson — cf. the F2 Ch8 sweep.)
- The part-name extractor needed widening too: Ch10 phrases citations as
  "printed page 290 (PDF page 299) —", so the Ch9 `— printed` anchor never
  fired. The second phrasing NESTS parens ("(parts (a) and (b); part (c)
  is recorded on #252)"), which no character-class regex can bracket, so
  it now uses a balanced scan truncated at the first ';' — everything
  after the ';' describes the OTHER leg and would invert the label.
  Verified on both chapters: 9 legs named, 0 inverted.
- **`check_collisions.py` EARNED ITS KEEP ON FIRST REAL USE** (run
  pre-filing, as intended): 2 candidates, 3 missing cross-links —
  `Instance/Powerset.v` (#382) and `Instance/Sets/Powerset.v` (#466,
  #704). All patched into the DRAFTS before filing, so they landed as real
  native edges (#745<-#382, #750<-#466, #750<-#704) instead of needing
  post-hoc repair. Zero collisions escaped this chapter.
- validate_drafts.py flags "awodey:10:ex7 covered twice" as a PROBLEM.
  This is a FALSE POSITIVE under schemas.md — a multi-part item split
  across two new drafts is sanctioned. Left as-is (advisory tool, and the
  flag is a useful prompt to check the split is real). Do not "fix" it by
  merging the issues.

### DEFECT HAUL: A44-A49 — A44 IS THE CAMPAIGN'S LARGEST CLUSTER (6 FILES)
**A44**: the "Kleisli = INITIAL resolution / Eilenberg-Moore = TERMINAL"
claim is asserted declaratively in **six** files (Monad/Eilenberg/Moore.v,
.../Moore/Adjunction.v, Theory/Monad.v, Monad/Kleisli.v,
Monad/Adjunction.v, Comonad/Duality.v) and is **not merely unproven — it
is UNSTATABLE in the tree**. I verified all six verbatim and ran the
counter-searches myself: `kleisli` = **0 hits** in Monad/Comparison.v and
**0** across all Monad/Monadicity/*.v (so no Kleisli->EM comparison
functor exists), and `(Record|Class|Definition|Instance).*Resolution` =
**0 hits** (so there is no category of resolutions in which initiality
could be stated). Asymmetry preserved in the ledger: terminality is
PARTLY backed (EM_Comparison_Forget/Free give the mediator, missing only
uniqueness); initiality has NO in-tree content.
**A45** Instance/Poset.v:46-54 claims "[Poset] **installs the resulting
dictionary**" (adjunction=Galois, monad=closure operator, product=meet,
coproduct=join). The file defines only `eq_equiv`, `Poset`,
`LessThanEqualTo_Category`. HIGH: it actively misleads classification —
it was found *while confirming an item ABSENT*.
**A46** Theory/Lambek.v:19-21 says the **structure map α is invertible**;
:40-41 proves only `F μ ≅ μ`. Consequential: the weak form cannot derive a
non-existence, which is exactly why #750 needs a strengthened Lambek.
**A47** docs/INHABITATION.md under-discloses that `adamek` has no concrete
in-tree `AdamekData` — and that doc is the one CLAUDE.md points readers to
for precisely this question.
- Coverage-log artifact corrected in the durable JSON (a 'closure oper'
  log mis-cited Structure/Factorization.v:69). NOTE TO SELF: I nearly
  replaced it with a WRONG count — case-sensitive grep gives 2 lines, but
  the verifier used `-i` and its 4 line numbers (48,64,66,68) are right,
  because :64 and :68 capitalize "Closure". Verify before "correcting".

## ============================================================
## NEW USER REQUIREMENT (2026-07-29): DEPENDENCY-GRAPH QUALITY GATE
## ============================================================
User: inter-issue dependencies must be CORRECT so that implementation can
proceed in the right order AND so independent issues can be worked by
parallel agents. This is now a completion requisite for the campaign.

FOUR PROPERTIES (the last is NOT implied by the graph):
 1 SOUND      - every declared edge is a real prerequisite
 2 COMPLETE   - every real prerequisite is declared
 3 CONSISTENT - body == trailer == native blockedBy
 4 CONFLICT-FREE - issues with NO dependency path must not write the same
   NEW file, else "independent" agents collide. THIS IS A DISTINCT
   PROPERTY and the dependency graph alone cannot express it.

### DETERMINISTIC PASS DONE (main session, no agents) — baseline
Corpus: 538 book-labelled issues, 672 native edges.
- **ACYCLIC: 0 cycles.** A valid total order exists.
- **9 topological layers**; layer 0 = **173 issues with NO prerequisites**
  (immediately parallelizable). Persisted: `doc/plan/books/graph/layers.tsv`.
- **body vs native: 2 mismatches** (now 0 after the fixes below).
- body vs trailer differs on 278 issues — **NOT a defect**: trailers store
  item-ids, bodies store resolved `#N`. Representational, verified.
- **4 genuinely missing edges found and ADDED** (#541<-#536, #649<-#648,
  #650<-#651, #650<-#649) + their raw ids resolved to `#N` in the bodies.
  Cause: Phase G resolves per-chapter AT FILING TIME, so a dependency on
  an item filed in a LATER chapter could never resolve, and nothing ever
  re-ran. **Any future chapter must re-run a global resolution pass.**
- ⚠ **METHOD WARNING (I got this wrong first):** a naive regex over
  `Depends on:` lines reported **190** unresolved deps and **3 cycles**.
  All were artifacts. Raw item-ids appear in two INNOCENT positions:
  (a) as the LABEL of an already-resolved dep — "#530 (`maclane:VIII.1:
  remark2`)"; (b) in trailing DOWNSTREAM prose on the same line —
  "Required by the member calculus (`maclane:VIII.4:def-member`)",
  "The pullbacks obtained here feed ...", "Provides the subquotient ...".
  Correct extraction strips `#N (`id`)` labels and truncates at the first
  reverse-cue (Required by|Provides|feeds|used by|Downstream|tracked by).
  True numbers: **7 issues, 4 distinct missing edges, 0 cycles.**

### ⚠ OPEN: 54 PARALLELISM HAZARDS ACROSS 27 MODULES (property 4)
61 NEW modules are proposed by more than one issue; **54 issue-pairs share
a new module with NO dependency path between them** — they LOOK independent
and are not. Persisted: `doc/plan/books/graph/parallel-hazards.json`.
Largest: `Construction/FreeMonoidal.v` (8 pairs; #496,497,498,504,509,608),
`Adjunction/Conjugate.v` (6; #394,396,397,398,399), `Theory/Algebra/Module.v`
(6; #505-509), `Structure/Monoidal/Coherence.v` (5; #497,499,501,504,509).
These are mostly GENUINE topic clusters (several issues building one file),
not dedup failures — so the fix is per-cluster judgement: identify which
issue CREATES the module and which EXTEND it, then add the ordering edges
(or mark the cluster as one serialized work-unit).
**NEXT ACTION: a workflow over the 27 modules to decide each cluster's
internal order and emit the edges. QUEUED behind fess-aw10 (MAX-2 cap).**

### fess-aw10 VERDICT: **HONEST, with ONE HARD FALSEHOOD** — all folded.
Best-instrumented audit of the campaign: it **compiled Coq** to disprove a
claim, image-read the §10.4/§10.5 boundary trap, and opened 11 of 16 PRESENT
records' citations. It also confirmed the classification layer is the
campaign's strongest (three records show the verifier overturning its OWN
blind pass with an argument, two carry in-place `[corrected by Phase D]`
markers, and BOTH qualifications I flagged survive verbatim, un-upgraded).

- **H1 (HIGH) — I PUT A FALSEHOOD IN A FILED ISSUE.** #750 asserted in FOUR
  places that the current `Qed`-opaque `lambek` "cannot be applied to
  conclude a non-existence", and I repeated it as A46's "consequential, not
  cosmetic" rationale. **FALSE.** `lambek` concludes `F μ ≅ μ`, which is
  exactly what Cantor contradicts; whether α IS the iso is irrelevant. The
  auditor compiled a probe; **I re-compiled it independently under Rocq 9.1
  and it builds**: `intro I; exact (cantor _ (lambek P I)).` FIXED: all four
  sites in #750 rewritten, the spurious `#748` blocker removed from body,
  trailer AND native edge (#750 blockedBy now 227,466,704). A46's rationale
  replaced — its UNDERLYING defect is still real and stands (header promises
  an invertible structure map, theorem delivers a bare iso).
  **LESSON: I reasoned about what a Coq lemma could prove instead of asking
  the compiler. Two lines of Coq beat a paragraph of plausible argument.**
- **H2 (HIGH)** — 7 of 8 Ch10 dedup targets lacked the contract-required
  `book:awodey` label (#463,#466,#471,#482,#476,#469,#252). A Ch10
  REGRESSION, not drift — every earlier chapter's targets sampled clean.
  Real consequence: the contract's idempotency pre-flight
  (`gh issue list --label book:<book>`) would not surface them, so a resumed
  run could re-file duplicates. FIXED, all 8 now verified labelled.
  (Root cause is the same F9 class fixed campaign-wide earlier; Ch10's
  targets were filed after that sweep, so they missed it. **Any future
  chapter must re-run the label sweep after filing.**)
- **M1 (MED) — A44 UNDERCOUNTED ITS OWN CLUSTER: EIGHT files, not six.**
  Missed `Theory/Adjunction.v:68-70` and `Monad/Comparison.v:25,28` (plus
  two more instances inside the already-counted Comonad/Duality.v). Both
  verified from source. **METHOD LESSON, now recorded in the ledger:** my
  counter-search proved the ARTIFACT absent (`kleisli` = 0 in
  Monad/Comparison.v) but I never searched for further ASSERTION SITES —
  and that very file asserts "the terminal resolution" twice.
  Absence-of-artifact and absence-of-claim are DIFFERENT searches.
  Auditor independently confirmed both A44 counter-searches and the
  recorded asymmetry; it also caught that "only uniqueness is missing" was
  too generous (the ambient category is missing too). Both fixed.
- **M2** book paraphrase over-attributed the non-uniqueness clause to the
  §10.2 remark (it belongs to the separate §10.3 remark, p.277) — the
  verifier had already walked this back in its notes but the `book` field
  was never corrected. FIXED in the durable JSON.
- **L1** "eventually-periodic" -> "eventually-fixed" (PDF 301 reads
  e^(n+1)(x) = e^(n)(x)). FIXED in inventory + coverage.
- **L4** A47 reframed: `adamek` is not under-disclosed in
  docs/INHABITATION.md, it is ABSENT (`grep -i adamek` = 0 hits) — an
  omission, not a mis-description. FIXED.
- **L2 (systemic, not fixed)** many notes say "recorded in problems[]" but
  no `problems` key exists in the inventory or any verified-*.json —
  content landed in library-defects.md; only the POINTER NAME is wrong.
  Worth fixing in the schema wording for Seven Sketches.
- **L3/L7** two negative-search logs mispair command with result
  (reproducibility broken, conclusions unaffected). L6: #471's gap clause
  (1) is already filed as #296 and the append doesn't cross-reference it.
- Auditor's disclosed gaps: 5 of 30 pages image-read (rest via text layer);
  drafts-vs-filed bodies not diffed line by line; 5 of 8 dedup append
  prose blocks checked structurally only; project numeric ID not confirmed.
**Ch10 CLOSED. AWODEY BOOK COMPLETE — 10/10 chapters, all audited HONEST.**

### GRAPH GATE: round 1 done — MY DETECTOR WAS THE MAIN DEFECT
Workflow wf_e18d4070-072 resolved 15 of 27 clusters (13 agents died on API
529 Overloaded, server-side). Of **27 edges it proposed, 20 ALREADY EXISTED.**
That ratio was the tell, and the diagnosis is important:

**`check_collisions.py` counted IMPORTS as creations.** Issues declare
imports after a donor marker — "In-tree donors: `Adjunction/Conjugate.v`
(new)" — while creators write "Suggested module: `Adjunction/Conjugate.v`".
My section-scan swept both, so for Conjugate.v it reported 6 conflicting
pairs when only **#394** creates the file and the other four merely import
it. The creator/consumer relationship had been recorded correctly all along.
FIXED (`doc/plan/books/tools/check_collisions.py`): each line is truncated at
the first donor marker (`In-tree donors|Donors:|Require Import|Downstream
consumers`) before extracting paths. That handles the awkward real cases:
#320 puts a proposal AND its donors on ONE line ("Suggested path: `A.v`.
Donors: `B.v`") and must keep A.v while dropping B.v. Regression-tested
against 5 known cases (2 precision, 3 recall) — all pass. NOTE the earlier
ad-hoc version had the OPPOSITE failure (indexed only "Suggested" lines,
missed #658's "Add X.v" bullet and #320's "Suggested path"), so BOTH failure
directions are now covered by the tests.

**Corrected numbers: 40 shared modules, 18 hazard pairs, 15 modules**
(was 61 / 54 / 27). Graph: **678 edges, ACYCLIC, 9 layers, 172 issues with
no prerequisites.** Deliverables refreshed at `doc/plan/books/graph/`
(`layers.tsv`, `parallel-hazards.json`).

**7 genuinely new edges added** (all cycle-checked first): #514<-#513,
#466<-#227, #704<-#227, #437<-#348, #504<-#497, #718<-#339, #443<-#400.
The adversarial verify stage more than paid for itself — it did NOT rubber-
stamp:
 - **#437<-#348**: refuted the proposed rationale with COMPILED counter-
   evidence (wrote both directions, `Print Assumptions` clean) — the edge
   survives on weaker grounds than claimed.
 - **FreeMonoidal**: caught a MISSED prerequisite #504<-#497 that the
   ordering agent had parked as "outside this set".
 - **Instance/Fun/Terminal**: caught that the proposed #720<-#718 ALREADY
   existed and only #718<-#339 was missing — i.e. the proposer's own
   premise ("the chain is missing from the graph") was half false.
 - **Instance/Rng/Free**: refuted #400<-#312 as OVER-CONSTRAINING — #312
   carries 6 blockers and only one of its rows touches the module, so that
   edge would make `Instance/Rng/Free.v` unstartable until all 6 clear.
   Recommended #400 as module owner instead. Applied #443<-#400.
 - **Instance/Module/Tensor**: refuted the prerequisite outright (the real
   supplier is #306, not #388/#449) → NO edge added, hazard left standing
   for a human. Correct call: an invented edge is worse than a known hazard.
**Round 2 running (wf_e6675647-08b) over exactly the 15 true clusters.**

### GRAPH GATE: NOW MACHINE-CHECKABLE — `doc/plan/books/tools/check_graph.py`
The requirement said this is a completion requisite, so it needed to be
VERIFIABLE, not asserted. The checker verifies all four invariants over the
live GitHub state and **exits non-zero on violation** (wire it into lint/check
the way the other repo guards are). Report persisted:
`doc/plan/books/graph/invariants.json`; schedule: `graph/layers.tsv`.

**CURRENT STATE: 538 issues, 678 edges, ACYCLIC, 9 layers, 172 issues at
layer 0. Invariants 1-3 CLEAN. 18 CONFLICT-FREE violations remain across 15
modules** (round-2 workflow wf_e6675647-08b resolving them).

Building it immediately caught FOUR defects, three of them MINE:
1. **ROOT off by one** (`tools->books->plan->doc`, stopping at `doc/` not the
   repo root) silently broke the "file already exists" filter, so every
   EXISTING module counted as newly-proposed — `Theory/Universal/Arrow.v`
   alone produced ~30 phantom conflicts. Now asserted at startup: the script
   refuses to run unless ROOT contains `Theory/`.
2. **7 of my own edges were NATIVE-ONLY.** I added them via GraphQL and never
   wrote the body `Depends on:` lines — the exact defect the Ch9 audit (F1)
   taught me, reintroduced within the same session. All 6 legitimate ones now
   have body lines; #652's declared-but-unmirrored #247 edge added.
3. **I over-constrained #541.** Its text says only "**Benefits from** the
   finite-biproduct matrix calculus", and I promoted that to a hard blocker
   on #536. Demoted (edge removed). The checker now treats a SOFT cue family
   (`Benefits from`, `same obligation as`, `Related (NOT blocking)`) as
   non-dependencies alongside the DOWNSTREAM family (`Required by`, `feeds`,
   `Provides`), because each family fails differently: downstream cues INVERT
   the arrow (phantom cycles), soft cues OVER-CONSTRAIN (needless serializing).
4. **My own prose created phantom edges.** A bare `#312` inside an
   explanatory clause ON a `Depends on:` line reads as a dependency, and
   #657 had a dedup sentence sharing its dependency line. Both reworded.
   **RULE: a `Depends on:` line must contain ONLY dependencies — no
   cross-references, no dedup notes, no comparisons naming other issues.**

Checker design notes worth keeping:
- The label pattern must allow prose INSIDE the paren
  ("#731 (`awodey:9.7:remark21` — structure on slice categories)") or every
  well-annotated dep is reported unresolved.
- CONSISTENT is checked BOTH ways: a native-only edge is as much a defect as
  a missing one, since the contract makes the body authoritative.
- Property 4 is deliberately separate: the dependency graph CANNOT express
  it, so a perfect graph can still yield an unsafe parallel schedule.

## ============================================================
## GRAPH GATE: **CLEAN** — all four invariants hold (2026-07-29)
## ============================================================
`python3 doc/plan/books/tools/check_graph.py` exits **0**.
538 issues, 684 edges, ACYCLIC, 9 layers, **168 issues startable immediately**.
Artifacts: `doc/plan/books/graph/{invariants.json,layers.tsv,
parallel-hazards.json,serialize-groups.json}`.

Round 2 (wf_e6675647-08b) resolved all 15 remaining clusters, 0 agent errors:
11 agreed, 4 disputed by the adversarial verifier. **6 substantive edges
added** (#312<-#400, #378<-#356, #585<-#334, #639<-#683, #683<-#223,
#343<-#503), each with a body line added IN THE SAME STEP this time.

### THE KEY DESIGN DECISION: two kinds of constraint, two homes
A shared-file conflict is discharged EITHER by a dependency edge (a real
order exists) OR by a **serialize-group** (peers with no precedence that
must not share a parallel wave). They cannot both be edges:
**asserting precedence that does not exist over-constrains the schedule, and
a fabricated edge is worse than a documented hazard because it silently
serializes work that could have run in parallel.** So
`graph/serialize-groups.json` holds 10 groups / 12 pairs, and check_graph.py
READS it — otherwise the gate could never reach clean and would stop being a
gate. Two sub-kinds recorded honestly:
 - SERIALIZE_ONLY peers (5 clusters): genuine co-authors of one new file.
 - Residual peers under a common creator (4): ordered behind the creator but
   mutually unordered — the resolver flagged this for Rng/Free itself.
 - UNRESOLVED (1): `Instance/Module/Tensor.v` #388+#449 — the verifier
   REFUTED the proposed prerequisite (the real supplier is #306, not either
   of them) and offered no replacement, so NO edge was invented. Human call.

### I ALMOST OVER-CONSTRAINED IT AGAIN — caught by reading titles
I was about to add 6 "creator-first" edges for the SERIALIZE_ONLY clusters.
The agents had deliberately emitted NO edges for those, and two of my
inferred directions were **backwards**: `#296 <- #502` would have put "The
free monoid and its universal property" (MacLane II.7) behind a specific
construction of it (VII.3), and `#564 <- #563` would have put the general
interchange theorem behind its Set-specific instance. Dropped all 6;
recorded as serialize-groups instead. **LESSON: when an analysis declines to
assert an edge, that is a finding, not an omission to fill in.**

## ============================================================
## BOOK 3: SEVEN SKETCHES — STARTED (2026-07-29)
## ============================================================
Fong & Spivak, *An Invitation to Applied Category Theory: Seven Sketches in
Compositionality*. PDF `/Users/johnw/Desktop/Spivak_Fong_Seven_Sketches.pdf`,
**353 pages** (verified via the /Count trick). Project **6** ("Seven
Sketches", verified to exist). priorBooks `["maclane","awodey"]` — dedup must
run against BOTH completed books (538 issues).

⚠ **NAMING FOOTGUN, now documented in schemas.md:** the item-ID prefix is
`7sketches:` (schemas.md + check_graph.py's ITEM_ID regex) but the DIRECTORY
and the `file_chapter.py` BOOK argument are `seven-sketches` (its PROJECT map
and ISSUEMAP path). BOTH spellings are load-bearing — do not "fix" either in
isolation. The empty `doc/plan/books/7sketches/` is a stale setup scaffold,
NOT the live directory. Live scaffolding created at
`doc/plan/books/seven-sketches/{inventory,coverage,issues}` + `issue-map.json`.

### ARCHITECTURE DECISION: why NOT one mega-workflow for all 7 chapters
Tempting, and wrong. **Cross-chapter dedup requires filing BETWEEN chapters.**
A single workflow drafting all seven chapters would have each chapter dedup
only against previously FILED issues — i.e. against MacLane+Awodey but not
against each other — so two Seven Sketches chapters covering the same
obligation would both file it. The whole campaign's one-canonical-issue
invariant depends on the filing step happening between chapters. Also filing
is a shared-state mutation and stays in the main session (the `issue_map`
corruption earlier this session is the standing argument for that).
So the shape is: ONE calibration workflow, then ONE pipeline per chapter with
filing + audit in between. Per-chapter cadence is unchanged.

### A0 CALIBRATION RUNNING: wf_44ddb197-d38 (new tool `books/tools/book-a0.js`)
Two INDEPENDENT agents in parallel, then a reconciler:
 - agent 1: edition + full TOC + the NUMBERING SCHEME, and is required to
   PROVE the scheme by quoting a body example rather than asserting it;
   explicitly forbidden from reporting an offset.
 - agent 2: determines the offset EMPIRICALLY from >=10 spread probes,
   forbidden from reading the TOC, and told about the Mac Lane non-uniform
   trap (9 dropped blank versos drifted the offset +11 -> +3, and every agent
   that assumed a constant offset produced wrong citations). Must bisect and
   report per-range blocks if it drifts. probes[] must list every page opened.
 - reconciler: applies agent 2's offset to agent 1's printed chapter starts
   and OPENS those pages to confirm each lands on the right chapter opening —
   that cross-check is the actual test of the calibration. Must report every
   disagreement rather than silently preferring one agent, and emits final
   per-chapter launch args (tiling with no gaps/overlaps) plus pagemap.md.
Splitting TOC from offset is deliberate: it makes the offset an independent
measurement instead of something inferred from the same TOC it validates.

### A0 CALIBRATION COMPLETE — CONFIRMED. Persisted:
`doc/plan/books/seven-sketches/pagemap.md` (26.6 KB) and
`chapter-args.json` (8 entries, ready-to-launch per-chapter args).
**Uniform offset +12: printed = pdf - 12**, for the entire arabic body, no
drift. Evidence: 18 probes; the reconciler then applied the offset to all TEN
reported chapter starts and OPENED every page (10/10 correct), re-derived the
offset three independent ways, and diffed all 146 sections against the printed
TOC (146/146 match, zero folio mismatches across all 341 body pages).
Tiling verified contiguous PDF 13..334 with no gaps: ch1 13-50, ch2 51-88,
ch3 89-128, ch4 129-158, ch5 159-192, ch6 193-232, ch7 233-270,
Appendix A 271-334. Bibliography 335-342 and Index 343-353 are deliberately
outside the tiling (no items).

### ⚠⚠ THE BIG FINDING: **DISPLAYED EQUATIONS SHARE THE ITEM COUNTER**
The campaign's known failure mode is LIVE in this book and unavoidable. ONE
counter per chapter, and numbered displays draw from it alongside every named
environment. Proof read off the page (printed 31-32): Proposition 1.111 ->
Exercise 1.112 -> Example 1.113 -> Exercise 1.114 -> Theorem 1.115 ->
**equation (1.116)** -> Example 1.117. Confirmed four independent ways plus a
mechanical harvest over the whole text: chapter 1 has named items at only 117
of its 125 numbers, and the absent {2,3,5,8,15,96,108,116} were each verified
to be a numbered display.
**Therefore the merge phase's NUMBERING-CONTINUITY check must NOT treat those
as gaps** — an agent that "fills the gaps" invents items that do not exist.
This is now written into schemas.md AND into the Ch1 launch `numbering` note.
Requiring the A0 agent to PROVE the numbering scheme from a body example,
rather than assert it, is what surfaced this before it corrupted anything.

Other A0 findings folded into the launch args + schemas.md:
- **'Rough Definition' is a real header kind** (4.45, 4.51, 5.33, 6.68, 6.91,
  6.98) that NEITHER source agent enumerated — the reconciler caught it.
  schemas.md kind enum extended with `rough-definition` and `equation`.
- Numbers are always CHAPTER.ITEM, never section-relative (item 1.125 exists
  though ch1 has only sections 1.1-1.5). Sections nest THREE deep (1.2.2).
- **TOC title != chapter-opening title for ALL SEVEN chapters** (ch1 TOC says
  "Orders and adjunctions", the opening page says "Orders and Galois
  connections") — will break any naive title-matching check.
- Exercises are INLINE, not collected at chapter end, numbered from the shared
  counter. Solutions in Appendix A; **Exercise 3.98 has no printed solution**
  (243 body exercises vs 242 solution headers) — do not chase it.
- Shaded boxes SPAN PAGE BREAKS (number on page N, body onto N+1); colour is
  the fastest visual discriminator when reading images.
- Front matter pdf 1-12 = roman i-xii at OFFSET 0, a different sequence.
  Appendix A runs its OWN equation counter (A.1-A.4) and holds no named items.
- Two known text-extraction false positives: "Definition 7.25. 8" (a wrapped
  list item) and "Example 2.2.23" (a citation to another book's numbering).
- SCHEMA-FORCED ENCODING: `sections[].n` is an integer, so it holds the
  section's ORDINAL and the real dotted number is PREFIXED onto `name`
  (name='1.2.2 Preorders'). The idnote tells agents to parse the dotted
  number off `name` and never use the ordinal in an id.

**Ch1 LAUNCHED: wf_a6814088-022** (PDF 13-50, offset 12, splitAt 30, 17
sections). Scratch `scratchpad/7s-ch1`. Then the established per-chapter
cadence: validate_drafts -> check_collisions (PRE-filing) -> file_chapter ->
refresh filed-issues.tsv -> resolve_chapter_deps -> persist -> fess audit
ALONE -> fold -> next chapter. After the last chapter, re-run
`check_graph.py` over the enlarged corpus (it must still exit 0).

### 7S Ch1 FILED — #754-#770 (17 new) + 43 dedup appends. AUDIT IN FLIGHT.
126 items, 24 agents, 0 errors. Phase G: **40 edges, GRAPH CLEAN.**
**Totals: 555 issues, 1610 ledger rows, 17 seven-sketches issues.**
Pre-filing checks both clean: validate STRUCTURALLY CLEAN, check_collisions
**0 candidates** (first chapter in the campaign with zero — the new-module
namespace for order theory does not overlap what MacLane/Awodey proposed).

- **THE EQUATION-COUNTER GUIDANCE WORKED.** No phantom gap reports, and the
  inventory correctly records genuine equation items (e.g. `eq8`) as items
  while leaving mere intermediate displays as consumed numbers. This was the
  single biggest risk in the book and it was defused at calibration time.
- **DEDUP LOAD IS THE HEAVIEST OF THE CAMPAIGN**: 43 appends onto ~20 prior
  MacLane/Awodey issues (#223 x6, #714 x6, #463 x5, #382 x4, #380 x4). That
  is expected — chapter 1 is order theory, which the prior two books already
  cover categorically — but it is also the chapter's main risk, so the audit
  brief specifically asks whether an order-theoretic SPECIAL CASE is being
  over-deduped onto its categorical GENERALIZATION. Those are not the same
  obligation and must not be silently merged.
- Three Phase-C corrections were kept in `verifier.notes` rather than
  overwriting the Phase-C fields, preserving provenance: ex7's boolean-join
  miscount, eq8 omitting that `CocartesianFunctor` IS in-tree
  (Functor/Structure/Cartesian.v:127-133), example9 vs the unused
  `nat_setoid` at Lib/Datatypes.v:353. Audit is checking the FILED issues
  reflect the corrections, not the uncorrected text.
- ⚠ **A LINE-BREAK CAN FALSIFY A NEGATIVE SEARCH.** A verifier found
  "generative effect -> 0 hits" was true only because the phrase is
  line-broken in the source; `Instance/Poset.v:96-100` in fact **cites this
  Seven Sketches chapter by name** and states the generative-effect
  definition. Valuable provenance, and a new failure mode for negative logs:
  multi-word greps need a whitespace-tolerant pattern. Audit is sweeping for
  others.

### DEFECTS: new file `doc/plan/books/seven-sketches/library-defects.md` (S1-S4)
- **S1** Instance/Two/Discrete.v:22-24 claims BOTH shape directions but the
  cited Structure/Limit/Cartesian.v has exactly ONE theorem (limit/product);
  `Cocartesian_Colimit|Colimit.*Cocartesian` = 0 hits tree-wide.
- **S2** Instance/Sets.v:32-33 claims "characterizations of monos as
  injections AND epis as surjections". Monos: real (`injectivity_is_monic`
  :369). Epis: **not in the environment** — the file itself says at :414-417
  that `surjectivity_is_epic` "ends in a non-completing tactic, so [it] does
  NOT enter the environment". The file contradicts its own header, and the
  honest predicativity disclosure at :99-104 makes the header the only wrong
  part.
- **S3** Instance/Rel.v:163-165 asserts `Relation_Functor` is "faithful";
  the symbol occurs exactly once (its own definition) and no `Faithful`
  instance exists. Unproven claim, probably true.
- **S4 DISMISSED, recorded so it is not re-litigated**: a verifier flagged
  Theory/Isomorphism.v:30-31 ("an isomorphism in Cat is the same as an
  equivalence") as stale, but the very next sentence explains that a strict
  isomorphism needs EQUALITY of the round trips and is deliberately not
  abstracted. Given `Isomorphism` states its round trips up to `≈`, the
  passage is correct as written.
- **RECURRENCE RECORD**: A1/A2 (dangling `[Pos]`/`[Ord]`) were flagged
  **independently by 8 agents** this chapter, and A45 (Poset "installs the
  dictionary") by 5 — both files are foundational to an order-theory chapter
  so every batch tripped over them. A1/A2 is now the campaign's
  most-rediscovered defect. Re-confirmed A45 with a sharper counter-search:
  `Cartesian|Cocartesian` over Poset.v AND Proset.v = 0 hits.

### NEXT: 7S Ch2 args ready in seven-sketches/chapter-args.json
Cadence unchanged. After Ch7, re-run `check_graph.py` — it must still exit 0
over the enlarged corpus (it will need the new seven-sketches issue-map, which
it already reads).

### ⚠ KNOWN BEHAVIOR: the fess-auditor goes IDLE WITHOUT DELIVERING
Observed three consecutive times now (fess-aw9, fess-aw10, fess-7s1): the
agent finishes its work, emits an `idle_notification` with NO summary and NO
report, and waits. Sending it a SendMessage asking for the report produces the
full findings immediately and at full quality — nothing is lost, it just does
not volunteer. **So on any idle notification from a fess-* agent with no
summary attached, ping it; do NOT assume it failed or re-run the audit.**
The ping should restate the required format and, importantly, tell it that an
honestly-reported PARTIAL audit beats a padded summary of incomplete work —
that instruction is what produced fess-aw10's explicit "Verification Gaps"
section (5 of 30 pages image-read, etc.), which was some of its most useful
output.

### fess-7s1 VERDICT: **HONEST work with a real defect cluster** — all folded.
⚠ **RECOVERY NOTE:** this auditor went idle twice WITHOUT delivering, even
after an explicit ping. Rather than re-run it (expensive) I recovered the full
report from its transcript by extracting only the ASSISTANT TEXT BLOCKS with
python — `subagents/agent-afess-7s1-*.jsonl`, 229 lines / 2.4 MB, so never
`cat` it. It had done all the work and left artifacts in the scratchpad; only
the delivery failed. **Technique to reuse: parse the jsonl, keep
message.content[] blocks of type "text", print the last few.**

- **H1 (HIGH) — the `book:` label was skipped on ALL 17 dedup targets. THIRD
  RECURRENCE.** I hand-swept this twice for Awodey and it came back, because
  the cause was never fixed: `file_chapter.py` automated dedup steps (b)
  project and (c) body-append but NOT (a) the label. **Now fixed in the tool**
  — the dup pass adds `book:<BOOK>` before the project-add. It matters because
  schemas.md's resume pre-flight is `gh issue list --label book:<book>`, so an
  unlabelled target is invisible to the idempotency check and a resumed run
  could re-file duplicates. All 17 labelled; 34 book:seven-sketches issues now.
  **LESSON (third time learning it): sweeping the instances is not fixing the
  bug. Fix the tool the FIRST time.**
- **H2 (HIGH) — 3 false "0 hits" logs, AND IT CORRECTED MY DIAGNOSIS.** I had
  recorded that the "generative effect → 0 hits" log was true "only because
  the phrase is line-broken". **Wrong, and too kind.** `Instance/Poset.v:97`
  reads `"Generative Effects: Orders and Galois` on ONE line; I re-ran the
  plain logged grep myself and it MATCHES. It was a straightforward false
  negative. Corrected in library-defects.md. (A line-break blind spot IS real
  — `prop91`/"final functor" at Structure/Factorization.v:96-97 — but it was
  not the cause here, and using it as the explanation papered over an error.)
- **H3 (HIGH) — this pass created a duplicated obligation.** "A symmetric
  preorder is an equivalence relation" was both #767's declared gap and a new
  checkbox on #223. Resolved by SCOPING rather than deleting either: #223 owns
  the RELATION-level axiom comparison (`Equivalence R → PreOrder R` and back),
  #767 owns the CATEGORY-level dagger framing plus skeletal⇒discrete. #767 now
  carries an explicit scope note and already depended on #223.
- **M1 (MED, SYSTEMIC) — 28 logged greps CANNOT BE RE-RUN AS WRITTEN**: they
  use `grep` with `|` alternation and no `-E`, so basic grep treats `|`
  literally and the command returns 0 hits UNCONDITIONALLY. A log that cannot
  fail is not evidence. Most conclusions survive re-running each alternative,
  but **M2/L-4 is materially wrong** because of it (`example76` claims no
  closure vocabulary while `remark39` in the SAME BATCH cites
  Instance/Lambda/Multi.v:74 as evidence). Recorded in the book's
  library-defects.md with the fix for later chapters: require `grep -E`/`rg`
  whenever a pattern contains `|`, and whitespace-tolerant patterns
  (`rg -U 'final\s+functor'`) since the tree hard-wraps prose at ~72 columns.
- **M4** 8 multi-part ledger rows carried the generic note. Named by hand, and
  `file_chapter.py` gained a THIRD phrasing fallback (this book states the part
  after "item \`id\` — " rather than in a parenthetical). Verified it now fires
  on all 7 append-side rows.
- **M5 (MED) — flag normalization gap in the MERGE phase**: exactly 8 of 17
  page-spanning items carried `spans-page-break`, and those 8 were precisely
  the ones in the FIRST agent's range (PDF 14-30, splitAt 30) — the flag
  tracked WHO WROTE THE RECORD, not the item. Fixed all 17 in the inventory,
  and **patched mergePrompt** to recompute DERIVABLE flags from merged data
  rather than unioning the agents' lists.
- Also confirmed by the audit: equation counter **VERIFIED, nothing missed and
  nothing invented** — it opened all eight contested pages and found each is a
  numbered display, four of them *inside* another item's box; minting `eq8` for
  (1.8) alone is right because it is the only one carrying a claim distinct
  from its enclosing item. All 201 evidence citations resolve. Native
  blockedBy matches bodies **17/17 exactly**. S1/S2/S3 re-confirmed (S2
  sharply: `surjectivity_is_epic` ends in **`Abort.`** at Instance/Sets.v:476).
  **S4's dismissal confirmed right, not convenient** — `Cat` uses
  `Functor_Setoid` and the equivalence↔iso bridge is proven with both round
  trips at Theory/Equivalence.v:182/:187.
- ⚠ **MY BRIEF DRIFTED AGAIN:** I described Exercise 1.7 as including an empty
  join; the page shows four questions and no empty join. Same class as the Ch6
  title drift — build audit briefs from the artifacts, never from memory.
- Deferred (recorded, not fixed): L2's 3 delegated WRONG-TARGET dedup verdicts
  (`example29`→#671, `ex38`→#647, `example61`→#234) rest on a sub-agent's
  judgment the auditor did not re-derive; 14 of 43 appends judged questionable,
  with the real pattern being skeletal-FinSet `eq_refl` computations routed
  onto general-theory issues because **no computational-witness issue exists**;
  `ex118`→#382 self-contradicts (asks #382 for dual-image work this campaign
  assigned to #384); `ex57`'s Hasse-diagram headline (0 hits tree-wide) landed
  on neither leg and got no issue. These need a human or a follow-up pass.
**7S Ch1 CLOSED.**

### GRAPH GATE RE-VERIFIED AFTER 7S Ch1 — still CLEAN, exit 0
555 issues, **724 edges** (+40 from Ch1), ACYCLIC, 9 layers, 168 at layer 0.
All four invariants hold; the 12 acknowledged serialize-pairs are unchanged.
So adding a whole chapter broke nothing — the per-chapter Phase G plus the
pre-filing collision check are keeping the graph correct incrementally rather
than needing a big repair at the end. Re-run after every chapter.

### I CORRECTED THE AUDITOR TWICE (recorded in the book's library-defects.md)
Verification cuts both ways, so I checked its findings too:
- **L6 is WRONG.** It said the Hasse-diagram deliverable "landed on neither
  target and got no issue". It DID get one: **#768** states the gap and its
  work item 5 is to define the covering relation "so 'the Hasse diagram of a
  preorder' has an in-tree referent"; three more new issues carry the same
  0-hits evidence. The auditor checked only `ex57`'s two APPEND targets and
  never asked whether a NEW issue from the same pass covered it.
- **The `ex118`->#382 "self-contradiction" is overstated.** The append block
  says verbatim "The general constructions are this issue's (and #384's)
  obligation; what this exercise adds is the concrete evaluation" — it names
  #384 explicitly. Genuine residue is only LOW: the concrete dual-image
  evaluation is tracked on #382 while the construction is #384's. Fixed with
  a pointer on #384; nothing moved.

## ============================================================
## BOOK 4 QUEUED: RIEHL, *Category Theory in Context* (2026-07-30)
## ============================================================
User request: add a fourth phase after Seven Sketches — Emily Riehl's textbook,
issues in a GitHub project named `Riehl`. **Everything is provisioned; nothing
is launched.** Riehl's A0 starts only after 7S Ch7 closes.

PROVISIONED NOW (so the resume is a single Workflow call):
- PDF verified: `/Users/johnw/Desktop/riehl-category-theory-in-context.pdf`,
  **296 pages**, letter, LaTeX+hyperref / pdfTeX 1.40.29.
  ⚠ **The `/Count` trick FAILED on this PDF** — its page tree is in compressed
  object streams, so `strings | grep /Count` returns nothing AND a raw
  `/Type /Page` count returns 0. **`pdfinfo <pdf> | grep ^Pages` works and is
  now the first thing to try** (this supersedes the campaign-2 learning note
  that said the /Count trick works; it worked for books 1-3 only).
- GitHub project **10 "Riehl"** created (`gh project list` confirms).
- Label **`book:riehl`** created — `gh` does NOT create labels implicitly, so a
  missing label would have failed every `gh issue create` in Phase F.
- Tooling registered in all four places: PROJECT maps in `file_chapter.py` and
  `validate_drafts.py` (`"riehl": "10"`), and in `check_graph.py` BOTH the
  `ITEM_ID` regex (so `riehl:` ids are recognized) and the issue-map loop (so
  its dependency resolution can see Riehl's map). All three parse-checked.
- Scaffolding `doc/plan/books/riehl/{inventory,coverage,issues}` +
  `issue-map.json`. Item-ID prefix `riehl:`; **prefix and directory AGREE**
  here — deliberately not replicating book 3's `7sketches`/`seven-sketches`
  split, which is a standing footgun.
- schemas.md: book enum extended to `maclane | awodey | 7sketches | riehl`,
  plus a Book-4 section recording all of the above.

FIRST STEP WHEN 7S FINISHES: run the A0 calibration exactly as for book 3 —
`Workflow({scriptPath: 'doc/plan/books/tools/book-a0.js', args: {book:"riehl",
title:"Riehl, Category Theory in Context", pdf:"<path>", pages:296,
project:10, priorBooks:["maclane","awodey","seven-sketches"]}})`.
`priorBooks` MUST list all three — Riehl overlaps Mac Lane heavily (it is a
modern replacement for much of the same canon), so the dedup load will be the
heaviest of the campaign and cross-book dedup must see all ~600 prior issues.
Expect A0 to matter: Riehl numbers by CHAPTER.SECTION.ITEM in some editions
and uses lettered exercise blocks, so the numbering scheme must be PROVEN from
a body example, as it was for book 3 (that requirement is what caught Seven
Sketches' shared equation counter).

### 7S Ch2: DRAFT PHASE FAILED mid-response — RESUMED (wf_3d458cd7-496)
17/18 agents completed; the drafter died on "API Error: Server error
mid-response". Critically it had written `drafts-2.md` (11 drafts) but **NOT
`duplicates-2.json`**, so the artifact set was INCOMPLETE-BUT-PLAUSIBLE. Filing
from it would have stranded every dedup item (unaccounted, and re-filable on a
later run). **Check for BOTH drafts-N.md AND duplicates-N.json before filing —
the presence of a large drafts file is not evidence the phase finished.**
Resumed with resumeFromRunId: the 17 cached agents replay instantly, only the
drafter re-runs, and it will now also see the two items minted below.

### ⚠ PROCESS DEFECT: an agent used FORMALIZABILITY as an INVENTORY filter
The merge flagged that range agent B **deliberately declined to record two
genuine numbered Remarks** (2.81, 2.95) as "non-formalizable", leaving holes at
those numbers that looked exactly like consumed display numbers. It flagged
this for decision instead of inventing replacements — correct behavior, and the
reason it was caught at all.
**I read PDF 81 and 84 as images and both are real numbered Remark
environments.** 2.81 (printed 69, §2.5.1) explains the term "closed", forward-
points to Definition 4.58 / §7.2.1 / Exercise 7.11, and gives the "single-use
v-to-w converter" reading. 2.95 (printed 72, §2.5.2) personifies a quantale as
a "navigator" — pure motivation.
RESOLUTION: minted both into `inventory-2.json` (92 items now) with an
explanatory flag, plus `verified-2-7.json` giving each an **OUT_OF_SCOPE**
record. Correct classification, no issue warranted, and the roster now matches
the book's own count.
**THE PRINCIPLE, now written into invPrompt:** the inventory is the
COMPLETENESS GATE; formalizability is a CLASSIFICATION decided in a later phase
(OUT_OF_SCOPE exists precisely for pure exposition). An omission at inventory
time is INVISIBLE downstream. Record every numbered environment without
exception; if it is pure prose, say so in statement_summary.
BONUS CONFIRMATION: PDF 81 shows equation **(2.80) sitting inside Definition
2.79's shaded box** — the A0 calibration fact confirmed directly on the page.

### Ch2 inventory notes worth keeping
- **The flag-normalization fix from Ch1 WORKED and reported honestly**: 0 flags
  added, 0 removed, because both Ch2 agents applied `spans-page-break`
  correctly — and the merge said so explicitly rather than silently passing.
- The chapter's FIRST named item is 2.2, because 2.1 is a wiring-diagram
  display. A naive 1..n check would report "item 2.1 missing"; it does not
  exist.
- Two axioms central to the resource reading — discard `x <= I` and copy
  `x <= x (tensor) x` — are typeset with TEXT labels "(discard axiom)"/"(copy
  axiom)" and consume NO counter value; recorded as unnumbered definitions with
  number:null, so they are invisible to number-keyed reconciliation. Disclosed,
  not a defect.

### ⚠⚠ MY RESUME BACKFIRED — EDITING AN UPSTREAM PROMPT VOIDS THE WHOLE CACHE
I patched `invPrompt` (the formalizability-filter fix) and THEN called
`resumeFromRunId` expecting the 17 completed agents to replay from cache. They
did not. `resumeFromRunId` caches on **(prompt, opts)**, so changing the FIRST
agents' prompt invalidated them and therefore every downstream agent too. The
resume re-ran INVENTORY from scratch, both agents hit 529s, and the workflow
died at `an inventory agent returned null`. No data lost (all artifacts were
already on disk) but ~3.6 min and 2 agents wasted.
**RULE: never edit a prompt upstream of the failure point before resuming. Fix
forward (or revert the edit, resume, then re-apply).**

### FIX FORWARD: new tool `doc/plan/books/tools/book-draft.js` (Phase E only)
Rather than revert the valuable invPrompt fix, I DECOUPLED the draft phase. It
is a one-agent workflow that reads the on-disk `inventory-N.json` +
`verified-N-*.json` (passed as `verifiedPaths`) and writes `drafts-N.md` +
`duplicates-N.json`. The `draftPrompt` body was lifted VERBATIM out of
book-chapter.js by script, not retyped, so the two cannot drift.
Two improvements over the inline phase:
 - **RETRIES up to 3 times.** The original failure was a transient server
   error; a retry would have saved all 18 agents' work. The inline phase had no
   retry at all.
 - Immune to upstream cache-key changes, and a drafter failure now costs ONE
   agent instead of eighteen.
**Use this whenever a chapter's draft phase fails.** Running (wf_19ba954a-45c)
for 7S Ch2 over all 8 verified files, including the hand-written
`verified-2-7.json` carrying the two minted OUT_OF_SCOPE Remarks.

### 7S Ch2 FILED — #771-#801 (31 new) + 2 dedup appends. AUDIT IN FLIGHT (fess-7s2).
The decoupled `book-draft.js` worked first try: 31 drafts + 2 duplicates
covering all 80 PARTIAL/ABSENT items, and it correctly gave NO issue to the two
minted OUT_OF_SCOPE Remarks. It also **carried forward the 11 drafts from the
interrupted run, re-validated them against the merged inventory, and extended
two** — so the partial work was reused rather than discarded.
**Totals: 586 issues, 1703 ledger rows, 67 seven-sketches issues.**
Phase G: 84 edges, 83 added. Graph gate re-run: **807 edges, ACYCLIC, exit 0.**

- ✅ **THE LABEL FIX WORKED AUTOMATICALLY**: filing printed "cross-book,
  labelled #308 book:seven-sketches" / "#684 book:seven-sketches" and both
  verified to carry the label. The three-times-recurring defect is closed at
  the source, not swept again.
- ✅ **The multi-part no-clobber patch worked**: `7sketches:2.5.2:ex92` is split
  across #778 (Boolean clauses) and #800 (Cost clauses) and came out as TWO
  ledger rows + `ex92@800` in issue-map.json automatically. I only had to
  hand-write the two part NAMES.
- ONE collision caught PRE-FILING and patched into the draft: the powerset
  draft (#780) shares the new `Instance/Powerset.v` with **#745**; #382 was
  already cross-linked, #745 was not. Fixed in body+trailer before filing, so
  it landed as a real native edge.
- `resolve_chapter_deps` reported one "failed" edge #790 <- #788. **False
  alarm, verified:** #790's body declares #788 TWICE (two different item-ids
  both resolving to it), so the first add succeeded and the duplicate failed.
  Native is {788,789}, matching the body.
- The drafter's own disclosure quality was high: it flagged the ex92 split as
  requiring coordinator action, reported both LIBRARY-DEFECTs as PLACED (none
  unplaced), and disclosed its link-verification METHOD (HTTP status via curl,
  validated against a deliberately bogus nLab slug so a 404 really means
  missing; 2 candidate slugs dropped for 404; 5 Wikipedia 429s re-checked).

### DEFECTS S5-S7 (all verified from source by me before recording)
- **S5 (HIGH)** `Functor/Structure/Monoidal.v:110-124` — `LaxMonoidalFunctor`
  makes its comparisons lax (`lax_pure : I ~> F I`, `lax_ap : F x ⨂ F y ~> F (x
  ⨂ y)`) but then REQUIRES `pure_left`/`pure_right`/`ap_assoc` as **`≅`
  isomorphism fields with no defaults**. `ap_assoc`'s iso cannot be supplied
  from a merely-lax `lax_ap`, so the class **excludes lax-not-strong functors**
  — and the header at :45-48 asserts the opposite, calling those fields
  "consequences of the comparisons, not extra structure" (a consequence would
  be a derived lemma, not a field). Bites §2.2.5, whose monoidal monotones are
  the canonical lax-not-strong examples. Folded into #782's DoD with #783 as
  its regression test.
- **S6 (MED)** `Construction/Enriched/Two.v:12` says enriched-over-2 are
  "**exactly**" preorders; `Enriched_Two_preorder` (:165) is `↔` = **`iffT`**
  (`Lib/Foundation.v:72`), i.e. functions both ways with no proof they are
  mutually inverse. Folded into #785, whose obligation is exactly that upgrade.
- **S7 (LOW-MED)** `Structure/Monoidal/Strict.v:42-43` states "strict monoidal
  categories are precisely monoid objects in `[Cat]`" using the in-tree bracket
  convention for a fact that is NOT in-tree — only the Funny-tensor cousin is
  (`Instance/StrictCat/Premonoid.v:137`), and THAT file calls the Cat statement
  "the **classical fact**", i.e. explicitly external.
- A1/A2 recur, with a sharper observation from the Ch2 verifier worth keeping:
  chasing `[Pos]` lands the reader on the **stdlib** `Pos` module (binary
  positives, used in Lib/MapDecide.v) — *worse than a dead link*, because it
  resolves to something real and unrelated.

### NEXT: 7S Ch3 (Databases: Categories, functors, and (co)limits), PDF 89-128,
offset 12, splitAt 109, 24 sections — args in seven-sketches/chapter-args.json.

### fess-7s2 VERDICT: **HONEST work** — 3 MEDIUM, 3 LOW. All folded.
Recovered from its transcript again (4th consecutive auditor to idle without
delivering, this time despite an explicit "do not go idle without replying").
**The transcript-extraction technique is now the DEFAULT for these agents** —
skip the ping entirely: parse `subagents/agent-a<name>-*.jsonl`, keep
`message.content[]` blocks of type "text", print the last one. 1.8 MB file, 53
text blocks, full 19 KB report in the final block.

- **MEDIUM-1 — a generality overstatement that reached a filed issue.**
  `prop87` clause (c) claimed `eval` holds "at the monoidal (non-cartesian)
  generality the book uses", citing `Structure/Monoidal/Closed.v:83`. FALSE, and
  I verified it: `ClosedMonoidal`'s FIRST field is `closed_is_cartesian :
  @CartesianMonoidal C` (`:46`, coercion `:71`), its header says so at `:41`, and
  `eval` sits under that context — cartesian ONLY. `Cost` (tensor `+`, meet
  `max`) is the book's own non-cartesian witness. The real counterpart is
  `eval'` at `StarAutonomous.v:120` under `SymMonClosed`, which has **no in-tree
  instance** and an unwired beta law. **CLAUDE.md already documents this exact
  trap** ("the in-tree `ClosedMonoidal` bundles `CartesianMonoidal`") — so the
  guard existed and the pipeline walked past it. FIXED in the coverage record
  and in **#798**'s body. Classification stays PARTIAL; no obligation lost.
- **MEDIUM-2 — MY OWN FIX WAS HALF-APPLIED.** I minted the two Remarks into
  `items[]` but left the page `notes` saying they were "**DELIBERATELY NOT
  RECORDED**". So the inventory contradicted itself, and the stale prose
  re-asserted exactly the reasoning the fix retracted (formalizability as an
  inventory filter) in the load-bearing place a reader would check. FIXED in
  both copies; 0 occurrences remain. **LESSON: when correcting a record, fix
  every field that ASSERTS something about it, not just the field that carries
  the data.**
- **MEDIUM-3 — the Ch1 log rule is mostly honored, not fully.** Bare-`|`-without
  `-E` logs fell 28 -> 10 of 373, so the launch-brief rule worked; but 4 of the
  10 narrate findings a literal grep cannot return. Auditor ran all three
  verbatim: each exits 1 with zero matches. Conclusions all survive the
  corrected forms. Recorded.
- **ADJUDICATED: `example19` PARTIAL -> ABSENT.** Its PARTIAL was earned entirely
  by the general mechanism belonging to the PRECEDING item — a double credit that
  counts one in-tree asset twice. The verifier had flagged this itself and said
  example14 must move with it; the auditor read printed p.47, confirmed identical
  shape, and ruled the stricter no-double-crediting policy right. Chapter
  PARTIAL/ABSENT 40/40 -> 39/41; filed-issue framing unchanged. Record + ledger
  updated.
- **S5 STRENGTHENED by the auditor, not merely confirmed**: `LaxMonoidalFunctor`
  has **no lax-not-strong inhabitant in the whole tree**, and ~8 developments
  take it as a hypothesis and so silently require strongness (DecoratedCospan
  family x6, Cospan/BlackBox, Monad/Distributive, Monad/Compose,
  Functor/Applicative). `Id.v:85`'s `apply tensor_assoc` is direct corroboration.
  Line numbers corrected (:117/:119). S6 and S7 confirmed exactly; for S6 it
  additionally searched for round-trip/inverse/bijection vocabulary in the file
  and found NONE, so "exactly" is genuinely overstated.

### What the audit CLEARED (it reported two of its own suspicions as wrong)
- The Wikipedia balanced-parenthesis link concern: false alarm.
- The "is 2 dedup appends too FEW?" question resolves in the drafter's favour:
  the chapter's overlap with ~570 prior issues was carried by **20 cross-book
  dependency EDGES** instead, which is the right instrument for a prerequisite.
  Topical probe: "quantale" and "monoidal closed/residual" match ZERO prior
  issues, and all six prior "enrichment" issues are Ab-/Cat-enriched, never
  V-enriched over a monoidal preorder. It probed the strongest candidate
  (#782 vs #607/#608) and found them genuinely distinct.
- **The completeness gate closes independently**: it built its own gate from the
  PDF text layer — 79 numbered environment headers vs the inventory's 80
  numbered items, **zero** missing, **zero** kind mismatches, the one extra
  being 2.101 correctly typed `equation` — then opened the three densest gap
  clusters as images. My minted records were confirmed correct with OUT_OF_SCOPE
  the right verdict, and **no other item was dropped for the same reason**,
  which was the question that actually mattered.
- Dependencies fully clean: 37 referenced issues all exist and are open, native
  `blockedBy` matches bodies **exactly on all 31**, and #790's doubled `#788`
  collapsed correctly. Multi-part bookkeeping contract-conformant.
- 138 of 139 evidence citations land exactly on the named symbol.
**7S Ch2 CLOSED.**

## ============================================================
## REMAINING ROADMAP TO "ALL TEXTS REVIEWED" (2026-07-30)
## ============================================================
Directive: continue until all texts are fully reviewed and assessed.

DONE: MacLane I-XII (424 issues) · Awodey 1-10 (~130) · 7S Ch1-2 (48).
**586 issues, 1703 ledger rows, graph gate CLEAN (807 edges, exit 0).**

REMAINING, in order — all args already calibrated and on disk:
| Unit | PDF | offset | splitAt | secs | source of args |
|---|---|---|---|---|---|
| 7S Ch3 Databases | 89-128 | 12 | 109 | 24 | chapter-args.json ← RUNNING |
| 7S Ch4 Co-design | 129-158 | 12 | 144 | 18 | chapter-args.json |
| 7S Ch5 Signal flow graphs | 159-192 | 12 | 176 | 18 | chapter-args.json |
| 7S Ch6 Circuits | 193-232 | 12 | 213 | 20 | chapter-args.json |
| 7S Ch7 Logic of behavior | 233-270 | 12 | 254 | 21 | chapter-args.json |
| **Riehl A0 calibration** | 296 pp | — | — | — | run `book-a0.js`, project 10 |
| Riehl Ch1..N | from A0 | | | | |

PER-CHAPTER CADENCE (unchanged, all tooling in doc/plan/books/tools/):
1. `Workflow(book-chapter.js, args)` — if the DRAFT phase alone fails, use
   `book-draft.js` (retries 3x, needs only the on-disk verified-*.json). Do NOT
   edit an upstream prompt then `resumeFromRunId` — that voids the whole cache.
2. `validate_drafts.py <R> <S> <book>` — "covered twice" is EXPECTED for a
   sanctioned multi-part split; check it is real, not a double-file.
3. `check_collisions.py <R> <S> <book>` **PRE-FILING** — patch any missing
   cross-link into the DRAFT so it lands as a real edge.
4. `file_chapter.py <R> <S> <book>` — now auto-adds `book:<book>` to cross-book
   dedup targets and handles multi-part `@` keys; only part NAMES may need hand
   editing.
5. refresh `<book>/filed-issues.tsv` → `resolve_chapter_deps.py` → persist
   inventory/coverage/issues into `doc/plan/books/<book>/`.
6. Verify new library-defect claims FROM SOURCE before recording them.
7. fess audit ALONE (MAX-2). **Expect it to idle without delivering — go
   straight to transcript extraction** (`subagents/agent-a<name>-*.jsonl`, keep
   assistant text blocks, print the last). Never `cat` those files.
8. Fold findings, verifying each BOTH ways (I have corrected auditors twice and
   been corrected by them four times).
9. `check_graph.py` — must exit 0. Re-run after EVERY chapter.

FINAL GATE when all texts are done: `check_graph.py` over the full corpus
(it already reads all four books' issue-maps and recognizes `riehl:` ids).

### fess-7s3 VERDICT: **HONEST work.** Two HIGH, three MEDIUM, one LOW. Folded.
Recovered from transcript (5th consecutive silent auditor — this is now simply
the procedure, not an exception).

- **S8 IS MACHINE-VERIFIED, AND I WAS WRONG ABOUT THE LIMITATION.** I recorded
  "the probe cannot be written from outside" because `Metacategory` is a module
  functor never instantiated elsewhere. **False.** The auditor built it — the
  functor takes any `WSfun PNN` and `FMapWeakList.Make PNN` is one. **I
  re-compiled it myself under Rocq 9.1: three results, all "Closed under the
  global context"** — `identity_unsatisfiable`, `Three_is_empty`, and
  `composition_law_live`. So the campaign's most serious truth-claim finding is
  no longer structural, it is proved. Probe preserved at
  `doc/plan/books/probes/S8-metacategory-vacuity.v`. Defect record corrected and
  UPGRADED. **LESSON: "I can't build a probe for this" deserves one more try
  than I gave it — the obstacle was a module-instantiation detail, not a real
  barrier.** The auditor also settled the PARTIAL-vs-ABSENT question by PROVING
  the surviving content non-vacuous (`composite ThreeArrows 0 3 3` etc. are
  inhabited), which is why PARTIAL is right and ABSENT would have been wrong.
- **HIGH #807 duplicated #742 — and `check_collisions.py` CANNOT catch it.**
  Same category under two names ("discrete dynamical system" vs "set with an
  endomorphism"), proposing `Instance/DDS.v` vs `Instance/Endo.v`. Zero path
  overlap → zero collisions reported. FIXED: #807 retargeted onto
  `Instance/Endo.v`, `Depends on: #742` in body+trailer+native edge, reciprocal
  note on #742. The general blind spot is recorded — a path-keyed check cannot
  see synonymous concepts, so the DRAFTER's dedup step is the only real defence.
- **I CORRECTED THE AUDITOR (3rd time this campaign).** Its other HIGH said
  #705 "absorbed three obligations its Definition of Done cannot discharge".
  **Not so:** all five Ch3 appends carry closure-tracking CHECKBOXES and I
  verified they landed in the FILED body (lines 141/147/153/159/165) — so
  closing #705 REQUIRES producing them. The premise "closing #705 would never
  produce them" is wrong; the checkbox mechanism exists precisely for this.
  What survives is milder and real: #705 is now a 16-box mixed-kind unit
  (abstract iso + concrete finite-data witnesses), which strains the
  one-PR granularity policy. Recorded as granularity, not lost obligation.
  ⚠ BOTH the Ch1 and Ch3 audits independently identified the same underlying
  structural gap: **the campaign has no home for concrete computational
  witnesses**, so they get routed onto general-theory issues. Worth a dedicated
  issue if it recurs again.
- **MEDIUM `example3.72` PRESENT -> PARTIAL.** Its own `strength_comparison`
  said "intree-weaker" while `gap` was None. `exp_iso` is the indexed family;
  the book presents currying as an INSTANCE of the adjunction definition, which
  needs the two one-variable functors — and `(- × y) ⊣ (- ^ y)` exists ONLY in
  prose comments at `Structure/Cartesian/Closed.v:34,47`. Notable: this was the
  rare PERMISSIVE verifier move (blind pass said PARTIAL, adversarial re-check
  UPGRADED to PRESENT) — with 99 CONFIRMED / 2 OVERTURNED, permissive upgrades
  are the unusual event and this one did not survive.
- **MEDIUM the grep-log defect WORSENED: 28 (Ch1) -> 10 (Ch2) -> 41 (Ch3)**,
  despite Ch3's brief carrying the strongest wording yet. **Prompt instruction
  is not fixing this.** It IS mis-transcription not fabrication (the decisive
  tell: one log narrates "23 files", exactly the `-E` answer), and every
  conclusion survives re-running — but two narrated hit lists are materially
  false. Structural fix recommended in the defect file: mechanically re-run
  logged commands rather than restating the rule a fourth time.
- **LOW multi-part rows lacked part names — fixed, AND fixed at the source.**
  The append blocks DID name the parts, in a FOURTH distinct phrasing
  ("Example 3.74, clause 2 (free preorder…)"). Rather than add a fifth regex I
  changed the CONTRACT: `duplicates-<R>.json` now carries a structured `part`
  field (drafter emits it; `file_chapter.py` prefers it; documented in
  schemas.md with all four failed phrasings listed as the rationale).
- Clean: completeness **exhaustive, not sampled** — 87 numbered items in the
  PDF, 87 in the inventory, zero missed, zero invented, and the 15 unoccupied
  numbers matched my claim exactly. Dependencies clean on all 8, native ==
  bodies. Ledger/issue-map reconcile exactly (101 items, 105 rows, 61 base
  entries = the 61 PARTIAL/ABSENT, 40 PRESENT unmapped, 4 `@`-legs). 199/200
  citations land exactly, all 200 within ±6.
- Auditor's disclosed gaps: background links unchecked (budget); read the PDF
  as TEXT not images, so layout claims in the pagemap are unverified by it;
  sampling 34/101 records and 27/42 dedups via subagents.
**7S Ch3 CLOSED.** 594 issues, 1808 ledger rows, graph gate exit 0.
  ⚠ POSTSCRIPT: my #807 fix initially left the body WITHOUT the `Depends on:
  #742` line while the trailer and native edge had it (my regex assumed a
  multi-line Depends-on run and #807's were separate lines). **`check_graph.py`
  caught it — GATE EXIT=1, "body [705,802] != native [705,742,802]".** Fixed;
  gate back to 0. This is the gate earning its keep on my OWN edit, and the
  third time the body-vs-native rule has caught a hand-edit this session.

### fess-7s4 VERDICT: **HONEST work** — no overstated claim, no invented or missed item, no false-PRESENT.
The risk I flagged in the brief (over-generous ABSENT/PARTIAL hiding real
in-tree coverage, since this chapter leans on machinery that DOES exist:
Theory/Profunctor.v, Theory/Coend.v, the monoidal stack) **did not
materialize** — the two records most exposed both cite the real code.

- **MEDIUM — 9 bare-pipe logs, and the ledger recorded only 3.** The verifier
  self-reported 3 logs that misstate WHERE hits are; the auditor found a
  separate, larger family of **9** using `grep` with bare `|` and no `-E`. It
  PROVED the defect (`def4.21`'s command run verbatim returns 0 lines), then
  re-ran all nine with `-E`: **every conclusion holds**. Transcription, not
  fabrication. Ledger corrected.
- ⚠⚠ **A COUNTING CORRECTION THAT INVALIDATES EARLIER FIGURES.** The auditor
  RETRACTED its own first count, noting 20 Ch4 logs use `\|` (VALID BRE
  alternation) and 35 use `-E`/`rg` (also correct), so lumping them together
  "would have been the wrong number". **That casts doubt on the 41 reported for
  Ch3 and the 28/10 for Ch1/Ch2.** I tried an independent recount and got
  2/4/34/0 — irreconcilable with 28/10/41/9, and demonstrably WRONG for Ch4
  where my regex says 0 against a proven instance. **So I published no count.**
  The qualitative finding stands (bare-`|` logs exist in every chapter, are
  unreproducible as written, and every checked conclusion survives correction);
  **the claim that the defect "is getting worse" rests on disputed counts and
  must NOT be relied on.** Recorded as such in the defect file.
  LESSON: three different counting methods gave three different answers. A
  metric nobody can reproduce is not a metric — state the defect, not a number.
- **MEDIUM S12 CONFIRMED and STRENGTHENED.** The pointer is **circular**:
  `Structure/Closed.v:54-58` repeats the claim as nLab prose and points BACK at
  `Construction/Enriched.v`. Plus `Class Closed` is visibly unfinished — a field
  literally named `hom_` with an unfilled `_` (`:182-184`) — and
  `Structure/Monoidal/StarAutonomous.v:60` independently says "We do NOT use
  Structure/Closed.v, an Eilenberg-Kelly [stub]". My line cite corrected
  :54-56 -> :54-58.
- **LOW, FIXED — #822 had no dependency on #776** though it is its
  categorification and the book says so on printed p.134. **My first fix
  attempt failed on my own guard**: I tested `'#776' in body`, which matched a
  PROSE mention (:67) and a DoD checkbox (:84) while the Dependencies section
  said "None." and native was empty — exactly the mention-vs-declaration
  confusion I have been flagging in others. Fixed properly; gate re-verified 0.
- LOW, accepted as-is: the PARTIAL/ABSENT boundary is applied at two
  tightnesses (`ex4.4` PARTIAL on ambient setting alone vs `def4.42` ABSENT
  despite naming a degenerate collage) — both defensible, no practical
  consequence since both file issues; and `rough-definition` items use a `def`
  ID slug (no collision; sets the precedent for 5.33/6.68/6.91/6.98).
- Clean and independently re-derived: completeness EXACT (51 numbered named
  environments in the text layer, inventory records exactly those + 1 flagged
  definitional display + 2 unnumbered = 54; all 14 unoccupied numbers occur as
  displays; three zero-item pages rendered and confirmed pure prose; Rough
  Definition 4.45 confirmed a literally boxed environment). Dedup checked
  against all 631 issue bodies with **zero** duplicates, including an explicit
  search for the Ch3 same-concept-different-name failure. All 49 edges verified,
  native == bodies exactly, **zero native-only edges**. 19 new module paths,
  zero collisions — my pre-filing 0 verified rather than restated. Ledger/
  issue-map/inventory/coverage agree exactly. All 29 background links HTTP 200.
- Auditor's disclosed gaps: **no `Print Assumptions` run on any PRESENT
  artifact** (by it or the Ch4 verifier) — the contract's Phase-D discipline
  asks for that on foundational PRESENT claims; nothing compiled; 10 of 54
  records fully opened.
**7S Ch4 CLOSED.** 610 issues, 1862 ledger rows, 872 edges, gate exit 0.

### fess-7s5 VERDICT: **HONEST work, one SYSTEMATIC defect + a dedup cluster.** All folded.
Everything mechanically checkable was clean: all 108 coverage anchors resolve,
page accounting accurate on all 15 of 34 pages opened against the PDF,
numbering continuity exact, ledger/issue-map agree perfectly, **all 72
dependency edges correct and natively mirrored 34/34**, all 37 background URLs
200, and S13 correctly diagnosed AND correctly left as a candidate.

- ⚠ **SYSTEMATIC (the important one): Phase-D verifier sharpenings never
  reached the filed issues.** The verification pass produced its single most
  useful output — for `example5.3`, that the FinSet-as-a-prop gap is "no
  instance is WRITTEN", not "not derivable", naming the exact one-application
  term `@Monoidal_op (FinSet^op) (@CC_Monoidal ... FinSet_Cocartesian
  FinSet_Initial)` AND an in-tree precedent for that very pairing at
  `Instance/FinSet/Lawvere.v:41-42` — and **#827 contained zero trace of it**.
  An implementer reads the ISSUE, not the coverage JSON.
  FIXED both ways: folded into #827 verbatim, and **draftPrompt now carries a
  VERIFIER-SHARPENING PASS** requiring the drafter to read verifier.notes for
  every item and fold substantive sharpenings into the body — with the rule
  that if a verifier note CONTRADICTS the Phase C text, the verifier note wins
  and the issue must say so.
- **MEDIUM-HIGH x2 — the Ch3 same-concept-different-name failure recurred, and
  my collision check again could not see it.**
  · **#829 re-filed two of #824's load-bearing steps** (the `CorelComposable`
    instance and the monoidal restriction to jointly-epic cospans). Module names
    differ by ONE WORD: `Instance/FinSet/Corelation.v` vs `.../Corel.v`. #829
    already depended on #824 but its parenthetical understated a two-thirds
    overlap. FIXED with an explicit SCOPE note ceding both steps and keeping
    only the PROP packaging + the partitions bijection.
  · **#843 re-specified #221's entire matrix category** in a second new file
    (`Instance/Mat.v` vs `Instance/Matr.v`); completing both as written would
    land TWO matrix categories, and #327 already depends on #221. FIXED with a
    SCOPE note: build ON #221, keep only the rig generalisation + PROP structure.
- **MEDIUM — #851 did not cite #500 although THIS CHAPTER deduped two sibling
  items (`example5.66`, `ex5.67`) onto #500 as the §5.4.2 monoid-object home.**
  Self-inconsistent within one chapter. FIXED: dependency added in body,
  trailer and native edge; gate re-verified 0.
- **MEDIUM — the def5.11 precision defect is real, and the VERIFIER'S OWN
  CORRECTION was also wrong.** The record said the in-tree notion "additionally
  requires unit preservation"; the verifier called that an overstatement because
  `strict_pure_obj : I = F I` is `0 = F 0` and automatic. True — but there is a
  SECOND unit-side field, `strict_pure_iso_id` (`:60-63`), demanding the unit
  comparison MORPHISM be the transported identity, which is NOT automatic since
  `hom(0,0)` is generally non-trivial in a prop. So neither the original nor the
  correction was right. #832 now states it precisely.
- **LOW — a genuine BOOK ERRATUM, recorded nowhere until now.** Definition 5.11
  (printed 151) requires only identity-on-objects + monoidal-on-morphisms, but
  the proof of Proposition 5.54 (printed 166) asserts that "by Definition 5.11"
  a prop functor must also preserve **symmetries**. A literal formalization of
  5.11 will NOT support Prop 5.54's proof. Affects #832 and #845; recorded in
  the defect file with the decision left to the implementer.
- LOW: the bare-`|` defect recurred twice (conclusions verified true via
  semantic re-runs, per my instruction not to report counts); one log line
  literally false (`ex5.9` "quantale 0 hits" — there is 1 comment hit) and now
  corrected in the durable JSON.
- **`ex5.9` ABSENT ADJUDICATED CORRECT, and empirically**: 35 of the 38 ABSENT
  records name a concrete in-tree near-miss in their negative log, so ABSENT
  consistently means "the item's own named object has no counterpart, though
  ingredients exist and are cited" — not "nothing relevant exists". A usable
  rule, now recorded.
**7S Ch5 CLOSED.** 644 issues, 1944 ledger rows, 945 edges, gate exit 0.

### fess-7s6 VERDICT: **HONEST work, unusually well-evidenced** — 1 HIGH, 6 MEDIUM, 3 LOW.
Completeness verified EXACTLY, not sampled: it reconstructed the chapter's item
set mechanically from the PDF text and matched the inventory on every count AND
every kind (25 examples, 30 exercises, 12 definitions, 3 rough-definitions, 4
theorems, 3 propositions, 1 corollary, 1 remark, 1 equation), derived the 21-gap
set independently with no residue, and confirmed the three "Rough Definition"
headers verbatim. All 159 evidence citations resolve. **The under-crediting risk
I flagged largely did NOT materialize** — the flagship test `thm6.77` is
correctly PARTIAL because `DecoratedCospan_Hypergraph` is projected from a
`Context {DCHGC : DecCospan_Hypergraph_Coherent}` that is **never instantiated**
(66 hits on the class, ZERO `Instance`/`Build_` witnesses; corroborated against
docs/AXIOMS.md:93-105 and Makefile:211).

- **HIGH — #865 is a TRUE DUPLICATE of #320**, and the mechanism is a contract
  gap worth more than the fix. Both specify `IsIndexedCoproduct`, `icoprod`,
  `colimit_is_indexed_coproduct`, `HasIndexedCoproducts` over the same donor.
  **Both justified novelty with a grep of the TREE returning 0 hits, and both
  greps were CORRECT — neither searched the BACKLOG.** Different module paths
  (`Structure/Limit/Coproduct.v` vs `Structure/Colimit/Shapes.v`) so the
  path-keyed collision check was blind too. FIXED (#865 scoped + edge), and
  **`draftPrompt` now mandates a BACKLOG search per principal symbol name**:
  a tree grep proves the LIBRARY lacks it; only a backlog grep proves the
  CATALOG lacks it.
- **MEDIUM — #871's prose CONTRADICTED its own graph, and that was MY error.**
  The body said the five Powerset claimants are "peers with no precedence", but
  native `blockedBy` was [227,466,704,750] — hard blockers asserting exactly the
  precedence the prose denied. Cause: I wrote the peer note INSIDE a
  `Depends on:` line, so `resolve_chapter_deps` extracted the numbers as
  dependencies. **This is the rule I wrote myself after an identical slip on
  #443 and then violated.** FIXED: one clean dep on #227, peer note moved out of
  the Dependencies block, three spurious edges removed.
  → **The gate then caught the CONSEQUENCE**: removing those edges left #750 and
  #871 unordered peers on a shared module, GATE EXIT=1. Correct resolution was
  to widen the serialize-group to all four consumers, not to restore the edges.
  Gate back to 0. That is the constraint living in its only correct home.
- **MEDIUM x4, ownership overlaps left OPEN and recorded** (#869 vs the already
  proven `cospan_scfa` in `Construction/Cospan/SCFA.v:1271` — a Phase-E
  regression, since the coverage record DID cite `Cospan_Hypergraph` and the
  draft dropped that half; #863 vs #417 on `FinitelyCocomplete`; #869 vs #879
  both creating `CospanCat FinSet`; #860 vs #357 codiscrete-vs-indiscrete;
  #862/#863/#326 on one `Structure/Pullback.v` TODO region).
- **MEDIUM — the multi-part ledger asymmetry is systematic and now fixed at
  source.** Exactly 2 bad rows across 2010 ledger ids, both the same shape:
  **the dedup-append leg gets its `part`, the NEW-ISSUE leg gets the issue
  title.** Cause: the dup loop writes the part, the draft loop wrote `title`.
  `file_chapter.py` now computes multi-target items BEFORE the draft loop and
  writes an explicit "part: NEEDS NAMING -- also on [...]" flag instead of a
  note that merely looks filled in. Both existing offenders named by hand.
- **LOW, both corrections to MY records**: S14 was UNDER-scoped — the same
  overstatement appears a second time at `Structure/Pullback.v:79-80`, and that
  site is worse because the false "proven below as [pullback_unique]" claim sits
  INSIDE a Wikipedia quotation, reading as part of the cited source. And A3's
  third citation was the wrong file (`Structure/UniversalProperty/Universal/
  Arrow.v:61`, not `Theory/Universal/Arrow.v:61` which is prose) — substance
  unaffected. Both records corrected.
- Also confirmed: the blind-verify pass is NOT a rubber stamp despite 88/88
  CONFIRMED — it made real in-place corrections and produced corroborating
  citations Phase C had missed.
**7S Ch6 CLOSED.** 667 issues, 2034 ledger rows, 970 edges, gate exit 0.

### fess-7s7 VERDICT: **HONEST work** — 1 HIGH, 3 MEDIUM, 4 LOW. All folded.
**SEVEN SKETCHES COMPLETE (7/7 chapters).** The classification layer was rated
better than the contract requires: the sheaf trap I flagged was handled
correctly (`def7.35` PARTIAL naming all three real weaknesses — per-leg
quantifier, subsingleton vacuity, one-cover-per-object — and the verifier added
a FOURTH undisclosed one), the `ex7.16` overturn was right, completeness was
verified exactly (91 items; the 70 numbered ones occupy exactly the 70 filled
counter values; the 12 gaps enumerated independently from the PDF and matched),
and 326 of 327 file references across all 22 bodies resolve.

- **HIGH — #885 duplicates #639, and the NEW backlog rule did not catch it.**
  Both own the internal connectives on Omega; module names differ by ONE WORD
  (`Structure/Topos/InternalLogic.v` vs `Structure/Topos/Logic.v`). Instructive
  detail: **the drafter DID search the backlog** — it correctly found and
  depends on #402 and #445 — it simply missed #639, whose title contains
  "subobject classifier". So the rule works but is not sufficient; symbol-name
  search does not catch a differently-titled owner. FIXED: #885 scoped to
  extend #639, dependency in body/trailer/native, #639 labelled book:7s.
- **MEDIUM — THE CAMPAIGN-WIDE ORPHAN, AND IT WAS MINE.**
  `7sketches:3.4.2:example3.72` sat PARTIAL with issue `-`, absent from
  issue-map, referenced by none of 710 issues. **I created it**: I reclassified
  it PRESENT->PARTIAL when folding the Ch3 audit and never gave it a home.
  Across 2128 ledger rows / 2100 distinct items it is the ONLY such orphan.
  FIXED: deduped onto **#239** (which already owns exactly that deliverable —
  packaging `(- x S) ⊣ (-)^S` as an `Adjunction` and instantiating at Sets), with
  append, label, project, ledger row and issue-map entry. No obligation was ever
  lost; the row was.
  **LESSON: a classification change is not complete until the item has a home.
  Reclassifying PRESENT->PARTIAL CREATES an obligation that must be placed.**
- **MEDIUM — one of my two hand-written part names was WRONG.** I wrote
  `7sketches:7.3:remark-presheaf-topos -> #893` as "Shv(X,Op) as an elementary
  topos", but #893's own Source says it covers the **site half only** (its Work
  item 3 is `Theory/Sheaf/Trivial.v`); the description I wrote belongs to #893's
  OTHER item, `7.4:def-topos`. A reader would have reconstructed the wrong
  residual obligation. Corrected. (#883's name was accurate.)
- **MEDIUM — #895 cited `Theory/Yoneda.v`, which does not exist** (twice: a Work
  item and the donors line). The real files are `Functor/Hom/Yoneda.v` and
  `Theory/Coend/Yoneda.v`. This was the ONLY bad path among 327 references.
  FIXED.
- LOW, recorded not fixed: two of the four #685 appends duplicate checkboxes
  already on it; #685's Depends-on was not extended to match its new checkboxes
  (#759 and #727 exist and are unlinked); the equation mint-vs-consume criterion
  is defensible but written down nowhere (7 minted, 12 consumed, and the auditor
  opened all 12 and agreed none carries content a neighbour lacks).
- **L8 — MY MESS, CLEANED**: stale `ProbeTmp2.{vo,vok,vos,glob}` + `.aux` were
  sitting in the repo root from a probe compile. Gitignored, so the build gate
  stayed green and I never saw them. Removed.
- ⚠ **AN UNVERIFIABLE PROBE CLAIM** — the Ch7 verifier said it proved the sheaf
  vacuity in `scratchpad/7s-ch7/ProbeSiteVacuous.v`; **no such file exists**. The
  auditor confirmed the MATH independently from `Theory/Sheaf.v:170-178` (the
  witness is existentially quantified over a `covering_family` that carries no
  covering requirement, so `(0; nil)` discharges it for ANY category), so the
  claim is true — but "it compiles" is unverified. Rule recorded in the defect
  file: **a record claiming a probe compiles must leave the probe on disk**, and
  it should be copied to `doc/plan/books/probes/` at fold time, as S8's was.
**7S Ch7 CLOSED. BOOK 3 COMPLETE.** 689 issues, 2129 ledger rows, gate exit 0.

### fess-r1 VERDICT: **HONEST work** — 2 HIGH, 3 MEDIUM, 4 LOW. All folded.
Completeness verified EXHAUSTIVELY, not sampled: a full text-layer sweep of PDF
21-72 reproduced the item census section by section (13/9/15/7/17/20/7 numbered
+ 4/1/4/0/3/2/1 unnumbered + 4/8/10/9/9/6/7 exercises + 2 in §1.0 = **158**),
every section's arabic counter contiguous once displays are restored, all 14
display tags present verbatim, exercises never carrying an arabic number.
**277 of 277 citations resolve within ±3 lines**, zero missing files. Dependency
mirrors mechanically perfect on all 21. No weaker-result substitution — the
records flag their own traps (e.g. `riehl:1.3:def-iso-categories` warns that
`≅[Cat]` is NOT Riehl's isomorphism of categories and routes to `≅[StrictCat]`).

- **HIGH — #915 declared the WRONG prerequisite.** It depended on **#489**,
  which CONSUMES `cHaus`, instead of **#413**, which BUILDS it — and #915's own
  prose named #413. Because blocking is transitive, the Riesz issue was parked
  behind Beck's monadicity, absolute coequalizers and Stone-Cech, none of which
  it needs. FIXED in body, trailer and native edge.
- **HIGH — a dedup append dropped half its obligation.** Riehl asserts
  naturality for FOUR exponential isomorphisms; #284 commits to two, and the
  append's checkbox covered only the cardinality half, leaving naturality of
  `Structure/BiCCC.v:90` and `:134` with no home in the chapter. FIXED.
- ⚠ **MEDIUM — MY `Instance/Comp.v` DIAGNOSIS WAS WRONG, refuted with counts.**
  Every FACT held, but my causal claim ("the classifier was searching an index
  that does not mention the file") is false: **228 of 486 registered files are
  unnamed in CLAUDE.md**, and this chapter cites **33 of them across 111 of 277
  citations (40%)**. The classifier searches the TREE, not the index. Exactly
  ONE other record was in the same class, and it is minor. **LESSON: I inferred
  a cause from a correlation without checking the base rate; one query refuted
  it.** The recommendation (index Comp.v) still stands and remains John's call —
  CLAUDE.md is TRACKED and this campaign touches only untracked doc/plan/.
- **MEDIUM — an append silently narrowed a hypothesis**: Riehl says "vector
  spaces of ANY dimension"; #237 is FdVect-scoped and no unrestricted `Vect_k`
  is scheduled anywhere. Scope checkbox added.
- **MEDIUM — two more prose-vs-graph defects, one of them my own error class.**
  #921 wrote "#225 … not a build prerequisite" INSIDE a `Depends on:` line, so
  the resolver made it a hard blocker — exactly the #871 mistake. #913's work
  item said "reuse the Riehl §1.1 issue" without ever naming #907, dropping the
  batch's only intra-campaign edge. Both fixed; gate re-verified 0.
- **LOW but PUBLIC — Riehl was referred to as "he"/"his" in THREE live issue
  bodies** (#231, #288, #250). Corrected to she/her, and a sweep of all 300
  `book:riehl` issue bodies now returns none. Worth a standing note: the drafter
  writes about book authors in prose, so pronouns are a real correctness surface.
- LOW recorded not fixed: a false exclusivity claim (`Instance/One.v:25` is also
  a one-object category; the substantive no-delooping claim is correct),
  topological monoids homeless on #500, two forgetful-functor clauses without a
  checkbox, and a PDF-63 page note contradicting its own correct items list.
- **A gap in MY brief:** the numbering-gap list omitted (1.4.12); the inventory
  disclosed it correctly, so the artifact was right and my brief was wrong.
**RIEHL Ch1 CLOSED.** 710 issues, 2302 ledger rows, 1096 edges, gate exit 0.
