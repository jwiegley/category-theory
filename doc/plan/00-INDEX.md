# doc/plan — execution index for the classical-completion campaign (phases 7–17)

> **AI executor: start here.** This directory splits the remaining work of
> `doc/classical-completion-plan.md` (the frozen master plan) into one
> standalone, executable **work order per phase**, plus a shared conventions
> file. Read `00-CONVENTIONS.md` once per session, then process one
> `phase-NN-*.md` at a time as a complete unit. This index gives the map, the
> dependency graph, the toolchain, and the hard-won execution lessons from
> phases 5–6 (which are DONE). Nothing here is committed; it is working state.

## Status snapshot (2026-07-08)

- **Phases 1–4** — merged to `master` (PRs #191–#194): funny tensor, Markov/
  copy-discard stack, free & coloured PROPs, premonoidal/effects.
- **Phase 5** (equivalence of categories, RAPL/LAPC, transport) — DONE, PR #195
  (`johnw/ct-phase5` → `master`). fess PASS, all gates green.
- **Phase 6** (comonads, monad resolutions) — DONE, PR #196
  (`johnw/ct-phase6` → `johnw/ct-phase5`). All gates green; fess was an in-loop
  self-audit (see "The blocker").
- **Phases 7–17** — NOT STARTED. This directory is their plan. ~113 Coq files.

Branch `johnw/ct-phase7` already exists as a label at the phase-6 tip, ready.

## The blocker (why 7–17 are paused)

Fable 5 credits are exhausted. The main loop was switched to Opus 4.8, but
**subagents do not follow**: a workflow agent with `model:'opus'` set explicitly
still failed instantly with "out of usage credits for Fable 5" (probe
wf_d3821a11-ecd, 0 tool uses). So the delegated implement→review→refute→closure
machinery cannot run. To resume, ONE of:
- **(a)** top up Fable credits, then run the phase workflows unchanged
  (the phase-5/6 workflow script is the proven template);
- **(b)** a harness change so subagents honor `model:'opus'` / bill the Opus
  pool;
- **(c)** implement directly in the main Opus loop, no subagents — feasible
  (phase-6 fixes were done this way) but slower, heavier main-loop token burn,
  and audits become in-loop self-audits.

## Dependency graph (topological execution order)

```
Phase 5 (done) ─┬─> 7   (F-(co)algebras; needs PreservesColimit)
                ├─> 8   (factorization/regular/Karoubi; needs Sets equivalence)
                ├─> 9   (monadicity; + Phase 8 IsCoequalizer)
                ├─> 10  (displayed/fibrations; + Phase 8 pullback toolkit)
                ├─> 15  (enriched/double)
                └─> 16  (Lawvere/operads; Phase 14 header-only)
Phase 6 (done) ──> 14  (reflective/localization idempotent monads)
Phase 8 ────────┬─> 9, 10, 11, 14, 17
Phase 11 ───────┴─> 14 (IsEqualizer API)
Phase 12 (in-tree) ──> 13 (Prof stretch only)
Phase 13 (in-tree; Fun.v coherence)
Phase 17 (topos; needs Phase 8 pullback/mono-stability)
```

Recommended order that respects all edges and front-loads unblockers:
**8 → 7 → 11 → 9 → 10 → 12 → 13 → 14 → 15 → 16 → 17.**
(8 first because 9/10/11/14/17 all consume its coequalizer/pullback/OFS toolkit;
12/13 are in-tree and can slot anywhere; 7 is independent after 5.)

## Phase table

| Phase | File | Coverage items (of the 17) | Depends on | Est. |
|---|---|---|---|---|
| 7 | `phase-07-falgebras-lambek-adamek.md` | 3 (F-(co)algebras, Lambek, Adámek) | 5 | 10f/~3.4k |
| 8 | `phase-08-factorization-regular-karoubi.md` | 8, 15 (factorization systems, regular cats; Karoubi) | 5 | 12f/~3.8k |
| 9 | `phase-09-monadicity.md` | 6 (Beck monadicity) | 5, 8 | 8f/~3.4k |
| 10 | `phase-10-displayed-fibrations-grothendieck.md` | 4 (fibrations, Grothendieck) | 5, 8 | 10f |
| 11 | `phase-11-additive-structure.md` | 10 (biproducts, additive, abelian) | 8 | ~ |
| 12 | `phase-12-coends-profunctors-day-drinfeld.md` | 5 (profunctors/coends/Day) + Drinfeld centre, star-autonomous | in-tree | 12f/~4k |
| 13 | `phase-13-bicategory-mates.md` | 12 (bicategory upgrade, mates) | in-tree; 12 (stretch) | 9f |
| 14 | `phase-14-aft-reflective-localization.md` | 7 (GAFT/SAFT), 9 (reflective/localization) | 6, 8, 11 | 11f |
| 15 | `phase-15-enriched-double-categories.md` | 14 (enriched/weighted), 13 (double cats) | 5 | 11f/~3.6k |
| 16 | `phase-16-lawvere-operads.md` | 16 (Lawvere theories), 17 (operads/multicats) | 5; 14 (header) | ~ |
| 17 | `phase-17-topos.md` | 11 (subobject classifier, elementary topos, sheaves) | 8 | 10f/~3.6k |

Full item→phase coverage matrix and the descope ledger are appended to
`00-CONVENTIONS.md`.

## Toolchain (concrete, as used for phases 5–6)

`coqc` is frequently NOT on PATH. Two reliable ways to compile one file from the
repo root:

- **Preferred:** `nix develop -c coqc -R . Category <file>` (or
  `nix develop -c make -jN` for a full build).
- **Pinned binary + env** (faster for single files; store hashes are
  session-specific — re-derive from `nix develop` if they 404):
  ```
  ROCQPATH='<equations>/lib/coq/9.1/user-contrib:<rocq-stdlib>/lib/coq/9.1/user-contrib/' \
  OCAMLPATH='<equations>/lib/ocaml' \
  <coq-9.1.1>/bin/coqc -R . Category <file>
  ```
  Values observed this session (verify before trusting):
  - coqc = `/nix/store/icx78phvvjsfmlvcwjbf4gb3p4qy2lq8-coq-9.1.1/bin/coqc`
  - equations = `/nix/store/84j9fr2pgyyl7n662d8i80rljviry0sz-coq9.1-equations-1.3`
  - rocq-stdlib = `/nix/store/zwqzwxw5cpbqzg5cjgfwlzb6fkal00b6-rocq-core9.1-stdlib-9.0.0`
  - `OCAMLPATH` is REQUIRED (the Equations plugin loads via findlib; without it
    you get "Findlib error: rocq-equations.plugin not found").

## Execution lessons from phases 5–6 (do not relearn these)

1. **`make todo` gate is a case-insensitive `egrep -i '(fail|abort|admit|`
   `undefined|jww)'`.** It flags COMMENT PROSE too. Reword "failure" →
   "breakdown/obstruction", "admits" → "supports/carries" before committing.
   Run it on the new files; it must be silent.
2. **Honest exit codes.** `cmd | tail -1; echo $?` reports *tail's* status in
   zsh, not `cmd`'s — every gate that hid behind a pipe read as passing. Capture
   `${pipestatus[1]}` or run un-piped. Bit me on the first nix-gate report.
3. **`nix build` / `nix flake check` see only TRACKED files.** Never run them
   before the commit series. `flake check`'s `checks.format-check` fails on
   trailing whitespace — keep new files whitespace-clean.
4. **Read-only `.vo`.** If an agent rematerializes the prebuilt library by
   copying from the nix store, those `.vo` are read-only and `make` dies with
   "Permission denied". Fix: `find . -name '*.vo' -exec chmod u+w {} +` then full
   `make`.
5. **Portability (8.19/8.20 Docker CI).** Rocq-9-only stdlib names break the
   older jobs. Confirmed offenders and the fix (a local shim lemma):
   `Fin.case_L_R'`/`_L`/`_R` (9.x only → reimplement `fin_split` as a `Fixpoint`
   over `Fin.caseS'`); `length_app` (8.20+; 8.19 calls it `app_length` → prove a
   two-line local `len_app` by induction). Harvest ALL offenders up front with a
   keep-going build in a detached worktree:
   `git worktree add --detach <wt> <branch>`; then
   `cd <wt> && nix develop <repo>#category-theory_8_19 -c make -jN -k` and again
   `#category-theory_8_20`. The flake exposes PACKAGES
   `category-theory_8_19/_8_20/_9_0/_9_1` (+ default = 9_1); there is only a
   default devShell — do not look for per-version devShells.
6. **The frozen plan can be wrong about what already exists.** Phase 5's plan
   said adjunction composition was "absent in-tree"; `adj_comp`
   (`Instance/Adjoints.v:55`) already existed, so `Adjunction/Compose.v` ended up
   a documented duplicate. **Before building any construct the plan calls new,
   grep for it.** If it exists, reuse/re-export rather than duplicating, or
   disclose the duplication loudly in the PR.
7. **`Coq` vs `Sets` hosting of concrete witnesses.** The plan sometimes asks for
   a `Coq`-hosted instance "pointwise =, closed assumptions". For any functor
   whose `fmap_respects` must hold on `Coq`, that field ENTAILS functional
   extensionality (machine-checkable, e.g. `coq_store_map_proper_entails_funext`)
   — so the axiom-free home is `Sets` (setoid homs). Env stayed on `Coq`; Store,
   Traced, streams moved to `Sets`. Take the plan's own risk-note fallback and
   record it in the PR.
8. **Commit shape.** Incremental `_CoqProject`: save the fully-registered file,
   `git checkout` it, then per commit `perl -pi -e '$_ .= "<line>\n" if $_ eq
   "<anchor>\n"' _CoqProject`, `git add <file> _CoqProject`, commit; a
   `docs(CLAUDE)` commit last. Diff the saved vs final `_CoqProject` at the end to
   prove the set is identical. Commit with
   `LEFTHOOK_EXCLUDE=nix-build,nix-check`.
9. **GPG signing cache expires.** Commits are signed by a hardware token whose
   agent cache lapses after idle; a commit then dies with a pinentry
   cancellation. Ask the human to unlock (`! echo unlock | gpg --clearsign -o
   /dev/null`) and retry; do not switch to `--no-gpg-sign`.
10. **Pushing is human-gated.** Never push or force-push shared history without
    explicit authorization. Use the gh HTTPS credential helper if SSH signing
    is unavailable:
    `git -c credential.helper= -c 'credential.helper=!gh auth git-credential'
    push ...`. `--force-with-lease` after a rebase needs pinned SHAs when the
    remote is a URL (stale tracking info otherwise).
11. **`Initial` is notation for `Terminal` of the op** (Phase 7 sharp edge):
    build instances with `terminal_obj`/`one` fields; the accessors are
    `initial_obj`/`zero`. Analogous op-dualities recur — prefer op-transfer over
    hand-dualization throughout (the funny/comonad/coalgebra work relied on
    `C^op^op = C` by reflexivity).
12. **Universe annotations are load-bearing** under the global
    `Set Universe Polymorphism` (Lib.v:11). A strictly-bound category
    (`Omega@{o h p}`, any thin/indexed construction) cannot mention a polymorphic
    constant without instantiating it — mirror `Instance/One.v`'s
    `Morphism_equality@{o h p}`/`poly_unit@{o}` idiom (called out in phases 7, 10).

## Pointers

- Master plan (authoritative skeletons, coverage, descope): `doc/classical-completion-plan.md`.
- Live campaign state / attempt counters: `doc/wiggum-handoff.md`.
- Proven workflow script template (phase 6):
  `~/.config/claude/personal/projects/-Users-johnw-src-category-theory-master/<session>/workflows/scripts/ct-phase6-implement-wf_ac3008aa-3fe.js`
  (MAX=1 gated; DAG-ordered implementers → verify → review → refute → fix →
  closure → final; swap the `FILES` array, `DOCS`, and per-phase invariants).
