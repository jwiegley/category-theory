# Phase 9 work order — monadicity

> **Standalone AI work order. Prerequisite reading: `doc/plan/00-CONVENTIONS.md`
> (binding rules, gates, definition of done) and `doc/plan/00-INDEX.md`
> (dependency graph, branch layout, execution lessons from phases 5–6).**
> The body below is the authoritative, red-teamed specification extracted
> verbatim from the master plan `doc/classical-completion-plan.md`. Do not
> paraphrase the Coq skeletons — implement against them and against the real
> current source of every donor file cited (the source is authoritative where
> it and a skeleton disagree; record such deltas as deviations).

## How to execute this phase (the loop that built phases 5–6)

1. **Baseline.** Confirm the prerequisite phases (see "Depends on" below) are
   built into the tree (`ls` a representative `.vo`). If `.vo` are missing or
   read-only (nix-store copies), run
   `find . -name '*.vo' -exec chmod u+w {} +` then `nix develop -c make -jN`.
   `coqc` is often off PATH — use `nix develop -c coqc` or the pinned store
   binary recorded in 00-INDEX.
2. **Branch.** `git checkout -b johnw/ct-phase9` off the tip of the branch
   this phase depends on (or off `master`/latest if that is already merged).
3. **Implement** each file in the dependency order in "Files" below. One agent
   per file at the configured concurrency (phases 5–6 ran MAX=1 due to credit
   limits — see 00-INDEX). Every file is MANDATE-PROTECTED: no
   `Admitted`/`admit`/`Axiom`/`Parameter`/`Conjecture`/`Unset *Checking`; the
   only sanctioned deferrals are the named fallbacks in this phase's "Risks".
   Comments must avoid the make-todo words `fail/fails/failure/abort/admit/`
   `admits/undefined/jww` (case-insensitive).
4. **Verify.** Clean-delete-and-recompile the new `.vo` in dependency order;
   `Print Assumptions` must report "Closed under the global context" for every
   artifact named in the checklist's assumptions line; the make-todo pattern
   must be silent on the new files.
5. **Adversarial review** (per-file + a checklist-fidelity pass) → refutation →
   fix. Then walk this phase's **Completion checklist** row by row, grep + read,
   confirming full strength (not a weakened form).
6. **Integrate.** Add each file to `_CoqProject` (explicit list, coqdep handles
   order); add the `CLAUDE.md` Key Files entry if the phase introduces a new
   headline module; `nix develop -c make` must be green.
7. **Portability harvest.** In a detached worktree, keep-going build under
   `nix develop <repo>#category-theory_8_19` then `_8_20`; fix any
   Rocq-9-only stdlib name with a local shim (see 00-INDEX "Portability").
8. **Gates.** `nix build` and `nix flake check` (capture the REAL exit code —
   `${pipestatus[1]}` in zsh, or run un-piped; a bare `| tail; echo $?`
   reports tail's status, not the command's).
9. **Commit** one atomic commit per file, each paired with its `_CoqProject`
   line; a `docs(CLAUDE)` commit last; `LEFTHOOK_EXCLUDE=nix-build,nix-check`.
10. **fess audit** the phase's commits with a SEPARATE evaluator; fold real
    findings back in. Then this phase is done; open its stacked PR only when a
    human authorizes the push.

## Definition of done for this phase

Every "Completion checklist" row hits at full strength · all §2.2 gates green ·
8.19/8.20 harvests clean · `nix build` + `nix flake check` green · fess audit
passed · branch rebased cleanly on its base. Never lower the bar; the AdamekData-
style named fallbacks are the ONLY sanctioned scope reductions and they never
weaken a theorem statement.

---

### Phase 9 — Monadicity

**Item 6 complete.** Branch `johnw/ct-phase9`. Depends on: Phase 5 (equivalences,
`ReflectsIsos`), Phase 6 (EM adjunction, including its Moore.v `@TAlgebra`
pre-step repair — files 3-6 here construct EM objects and need it), Phase 8
(`IsCoequalizer` API). Est. 8 files / ~3400 lines.

**Goal.** Split and reflexive coequalizers in the setoid setting, the Eilenberg-Moore
comparison functor, crude monadicity FULLY proven, Beck's precise monadicity theorem
(both directions), and adjoint lifting in the crude case.

**Files.**

1. `Structure/Coequalizer/Split.v` —

   ```coq
   Record SplitCoequalizer {C : Category} {x y : C} (f g : x ~> y) := {
     scoeq_obj : C;
     scoeq_e : y ~> scoeq_obj;  scoeq_s : scoeq_obj ~> y;  scoeq_t : y ~> x;
     scoeq_law1 : scoeq_e ∘ f ≈ scoeq_e ∘ g;
     scoeq_law2 : scoeq_e ∘ scoeq_s ≈ id;
     scoeq_law3 : f ∘ scoeq_t ≈ id;
     scoeq_law4 : g ∘ scoeq_t ≈ scoeq_s ∘ scoeq_e
   }.
   Theorem split_coequalizer_is_coequalizer :
     ∀ (S : SplitCoequalizer f g), IsCoequalizer f g (scoeq_obj S) (scoeq_e S).
   Theorem functor_preserves_split `(F : C ⟶ D) :
     SplitCoequalizer f g → SplitCoequalizer (fmap[F] f) (fmap[F] g).  (* absoluteness *)
   ```

2. `Structure/Coequalizer/Reflexive.v` — reflexive pairs (common section
   `s` with `f ∘ s ≈ id ∧ g ∘ s ≈ id`), `Class HasReflexiveCoequalizers`.
3. `Monad/Comparison.v` — for `F : D ⟶ C`, `U : C ⟶ D`, `A : F ⊣ U` (mind the
   orientation: F is the LEFT adjoint; the monad `U ◯ F` lives on D):

   ```coq
   Program Definition EM_Comparison {C D} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
     C ⟶ EilenbergMoore (U ◯ F) := {|
     fobj := fun c => (U c; {| t_alg := fmap[U] (@counit _ _ _ _ A c) |})
   |}.
   Theorem EM_Comparison_Forget : EM_Forget (U ◯ F) ◯ EM_Comparison A ≈ U.
   Theorem EM_Comparison_Free   : EM_Comparison A ◯ F ≈ EM_Free (U ◯ F).
   Definition Monadic {C D} (U : C ⟶ D) :=
     ∃ (F : D ⟶ C) (A : F ⊣ U), EquivalenceOfCategories (EM_Comparison A).
   ```

4. `Monad/Monadicity/BeckObjects.v` — the engine room: for an algebra `(a, α)` the
   canonical reflexive pair `(F α, counit (F a)) : F (U F a) ⇉ F a`, the split
   coequalizer of its U-image, and the two shared pillars: `EM_Forget` reflects isos,
   and `EM_Forget` CREATES coequalizers of U-split pairs (stated concretely: given a
   pair whose image under `EM_Forget` has a `SplitCoequalizer`, there is a chosen
   algebra structure on the split coequalizer object making it a coequalizer in
   `EilenbergMoore`, uniquely).
5. `Monad/Monadicity/Crude.v` — the crude monadicity theorem, fully proven:

   ```coq
   Theorem crude_monadicity {C D} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
     `{@HasReflexiveCoequalizers C}
     (pres : ∀ ..., PreservesColimit ... U)   (* U preserves reflexive coequalizers *)
     (refl : ReflectsIsos U) :
     EquivalenceOfCategories (EM_Comparison A).
   ```

   Quasi-inverse: an algebra maps to the coequalizer of its canonical pair; the
   unit/counit natural isos come from `ReflectsIsos` + split absoluteness (file 1).
6. `Monad/Monadicity/Beck.v` — the precise theorem:

   ```coq
   Class CreatesUSplitCoequalizers {C D} (U : C ⟶ D) := {
     create_coeq {x y} (f g : x ~> y)
       (S : SplitCoequalizer (fmap[U] f) (fmap[U] g)) :
       { q : C & { e : y ~> q & IsCoequalizer f g q e
           ∧ (* U-image matches S up to the canonical iso *) ... } };
     create_coeq_unique : ...
   }.
   Theorem beck_monadicity : F ⊣ U → CreatesUSplitCoequalizers U →
     EquivalenceOfCategories (EM_Comparison A).
   Theorem monadic_creates : (* converse: EM_Forget creates U-split coequalizers,
     transported along any equivalence over D *) ...
   ```

7. `Monad/Lifting.v` — adjoint lifting along monadic functors, crude case: given
   monadic `U : C ⟶ D`, a functor between the bases with a left adjoint, and
   reflexive coequalizers upstairs, lift the left adjoint to the EM/monadic side.
   Scoped to the crude hypotheses (what applications use).
8. `Monad/Monadicity/Examples.v` — routine sanity: the identity monad's comparison
   is an equivalence; cross-reference note that Moore.v's header promises are now
   fully discharged (comment update commit).

**Completion checklist.**

| Deliverable | File |
|---|---|
| `SplitCoequalizer`, `split_coequalizer_is_coequalizer`, `functor_preserves_split` | Structure/Coequalizer/Split.v |
| reflexive pairs, `HasReflexiveCoequalizers` | Structure/Coequalizer/Reflexive.v |
| `EM_Comparison`, both triangle theorems, `Monadic` | Monad/Comparison.v |
| `EM_Forget` reflects isos; creates U-split coequalizers | Monad/Monadicity/BeckObjects.v |
| `crude_monadicity` | Monad/Monadicity/Crude.v |
| `CreatesUSplitCoequalizers`, `beck_monadicity`, `monadic_creates` | Monad/Monadicity/Beck.v |
| `adjoint_lifting` | Monad/Lifting.v |
| identity-monad witness | Monad/Monadicity/Examples.v |

`Print Assumptions` closed for `crude_monadicity`, `beck_monadicity`,
`adjoint_lifting`.

**Risks and fallbacks.** Beck-precise final assembly (transport of algebra structure
along created coequalizers) is among the campaign's longest proofs. QUARANTINE
(binding): land files 1-5 and 7-8 first; attempt `Beck.v` last. If it overruns the
phase budget, `Beck.v` moves WHOLE (statement + creation class + partial lemma
stack, all compiling, no holes — simply not yet concluding the top theorem, which is
then withheld from the commit) to a fast-follow on this branch or the head of the
Phase 10 branch, tracked as a MISSING escalation (Section 6.4) and ledger entry 17.
Crude monadicity and adjoint lifting are non-negotiable in-phase.

---

---

## Post-implementation appendix (added for standalone execution)

**Commit-series shape.** Reuse the incremental `_CoqProject` technique proven in
phases 5–6: save the fully-registered `_CoqProject`, `git checkout` it, then per
file `perl`-insert its one line at the correct anchor, `git add <file>
_CoqProject`, commit. Bundle any sanctioned existing-file edit (e.g. a donor
repair or a header retirement named in this phase) into the SAME commit as the
new file that motivates it.

**PR.** Base this phase's PR on the previous phase's branch (stacked). In the PR
body, disclose every deviation from the plan explicitly (host moves, named
fallbacks taken, any duplication of existing in-tree constructs discovered) — a
frozen plan can be wrong about what already exists; verify each "absent in-tree"
claim with a grep before building a parallel construct.

**If interrupted** (credits/session/context): the workflow journal replays
completed agents from cache on resume; leave `doc/wiggum-handoff.md` current
(phase status + attempt counters) so a fresh session re-baselines and continues.
