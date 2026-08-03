# Phase 14 work order — aft reflective localization

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
2. **Branch.** `git checkout -b johnw/ct-phase14` off the tip of the branch
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

### Phase 14 — Adjoint functor theorems; reflective subcategories; localization

**Items 7 (GAFT/SAFT half) and 9 complete.** Branch `johnw/ct-phase14`. Depends on:
Phase 5 (preservation vocabulary, RAPL, equivalences), Phase 6 (monad machinery for
idempotent monads), Phase 8 (`Orthogonal`), Phase 11 (`IsEqualizer` API). Est. 11
files / ~3800 lines.

**Goal.** GAFT with solution sets, concluded through the PROVEN in-tree
universal-arrow assembly (`Theory/Universal/Arrow.v`'s
`AdjunctionFromUniversalArrows`); SAFT as a corollary with its classical hypotheses
packaged as data; reflective/coreflective subcategories on
`Construction/Subcategory.v` with the idempotent-monad correspondence; and
orthogonal-subcategory localization with its universal property.

**Files.**

1. `Instance/Discrete.v` — `DiscreteCat (A : Type) : Category` (`hom x y := x = y`,
   `homset := Morphism_equality`, explicit `@{o h p}` binders per rule 2.4.11);
   `DiscreteCat_Functor : (A → C) → (DiscreteCat A ⟶ C)`; sanity lemma relating to
   the existing PREDICATE `Discrete` in `Structure/Discrete.v` (distinct notion —
   name nothing `Discrete` here).
2. `Structure/Limit/Product.v` — indexed products as limits over `DiscreteCat A`,
   with Fork-style accessors `iprod`, `iprod_proj`, `iprod_ump` insulating GAFT from
   cone plumbing.
3. `Theory/WeaklyInitial.v` — weakly initial families and the crux lemma:

   ```coq
   Record WeaklyInitialFamily (C : Category) := {
     wif_index : Type;
     wif_obj : wif_index → C;
     wif_cover (c : C) : { i : wif_index & wif_obj i ~> c }
   }.
   Theorem initial_from_weakly_initial `(W : WeaklyInitialFamily C)
     (P : (* iprod of wif_obj, file 2 *)) (E : (* HasEqualizers C, Phase 11 API *)) :
     @Initial C.
   ```

   (Product of the family, then the equalizer-of-all-endomorphisms argument.
   Remember `@Initial C` is notation for `@Terminal (C^op)` — build accordingly.)
4. `Construction/Comma/Limit.v` — creation of limits in `(=(d) ↓ U)` from limits in
   C when U preserves them (`comma_proj`-based; `Structure/Limit/Preservation.v`
   vocabulary; the phase's heavy plumbing). Name: `Comma_Complete`.
5. `Adjunction/GAFT.v` — layered (binding):

   ```coq
   Record SolutionSet {C D : Category} (U : C ⟶ D) (d : D) := {
     sol_index : Type;
     sol_obj : sol_index → C;
     sol_arr : ∀ i, d ~> U (sol_obj i);
     sol_covers {c} (h : d ~> U c) :
       { i : sol_index & { t : sol_obj i ~> c & fmap[U] t ∘ sol_arr i ≈ h } }
   }.
   Theorem GAFT_from_initials {C D} (U : C ⟶ D)
     (H : ∀ d : D, @Initial (=(d) ↓ U)) : { F : D ⟶ C & F ⊣ U }.
     (* immediate from Theory/Universal/Arrow.v's proven assembly *)
   Theorem GAFT {C D} (U : C ⟶ D)
     (comp : @Complete C) (cont : PreservesAllLimits U)
     (sols : ∀ d, SolutionSet U d) : { F : D ⟶ C & F ⊣ U }.
     (* solution set ⇒ weakly initial family in the comma category (file 4 gives
        its completeness) ⇒ initial object (file 3) ⇒ GAFT_from_initials *)
   ```

6. `Adjunction/SAFT.v` — SAFT as a GAFT corollary with hypotheses as data (no size
   machinery exists in the library — the packaging IS the honest reading, stated in
   the header): `Record SubobjectIndex` (a chosen small indexing of subobjects —
   self-contained here; Phase 17's `SubObj` setoid is not needed), `Record
   Cogenerator`; theorem builds the solution set from subobjects of products of the
   cogenerating family.
7. `Construction/Reflective.v` —

   ```coq
   Record Reflective {C : Category} (S : Subcategory C) := {
     reflective_full : Construction.Subcategory.Full S;   (* full subcategory *)
     reflector : C ⟶ Sub S;
     reflective_adj : reflector ⊣ Incl S
   }.
   Definition Coreflective {C} (S : Subcategory C) := (* dual via C^op *)
   ```

   plus the counit-is-iso lemma for full reflective subcategories. (Sub's
   first-projection homsets make the adjunction `≈`-goals tractable — the Centre.v
   precedent.)
8. `Construction/Reflective/Idempotent.v` —
   `Class IdempotentMonad {C} (M : C ⟶ C) `{@Monad C M} :=
   { idem_join_iso {x} : IsIsomorphism (@join C M _ x) }` with the equivalent
   characterizations as lemmas; THEOREMS: a reflective subcategory induces (via
   `Adjunction_Monad`) an idempotent monad; an idempotent monad yields a reflective
   subcategory (`sobj x := IsIsomorphism (ret[M] x)`-fixed points, reflector via
   Phase 6's machinery), with the EM category equivalent (Phase 5) to that
   subcategory.
9. `Construction/Localization.v` — orthogonal-subcategory localization: for a
   `MorphismClass W`, `WLocal x := ∀ {a b} (w : a ~> b), W _ _ w →
   IsIsomorphism (precomposition on [Hom ─,x])` (stated with `Functor/Hom.v`'s
   contravariant hom and Sets isos); the full subcategory `C_W` of W-local objects
   via `Construction/Subcategory.v`; when `C_W` is `Reflective`, the reflector
   inverts W (unit at local objects).
10. `Construction/Localization/Universal.v` — the universal property: for reflective
    `C_W`, any `G : C ⟶ E` sending W to isos factors through the reflector up to
    natural iso (`≈` of functors), uniquely. Header states honestly: this is the
    orthogonal-subcategory form; zig-zag calculus of fractions is descoped (ledger
    entry 15, permitted by item 9's wording).
11. `Adjunction/GAFT/Examples.v` — routine integration test: re-derive one known
    adjunction from GAFT-from-initials (cheapest honest witness: the diagonal ⊣
    product adjunction on a complete base, or the comma-initial route for
    `Kleisli_Free`).

**Completion checklist.**

| Deliverable | File |
|---|---|
| `DiscreteCat`, `DiscreteCat_Functor` | Instance/Discrete.v |
| `iprod`, `iprod_proj`, `iprod_ump` | Structure/Limit/Product.v |
| `WeaklyInitialFamily`, `initial_from_weakly_initial` | Theory/WeaklyInitial.v |
| `Comma_Complete` | Construction/Comma/Limit.v |
| `SolutionSet`, `GAFT_from_initials`, `GAFT` | Adjunction/GAFT.v |
| `SubobjectIndex`, `Cogenerator`, `SAFT` | Adjunction/SAFT.v |
| `Reflective`, `Coreflective`, counit-iso lemma | Construction/Reflective.v |
| `IdempotentMonad`, correspondence both ways | Construction/Reflective/Idempotent.v |
| `WLocal`, `C_W`, reflector-inverts-W | Construction/Localization.v |
| `localization_universal` | Construction/Localization/Universal.v |
| GAFT integration witness | Adjunction/GAFT/Examples.v |

`Print Assumptions` closed for `GAFT`, `SAFT`, `localization_universal`, and the
idempotent-monad correspondence.

**Risks and fallbacks.** (a) `Comma_Complete` is the quarantined chunk (limit
creation through sigma-shaped comma homs). The GAFT layering above is the fallback
BY CONSTRUCTION: `GAFT_from_initials` is provable immediately from the in-tree
assembly; if comma-limits slip, it and file 3 still land and the gap is the single
named lemma, escalated per Section 6.4 (ledger entry 17). (b) The
equalizer-of-endomorphisms limit in file 3 is hom-indexed — universe-sensitive;
keep the product/equalizer inputs as explicit hypotheses (as skeletoned) rather
than routing through `Complete` inside the proof, so smallness stays caller-chosen.
(c) `Complete C` in GAFT quantifies over all diagram categories; if polymorphic
instantiation fights at the comma category, FALLBACK: restate `GAFT`'s completeness
input as the two specific limit families used (indexed products over `sol_index` +
equalizers) — textbook-honest, recorded in the header.

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
