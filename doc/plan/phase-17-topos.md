# Phase 17 work order — topos

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
2. **Branch.** `git checkout -b johnw/ct-phase17` off the tip of the branch
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

### Phase 17 — Topos theory

**Item 11 complete.** Branch `johnw/ct-phase17`. Depends on: Phase 8 (pullback
toolkit, mono stability). Est. 10 files / ~3600 lines.

**Goal.** Subobjects as a setoid (the setoid IS the quotient of monos), the `Sub`
functor, subobject classifiers, elementary toposes with derived power objects, the
FinSet witness (computable products, exponentials, classifier), the honest
cross-universe statement for Sets (upgrading the note at `Instance/Sets.v:348` from
comment to theorem), and the category of sheaves over the existing `Site`.

**Files.**

1. `Theory/Subobject.v` —

   ```coq
   Record SubObj {C : Category} (x : C) := {
     sub_dom : C;
     sub_mono : sub_dom ~> x;
     sub_is_monic : Monic sub_mono
   }.
   Program Instance SubObj_Setoid {C} (x : C) : Setoid (SubObj x) := {
     equiv := fun u v =>
       { i : sub_dom u ≅ sub_dom v & sub_mono v ∘ to i ≈ sub_mono u }
   }.
   ```

   plus the preorder `sub_le` (factorization of one mono through another) and
   `equiv ↔ mutual sub_le` (the factorizations are inverse by monicity).
2. `Theory/Subobject/Functor.v` — for `@HasPullbacks C`: reindexing by chosen
   pullbacks (`monic_pullback_stable`, Phase 8), `Sub : C^op ⟶ Sets` with
   `Sub x := {| carrier := SubObj x |}`; functoriality up to the setoid is where
   Phase 8's pasting lemmas earn their keep.
3. `Structure/SubobjectClassifier.v` —

   ```coq
   Class SubobjectClassifier (C : Category) `{@Terminal C} `{@HasPullbacks C} := {
     Ω : C;
     truth : 1 ~> Ω;
     char {u x} (m : u ~> x) (M : Monic m) : x ~> Ω;
     char_respects : (* in m, up to subobject equivalence *) ;
     char_pullback {u x} (m : u ~> x) (M : Monic m) :
       (* the square (u → 1, m, truth, char m) is a pullback: a Pullback record
          witness for (char m) and truth whose Pull is iso to u aligning legs *) ;
     char_unique {u x} (m : u ~> x) (M : Monic m) (h : x ~> Ω) :
       (* that square with h in place of char m is a pullback *) → h ≈ char m M
   }.
   Theorem classifier_classifies `{@SubobjectClassifier C} (x : C) :
     @Isomorphism Sets (Sub x) {| carrier := x ~> Ω |}.
   ```

4. `Structure/Topos.v` — `Class ElementaryTopos := { topos_terminal;
   topos_cartesian : @Cartesian C; topos_pullbacks : @HasPullbacks C;
   topos_closed : @Closed C _; topos_classifier : @SubobjectClassifier C _ _ }`.
   Here `Closed` is `Structure/Cartesian/Closed.v`'s class (sectioned over
   `` `{@Cartesian C} ``, so `@Closed C _` is exactly its shape — the
   `Coq_Closed : @Closed Coq _` precedent in `Instance/Coq.v`; NOT the stub
   `Structure/Closed.v`, Section 2.5). Finite limits are carried EXPLICITLY as
   terminal+products+pullbacks (the pullback-as-product+equalizer reduction is a
   known in-tree gap; do not assume it — state the class with what instances can
   supply). Derived: power objects `Pow a := Ω ^ a` via
   `Structure/Cartesian/Closed.v`'s exponentials (`y ^ x` in object scope,
   `exp_iso`/`curry`/`eval`), with the relations iso
   `Sub (a × b) ≊ (b ~> Pow a)` from `classifier_classifies` + currying.
5. `Instance/FinSet/Product.v` — computable products on skeletal FinSet:
   `m × n := (m * n)%nat` with `fin_pair`/`fin_unpair` codecs mirroring
   `fin_split`/`fin_join`'s closed-computation style (local shims for any
   version-divergent `Fin`/arith names — Section 2.3); `FinSet_Cartesian`,
   `FinSet_Terminal` alignment.
6. `Instance/FinSet/Closed.v` — computable exponentials: `n ^ m` by enumeration
   codecs `Fin (n ^ m) ≃ (Fin m → Fin n)` (tabulation as digit lists);
   `eval`/`curry` laws pointwise-decidable; `FinSet_Closed` instantiating
   `Structure/Cartesian/Closed.v`'s `Closed` class (not the stub
   `Structure/Closed.v` — Section 2.5).
7. `Instance/FinSet/Classifier.v` — `Ω := 2`, `truth := const F1`; `char` by
   decidable image-membership (`Fin` equality is decidable; monos in FinSet are
   injections — mirror `injectivity_is_monic` from `Instance/Sets.v`);
   `char_pullback`/`char_unique` by case analysis; `FinSet_Pullbacks` computed
   (subset-as-count codecs) either here or in file 5, whichever keeps both under
   budget.
8. `Instance/FinSet/Topos.v` — assembly: `FinSet_Topos : ElementaryTopos FinSet`
   from files 5-7. The library's honest, universe-clean topos witness.
9. `Instance/Sets/Classifier.v` — the cross-universe THEOREM for Sets (not an
   instance — none is possible at a single level): monos in `Sets@{o}` are
   classified in `Sets@{o+1}` with Ω the setoid of propositions-up-to-iff at level
   o; state the strongest true cross-level `char`/pullback statement as theorems,
   cite and upgrade the `Instance/Sets.v:348` note (comment edit in the same
   commit). Header spells out why `SubobjectClassifier Sets` at one level is not
   claimable.
10. `Theory/Sheaf/Category.v` — the category of sheaves over the EXISTING `Site`
    (one covering family per object — its acknowledged weakness is restated in the
    header, honestly scoping what follows): `Sheaves` as the full subcategory of
    `Presheaves C Sets` on the `Sheaf` predicate via `Construction/Subcategory.v`
    (`Full` by construction, hence `Full`/`Faithful` inclusion via
    `Full_Implies_Full_Functor`); repleteness of the predicate (sheaf transported
    across iso of presheaves). Sheafification: ledger entry 1.

**Completion checklist.**

| Deliverable | File |
|---|---|
| `SubObj`, `SubObj_Setoid`, `sub_le`, equiv-iff-mutual | Theory/Subobject.v |
| `Sub` functor | Theory/Subobject/Functor.v |
| `SubobjectClassifier`, `char`, `char_pullback`, `char_unique`, `classifier_classifies` | Structure/SubobjectClassifier.v |
| `ElementaryTopos`, `Pow`, relations iso | Structure/Topos.v |
| `fin_pair`/`fin_unpair`, `FinSet_Cartesian` | Instance/FinSet/Product.v |
| `FinSet_Closed` | Instance/FinSet/Closed.v |
| `FinSet_Classifier` (+ FinSet pullbacks) | Instance/FinSet/Classifier.v |
| `FinSet_Topos` | Instance/FinSet/Topos.v |
| cross-universe Sets classifier theorems; Sets.v:348 upgraded | Instance/Sets/Classifier.v |
| `Sheaves`, full/faithful inclusion, repleteness | Theory/Sheaf/Category.v |

`Print Assumptions` closed for `classifier_classifies`, `FinSet_Topos` (or its
staged components), the Sets cross-universe theorems, and `Sheaves`.

**Risks and fallbacks.** (a) FinSet exponentials are the quarantined combinatorial
grind (codec arithmetic across Coq versions). FALLBACK (named): land Product.v +
Classifier.v first — "finite limits + classifier" verified — and stage
Closed.v/Topos.v as the phase's final commits; if the codecs slip past budget, the
classifier and products land and `FinSet_Topos` moves to a fast-follow on this
branch per Section 6.4 (ledger entry 17); the classifier/Sub/topos-definition core
of item 11 is already satisfied. (b) `Sub` functoriality needs the Phase 8 pasting
lemmas — the dependency is real and the phase order enforces it.

**Universe note (item 11).** The central hazard of the campaign. No
`SubobjectClassifier Sets` instance at one level is possible or claimed; the
cross-universe theorem file is the honest Sets story and FinSet is the genuine
elementary-topos witness. `Print Universes` on files 4 and 9 is part of review.

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
