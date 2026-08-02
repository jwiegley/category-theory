# Phase 13 work order — bicategory mates

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
2. **Branch.** `git checkout -b johnw/ct-phase13` off the tip of the branch
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

### Phase 13 — Bicategory upgrade, Cat as bicategory, mates

**Item 12 complete.** Branch `johnw/ct-phase13`. Depends on: in-tree (Fun.v
coherence stack); Phase 12 only for the ledgered Prof stretch. Est. 9 files /
~3600 lines.

**Goal.** Finish `Theory/Bicategory.v` (data-only since 2018) with unitors,
associator, and coherence; pseudofunctors, lax/oplax transformations, modifications;
adjunctions in a bicategory and the mates correspondence; Cat as the motivating
instance riding `Instance/Fun.v`'s associator/unitor/whiskering lemma stack.

**Files.**

1. `Theory/Bicategory.v` — REFACTOR IN PLACE (verified: only comment-level
   consumers in `Construction/Span/Category.v` and `Construction/Cospan/Category.v`;
   re-run the grep before editing — if a code consumer has appeared, switch to the
   additive-subclass fallback `Bicategory_Coherent` and record the decision in the
   commit message). Add fields; change no existing field, notation, or instance:

   ```coq
   hcomp2 {x y z} {g g' : bicat y z} {f f' : bicat x y}
     (θ : g ~{bicat y z}~> g') (η : f ~{bicat x y}~> f') :
     hcompose (g, f) ~{bicat x z}~> hcompose (g', f') :=
     fmap[@hcompose x y z] ((θ, η));         (* definitional Godement whiskering *)
   hunit_left  {x y} (f : bicat x y) : hcompose (bi1id, f) ≅[bicat x y] f;
   hunit_right {x y} (f : bicat x y) : hcompose (f, bi1id) ≅[bicat x y] f;
   hassoc {w x y z} (h : bicat y z) (g : bicat x y) (f : bicat w x) :
     hcompose (hcompose (h, g), f) ≅[bicat w z] hcompose (h, hcompose (g, f));
   hunit_left_natural / hunit_right_natural / hassoc_natural : ... ;
   hcoherence_triangle : ... ;
   hcoherence_pentagon : ...
   ```

   Delete the 2018 TODO comment block; rewrite the STATUS header (no longer
   data-only). Provide `Build_Bicategory'` deriving what symmetry permits.
2. `Theory/Bicategory/Pseudofunctor.v` — `Class Pseudofunctor (B B' : Bicategory)`:
   `pf0 : bi0cell B → bi0cell B'`; hom-functors
   `pf1 {x y} : bicat B x y ⟶ bicat B' (pf0 x) (pf0 y)`; unitor/compositor isos
   `pf_id {x} : pf1 bi1id ≅ bi1id` and
   `pf_comp {x y z} (g f) : pf1 (hcompose (g, f)) ≅ hcompose (pf1 g, pf1 f)`;
   `pf_comp_natural`; hexagon (`pf_assoc_coherence`) + two unit squares. Identity
   and composite pseudofunctors.
3. `Theory/Bicategory/Lax.v` — lax and oplax transformations between pseudofunctors
   (1-cell components + structure 2-cells + unit/composition coherence);
   pseudonatural := lax with iso components (mixin).
4. `Theory/Bicategory/Modification.v` — modifications; the setoid of lax
   transformations.
5. `Theory/Bicategory/Adjunction.v` — adjunctions inside a bicategory: 1-cells
   `f : bicat x y`, `u : bicat y x` with unit/counit 2-cells and the two triangle
   2-cell equations stated through `hcomp2`/`hassoc`/unitor conjugation (this is why
   file 1 comes first); uniqueness of adjoints up to invertible 2-cell.
6. `Theory/Bicategory/Mates.v` — the mates correspondence: given adjunctions
   `f ⊣ u` (x,y) and `f' ⊣ u'` (x',y') and 1-cells `a : x → x'`, `b : y → y'`, the
   bijection (an `Isomorphism` in Sets of 2-cell setoids) between
   `2cells (hcompose (f', a)) (hcompose (b, f))` and
   `2cells (hcompose (a, u)) (hcompose (u', b))`, by pasting with unit/counit;
   round trips by the triangle identities. (Functoriality of mates under pasting
   beyond the bijection: ledger entry 10.)
7. `Instance/Cat/Bicategory.v` — Cat as a bicategory: `bi0cell := Category`,
   `bicat C D := [C, D]`, `hcompose` from `Compose`/`nat_hcompose`/whiskering;
   unitors from `nat_λ`/`nat_ρ` — RECONCILE the reversed-naming convention flagged
   in `Instance/Fun.v`'s comment explicitly; associator `nat_α`; pentagon/triangle
   discharged from `nat_α_nat_α`, `nat_α_whisker_*`, `whisker_left_right`. This
   instance is the reuse audit of file 1's field shapes — develop it in lockstep
   with file 1 before Qed-ing either.
8. `Instance/Cat/Bicategory/Adjunction.v` — adjunctions in Cat-the-bicategory
   coincide with `F ∹ U` (Adjunction/Natural/Transformation.v), hence with `⊣`;
   mates in Cat unfold to the `⌊−⌋`/`⌈−⌉` transposes — the payoff making mates
   usable by ordinary-CT files.
9. `Theory/Bicategory/OneObject.v` — routine sanity: a monoidal category is a
   one-object bicategory (exercises every new field cheaply).

**Completion checklist.**

| Deliverable | File |
|---|---|
| `hcomp2`, `hunit_left/right`, `hassoc`, naturality, `hcoherence_triangle`, `hcoherence_pentagon`; no TODO markers remain | Theory/Bicategory.v |
| `Pseudofunctor`, identity/composite | Theory/Bicategory/Pseudofunctor.v |
| `LaxTransformation`, `OplaxTransformation`, pseudonatural mixin | Theory/Bicategory/Lax.v |
| `Modification` + setoid | Theory/Bicategory/Modification.v |
| `BicatAdjunction` + uniqueness | Theory/Bicategory/Adjunction.v |
| `mate`, `mate_roundtrip_left/right` | Theory/Bicategory/Mates.v |
| `Cat_Bicategory` | Instance/Cat/Bicategory.v |
| `Cat_BicatAdjunction_iff`, Cat mates unfolding | Instance/Cat/Bicategory/Adjunction.v |
| `Monoidal_OneObject_Bicategory` | Theory/Bicategory/OneObject.v |

`Print Assumptions` closed for `Cat_Bicategory`, `mate`, and the Cat adjunction
correspondence.

**Risks and fallbacks.** (a) Cat's pentagon can sprawl at the whisker-algebra level
— prove it componentwise (`transform`-level), where both sides reduce to
`fmap[F] id`-juggling; remember `nat_id`'s component is `fmap[F] id`, not `id` (the
standing trap), and use `Build_Transform'` + `cat`. (b) General mates is long —
FALLBACK (named): file 8's Cat-specific mates (direct, via `⌊−⌋`/`⌈−⌉` algebra)
lands even if file 6's general bijection slips to a follow-on commit within the
phase; Section 6.4 applies. (c) The in-place refactor's audit-first rule in file 1
is binding.

**Universe note (item 12).** `Cat_Bicategory` puts `bi0cell := Category@{o h p}`
one level up — the same pattern as `Instance/Cat.v` itself. Keep the instance a
Definition (registration-free), keep the Bicategory class's levels free per field
group, and never form the bicategory of bicategories. `Print Universes` on files 1
and 7 is part of review.

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
