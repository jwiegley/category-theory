# Phase 15 work order — enriched double categories

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
2. **Branch.** `git checkout -b johnw/ct-phase15` off the tip of the branch
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

### Phase 15 — Enriched upgrade; double categories

**Items 14 and 13 complete.** Branch `johnw/ct-phase15`. Depends on: Phase 5
(equivalence for instance statements), Phase 8 (`Theory/Morphisms/Stability.v`
pasting toolkit, op-dualized for the pushout pasting in file 11's associator
coherence — `HasPushouts` and the pushout accessors themselves are already
in-tree in `Structure/Pushout.v`, per Section 2.5; Phase 8 adds no pushout
artifact). Est. 11 files / ~3600 lines.

**Goal.** V-natural transformations and the (ordinary) category of V-functors;
V=Sets recovering ordinary CT at all three levels; V=2 as the cheap second instance;
Sets-weighted limits with the conical case recovered. Then pseudo double categories
(strict vertical, weak horizontal — the choice that makes the cospan example
possible), companions/conjoints, the squares double category, and cospans.

**Files.**

1. `Construction/Enriched/Natural.v` — V-natural transformations over
   `Construction/Enriched.v`'s `Enriched`/`EnrichedFunctor`:

   ```coq
   Class EnrichedTransform {K : Category} `{@Monoidal K} {C D : Enriched K}
         (F G : EnrichedFunctor K C D) := {
     etransform (x : eobj C) : I ~{K}~> ehom D (efobj F x) (efobj G x);
     enaturality {x y : eobj C} :
       ecompose D ∘ (etransform y ⨂ efmap F) ∘ (unitor conjugation)
         << ehom C x y ~~> ehom D (efobj F x) (efobj G y) >>
       ecompose D ∘ (efmap G ⨂ etransform x) ∘ (unitor conjugation)
   }.
   ```

   The typed-equality notation `<< A ~~> B >>` (already used by Enriched.v for
   exactly this unitor-conjugation situation) is mandatory here; componentwise
   setoid.
2. `Construction/Enriched/Compose.v` — routine: identity and composition of
   V-functors, whiskering of `EnrichedTransform`.
3. `Construction/Enriched/Fun.v` — the ordinary category `[C, D]_V` of V-functors
   and V-natural transformations (vertical composition via `ecompose` and unitors;
   associativity from K's coherence). NOTE (ledger entry 11): the hom-OBJECTS
   (making it a V-category) need ends in K and underlying-category machinery — the
   ordinary category is what this phase delivers.
4. `Construction/Enriched/Sets.v` — extend the proven round trips with
   `EnrichedTransform Sets ... ↔ (F ⟹ G)` (Transform), completing "V=Sets recovers
   ordinary CT" at the category/functor/transformation levels (the first two are
   in-tree: `Category_is_Enriched_over_Set`, `Functor_is_Enriched_over_Set`).
5. `Instance/Two/Monoidal.v` — cartesian monoidal structure on the walking arrow
   `_2` (tensor = meet; terminal = TwoY): small and mechanical, the base for file 6.
6. `Construction/Enriched/Two.v` — `Enriched _2` categories are preorders
   (`eobj` + a hom-valued truth value; `ecompose` = transitivity, `eid` =
   reflexivity); enriched functors = monotone maps. The promised cheap second
   instance.
7. `Structure/Limit/Weighted.v` — Sets-weighted (co)limits by representability
   (honest scope stated in the header: ordinary weights, full V-weights ledgered):

   ```coq
   Program Definition HomDiagram {J C : Category} (c : C) (F : J ⟶ C) : J ⟶ Sets.
     (* j ↦ {| carrier := c ~{C}~> F j |} *)
   Class WeightedLimit {J C : Category} (W : J ⟶ Sets) (F : J ⟶ C) := {
     wlim_obj : C;
     wlim_iso (c : C) : @Isomorphism Sets
       [[[J, Sets]]](W, HomDiagram c F)
       {| carrier := c ~{C}~> wlim_obj |};
     wlim_natural {c c'} (h : c' ~> c) ... (* precomposition square *)
   }.
   Theorem conical_weighted `(F : J ⟶ C) :
     WeightedLimit (constant terminal weight) F ↔ Limit F.
   Definition WeightedColimit ... (* by op *)
   ```

   (The constant weight comes from `Functor/Diagonal.v`'s constant functor at the
   terminal setoid.) The conical theorem is the item's named deliverable.
8. `Theory/DoubleCategory.v` — PSEUDO double categories (strict vertical category,
   weak horizontal composition mediated by invertible globular squares — this
   hosts BOTH Sq and Cospan):

   ```coq
   Class DoubleCategory := {
     dcat : Category;                             (* objects + vertical morphisms *)
     dhor : dcat → dcat → Type;                   (* horizontal 1-cells *)
     dsq {a b c d : dcat} :
       dhor a b → (a ~{dcat}~> c) → (b ~{dcat}~> d) → dhor c d → Type;
     dsq_setoid ... : Setoid (dsq h u v k);
     dsq_coerce {...} (eu : u ≈ u') (ev : v ≈ v') : dsq h u v k → dsq h u' v' k;
     dsq_coerce_id / dsq_coerce_trans : ... (* proof irrelevance, Phase 10 pattern *)
     dsq_vid {a b} (h : dhor a b) : dsq h id id h;
     dsq_vcomp : dsq h u v k → dsq k u' v' l → dsq h (u' ∘ u) (v' ∘ v) l;
     (* strict vertical laws stated through dsq_coerce *)
     dhid (a : dcat) : dhor a a;
     dhcomp {a b c} : dhor b c → dhor a b → dhor a c;
     dsq_hcomp : dsq h u v k → dsq h' v w k' → dsq (dhcomp h' h) u w (dhcomp k' k);
     dinterchange : ... ;
     dassoc {a b c d} (f : dhor a b) (g : dhor b c) (h : dhor c d) :
       (* invertible globular square (identity verticals) between the two
          horizontal composites *) ;
     dunit_left / dunit_right : ... ;
     dcoherence_pentagon / dcoherence_triangle : ... (* at square level *)
   }.
   ```

   (The `dsq_coerce` design is the Phase 10 `dtransport` pattern re-applied; note
   it in the header.)
9. `Theory/DoubleCategory/Companion.v` — companions and conjoints (binding squares
   + the two zigzag identities), uniqueness up to canonical invertible square.
10. `Construction/Sq.v` — the double category of commuting squares of C: horizontal
    AND vertical 1-cells are C-morphisms; `dsq h u v k := (k ∘ u ≈ v ∘ h)` — squares
    are `≈`-propositions, so the square setoid is trivial and ALL coherence fields
    are automatic. Theorems: every morphism has a companion and a conjoint (itself,
    transposed). This instance is the class's reuse audit — develop in lockstep
    with file 8.
11. `Construction/Cospan/Double.v` — the cospans double category over
    `HasPushouts C` (the in-tree Structure/Pushout.v accessors by name):
    horizontal 1-cells = cospans, horizontal composition by chosen pushouts,
    squares = cospan morphisms commuting with the verticals; associator/unitor
    globular squares from the pushout UMP. Cross-reference
    `Construction/Cospan/Category.v` (the existing 1-category). QUARANTINE: the
    pentagon-level coherence of the pushout associator is the phase's hard proof
    (paste pushout squares via Phase 8's `Theory/Morphisms/Stability.v` toolkit,
    op-dualized — the phase's only Phase 8 input); FALLBACK (named): land the data, unit squares, and
    unitality, escalate the associator coherence per Section 6.4 (ledger entry 8).
    Monoidal double categories: header note only (ledger entry 9, per item 13's own
    scoping).

**Completion checklist.**

| Deliverable | File |
|---|---|
| `EnrichedTransform`, `enaturality` | Construction/Enriched/Natural.v |
| V-functor compose/id, whiskering | Construction/Enriched/Compose.v |
| `Enriched_Fun` (the category) | Construction/Enriched/Fun.v |
| `EnrichedTransform_is_Transform` (Sets level) | Construction/Enriched/Sets.v |
| `Two_Monoidal` | Instance/Two/Monoidal.v |
| `Enriched_Two_preorder` (both directions) | Construction/Enriched/Two.v |
| `HomDiagram`, `WeightedLimit`, `conical_weighted`, `WeightedColimit` | Structure/Limit/Weighted.v |
| `DoubleCategory` with `dsq_coerce`, `dinterchange`, coherence | Theory/DoubleCategory.v |
| `Companion`, `Conjoint`, uniqueness | Theory/DoubleCategory/Companion.v |
| `Sq`, companion/conjoint theorems | Construction/Sq.v |
| `Cospan_Double` (+ possible ledger-8 escalation) | Construction/Cospan/Double.v |

`Print Assumptions` closed for `conical_weighted`, `Enriched_Two_preorder`, `Sq`,
and whatever of `Cospan_Double` lands.

**Risks and fallbacks.** (a) `enaturality` unitor plumbing — the typed-equality
notation is mandatory; budget it. (b) The double-category class fighting setoid
1-cells — resolved by design (`dsq_coerce`); if the general class still fights,
specialize `dhor` to carry its own setoid from the start (Sq and Cospan need only
that) and record the decision. (c) Cospan coherence — staged, fallback named in
file 11.

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
