# Phase 8 work order — factorization regular karoubi

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
2. **Branch.** `git checkout -b johnw/ct-phase8` off the tip of the branch
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

### Phase 8 — Factorization systems, regular categories, images; pullback toolkit; Karoubi envelope

**Items 8 and 15 complete.** Branch `johnw/ct-phase8`. Depends on: Phase 5 (Karoubi's
Sets equivalence). Est. 12 files / ~3800 lines.

**Goal.** Orthogonality and orthogonal factorization systems over morphism classes,
(StrongEpi, Mono), regular categories (kernel pairs, regular epis, pullback
stability) with the (RegularEpi, Mono) image factorization, wired to
`Theory/Morphisms.v` and `Instance/Fact.v`; the pullback pasting/stability toolkit
that Phase 17 also needs; cofork accessors for coequalizers (consumed here and by
Phase 9); and the Karoubi envelope with its universal property and Cauchy
completeness for Sets.

**Files.**

1. `Theory/Morphisms/Classes.v` — routine:
   `Definition MorphismClass (C : Category) := ∀ x y : C, (x ~> y) → Type` plus named
   classes `MonoClass`, `EpiClass`, `IsoClass`, `SplitEpiClass`, `SplitMonoClass`
   (wrapping `Monic`/`Epic`/`IsIsomorphism`/`Retraction`/`Section`) and inclusion
   lemmas.
2. `Theory/Orthogonality.v` —

   ```coq
   Class Orthogonal {C : Category} {a b x y : C} (e : a ~> b) (m : x ~> y) := {
     ortho_lift {u : a ~> x} {v : b ~> y} (comm : m ∘ u ≈ v ∘ e) :
       ∃! d : b ~> x, (d ∘ e ≈ u) ∧ (m ∘ d ≈ v)
   }.
   Notation "e ⫫ m" := (Orthogonal e m) (at level 70) : category_theory_scope.
   ```

   plus closure lemmas: isos orthogonal to everything (both sides), closure of the
   left class under composition, cobase change stubs deferred to file 4's toolkit,
   retract closure (via `Section`/`Retraction`).
3. `Structure/Coequalizer.v` — the elementary cofork API insulating consumers from
   `Parallel`-diagram plumbing:

   ```coq
   Record IsCoequalizer {C : Category} {x y : C} (f g : x ~> y) (q : C) (e : y ~> q) := {
     cofork : e ∘ f ≈ e ∘ g;
     coeq_desc {z} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) : ∃! u : q ~> z, u ∘ e ≈ h
   }.
   (* conversions both ways with Coequalizer (APair f g)  — i.e. Colimit —
      plus uniqueness-up-to-iso of coequalizers *)
   Class HasCoequalizers (C : Category) := {
     coeq {x y} (f g : x ~> y) : ∃ q e, IsCoequalizer f g q e }.
   ```

4. `Theory/Morphisms/Stability.v` — the pullback toolkit (`Structure/Pullback.v`'s
   Record form has none of this): pasting lemmas (given two side-by-side squares
   with the left one a `Pullback`, the outer rectangle is a `Pullback` iff the right
   square is), `monic_pullback_stable` (the pullback projection along a mono is
   monic; pulling back a mono yields a mono), iso stability, and the
   `pullback_unique`-based transport lemmas the later files chase diagrams with.
   Front-loaded deliberately: files 7-8 here and Phase 17's `Sub` functor consume it.
5. `Structure/Factorization.v` —

   ```coq
   Record Factorization {C : Category} {x y : C} (f : x ~> y)
          (E M : MorphismClass C) := {
     fact_mid : C;
     fact_e : x ~> fact_mid;   fact_e_in : E _ _ fact_e;
     fact_m : fact_mid ~> y;   fact_m_in : M _ _ fact_m;
     fact_comm : fact_m ∘ fact_e ≈ f
   }.
   Class OFS {C : Category} (E M : MorphismClass C) := {
     ofs_e_respects : (* E closed under ≈ *) ;  ofs_m_respects : (* M *) ;
     ofs_factor {x y} (f : x ~> y) : Factorization f E M;
     ofs_orth {a b x y} (e : a ~> b) (m : x ~> y) : E _ _ e → M _ _ m → e ⫫ m
   }.
   ```

   plus uniqueness-of-factorization up to unique iso (two `ortho_lift`s), E and M
   determine each other, and the `Instance/Fact.v` connection: every
   `Factorization f` is an object of `Fact f`, and any two OFS-factorizations of `f`
   are canonically isomorphic there (giving `Fact.v`'s dangling initial/terminal
   comment its first real content).
6. `Structure/Factorization/StrongEpi.v` — `StrongEpi f := Epic f × (∀ m monic, f ⫫ m)`;
   composition/cancellation; split epi ⇒ strong epi (`Retraction`); strong epi +
   mono ⇒ iso.
7. `Structure/Regular.v` — kernel pairs and the class:

   ```coq
   Definition kernel_pair {C} `{@HasPullbacks C} {x y} (f : x ~> y) := pullback f f.
   Record RegularEpi {C : Category} {x y : C} (f : x ~> y) := {
     regepi_dom : C;  regepi_p1 regepi_p2 : regepi_dom ~> x;
     regepi_is_coeq : IsCoequalizer regepi_p1 regepi_p2 y f
   }.
   Class Regular (C : Category) := {
     regular_terminal  : @Terminal C;
     regular_pullbacks : @HasPullbacks C;
     regular_coeq {x y} (f : x ~> y) :
       (* chosen coequalizer of f's kernel pair *) ;
     regular_stable : (* pullback of a RegularEpi along any morphism is RegularEpi *)
   }.
   ```

   plus regular epi ⇒ strong epi ⇒ epi.
8. `Structure/Regular/Factorization.v` — regular ⇒ (RegularEpi, Mono) OFS: image :=
   coequalizer of the kernel pair; the comparison to `y` is monic (THE
   pullback-stability argument, using file 4); registered as `OFS RegularEpiClass
   MonoClass` (name `Regular_OFS`).
9. `Instance/Sets/Image.v` — the concrete image in Sets: sub-setoid
   `{ y | ∃ x, f x ≈ y }` (proof-relevant sigma), factorization
   (surjection-onto-image, injection). Note: this needs no epis-are-surjections (the
   Aborted lemma in `Instance/Sets.v`) — the factorization is direct.
10. `Construction/Karoubi.v` —

    ```coq
    Program Definition Karoubi (C : Category) : Category := {|
      obj := ∃ x : C, { e : x ~> x & e ∘ e ≈ e };
      hom := fun x y => { f : `1 x ~> `1 y &
               (`1 (`2 y) ∘ f ≈ f) ∧ (f ∘ `1 (`2 x) ≈ f) };
      homset := fun x y => {| equiv := fun f g => `1 f ≈ `1 g |};
      id := fun x => (`1 (`2 x); _);          (* the idempotent is the identity *)
      compose := fun _ _ _ f g => (`1 f ∘ `1 g; _) |}.
    Program Definition Karoubi_Embed {C} : C ⟶ Karoubi C.   (* x ↦ (x, id) *)
    ```

    `Full`/`Faithful` instances for the embedding (the REAL classes from
    Theory/Functor.v); every `Idempotent` in `Karoubi C` splits, witnessed with
    `SplitIdempotent` from `Theory/Morphisms.v` by name.
11. `Construction/Karoubi/Universal.v` —
    `Class IdempotentsSplit (C) := { split_of {x} (e : x ~> x) : Idempotent e → SplitIdempotent e }`;
    `Karoubi C` satisfies it; the extension
    `Karoubi_Extend : (C ⟶ D) → IdempotentsSplit D → (Karoubi C ⟶ D)` with
    `Karoubi_Extend_comm : Karoubi_Extend G _ ◯ Karoubi_Embed ≈ G` and uniqueness up
    to `≈` (Functor_Setoid); `Definition CauchyComplete := IdempotentsSplit` with the
    statement: if `IdempotentsSplit C` then `Karoubi_Embed` is an
    `EquivalenceOfCategories` (Phase 5's class, via FF+ESO).
12. `Instance/Sets/Karoubi.v` — `Sets_IdempotentsSplit` (split through the fixed-point
    sub-setoid `{ a | e a ≈ a }`); corollary `Karoubi_Embed : Sets ⟶ Karoubi Sets` is
    an `EquivalenceOfCategories` — the Cauchy-completeness statement for Sets and the
    phase's Phase-5 integration test.

**Completion checklist.**

| Deliverable | File |
|---|---|
| `MorphismClass`, `MonoClass`, `EpiClass`, ... | Theory/Morphisms/Classes.v |
| `Orthogonal`, `ortho_lift`, `⫫`, closure lemmas | Theory/Orthogonality.v |
| `IsCoequalizer`, conversions, `HasCoequalizers` | Structure/Coequalizer.v |
| `pullback_paste`, `monic_pullback_stable` | Theory/Morphisms/Stability.v |
| `Factorization`, `OFS`, `ofs_factor`, Fact.v comparison | Structure/Factorization.v |
| `StrongEpi`, `strong_epi_mono_is_iso` | Structure/Factorization/StrongEpi.v |
| `kernel_pair`, `RegularEpi`, `Regular` | Structure/Regular.v |
| `Regular_OFS` | Structure/Regular/Factorization.v |
| `Sets_Image` factorization | Instance/Sets/Image.v |
| `Karoubi`, `Karoubi_Embed` + Full/Faithful + splitting | Construction/Karoubi.v |
| `IdempotentsSplit`, `Karoubi_Extend`, `CauchyComplete` | Construction/Karoubi/Universal.v |
| `Sets_IdempotentsSplit`, Sets Cauchy corollary | Instance/Sets/Karoubi.v |

`Print Assumptions` closed for `Regular_OFS`, `Karoubi_Extend`, and the Sets Cauchy
corollary.

**Risks and fallbacks.** The pullback-stability argument in file 8 is the phase's
hard proof (~250 lines of Record-based pullback pasting). FALLBACK (named): land the
OFS + StrongEpi + image + "regular epi ⇒ strong epi" chain in full, keep
`regular_stable` as a class FIELD (it remains demanded of instances), and if the
derived pasting-chain lemmas for file 8's mono comparison overrun, deliver the
factorization theorem with the stability steps factored into named lemmas proved
against `WeakPullback` plus a conversion — reviewed before adoption, ledger-tracked
(entry 17). `Instance/Sets/Regular` is deliberately NOT promised here (Sets
coequalizers land with the quotient machinery in Phase 12; a Sets `Regular` instance
is a natural fast-follow noted in the ledger).

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
