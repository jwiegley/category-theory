# Phase 7 work order — falgebras lambek adamek

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
2. **Branch.** `git checkout -b johnw/ct-phase7` off the tip of the branch
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

### Phase 7 — F-(co)algebras, Lambek, Adamek, recursion schemes

**Item 3 complete.** Branch `johnw/ct-phase7`. Depends on: Phase 5 (file 5,
`PreservesColimit`). Est. 10 files / ~3400 lines.

**Goal.** Categories `FAlg F` / `FCoalg F`, initial-algebra and final-coalgebra
theory, Lambek's lemma both ways, Adamek's theorem as an explicit-hypothesis theorem
over the omega-chain (with a `Complete`-driven corollary), catamorphism/anamorphism
universal properties, lists on `Coq` and streams on `Sets`.

**Files.**

1. `Instance/Omega.v` — the thin chain category, engineered for universe unification
   (rule 2.4.11) and version portability (no stdlib `le` anywhere):

   ```coq
   Inductive le_t@{u} (n : nat) : nat → Type@{u} :=  (* Type-valued: Prop le cannot
     | le_t_n : le_t n                                  eliminate into hom Types *)
     | le_t_S {m} : le_t m → le_t (S m).              (* uniform-parameter style *)
   (* close the section/inductive block, then: *)
   Definition le_t_trans@{u} {m n k} : le_t@{u} m n → le_t@{u} n k → le_t@{u} m k.
   Program Definition Omega@{o h p} : Category@{o h p} := {|
     obj := nat; hom := le_t@{h}; homset := Morphism_equality@{o h p};
     id := fun n => le_t_n@{h} n; compose := fun x y z f g => le_t_trans@{h} g f |}.
   ```

   (`Morphism_equality` makes all law obligations proof-irrelevant; prove the two
   `le_t_trans` unit/associativity equations as `=` lemmas by induction. The
   `@{u}`/`@{h}`/`@{o h p}` instantiations are load-bearing: under the library's
   global `Set Universe Polymorphism` (Lib.v:11), a strictly bound
   `Omega@{o h p}` cannot mention a polymorphic constant without instantiating it
   (unbound-universe errors otherwise) — the `Instance/One.v` precedent, which
   writes `Morphism_equality@{o h p}` and `poly_unit@{o}` for exactly this reason.
   This version, including the three law obligations by induction, is verified to
   compile end-to-end.)
2. `Construction/FAlg.v` — the category of F-algebras, reusing `FAlgebra` from
   `Theory/Functor.v` and the first-projection-homset idiom:

   ```coq
   Program Definition FAlg `(F : C ⟶ C) : Category := {|
     obj := ∃ a : C, FAlgebra F a;
     hom := fun x y => { h : `1 x ~> `1 y & h ∘ `2 x ≈ `2 y ∘ fmap[F] h };
     homset := fun x y => {| equiv := fun f g => `1 f ≈ `1 g |};
     id := fun x => (id; _); compose := fun _ _ _ f g => (`1 f ∘ `1 g; _) |}.
   Program Definition FAlg_Forget `(F : C ⟶ C) : FAlg F ⟶ C.
   ```

3. `Construction/FCoalg.v` — `FCoalg F := (FAlg (F^op))^op` (definitional), the
   hom-unfolding reflexivity lemma, covariant accessors (`FCoalgebra` carriers,
   structure maps, hom condition), `FCoalg_Forget`.
4. `Theory/Lambek.v` —

   ```coq
   Theorem lambek `(F : C ⟶ C) (I : @Initial (FAlg F)) :
     F (`1 (@initial_obj _ I)) ≅ `1 (@initial_obj _ I).
   ```

   (Structure map vs. the mediator into the algebra `(F μF, fmap[F] α)`; the two
   composites are identities by initial-mediator uniqueness.) `lambek_final` for
   final coalgebras free by duality through FCoalg. SHARP EDGE: `Initial` is
   notation for `Terminal` of the op — instances are built with
   `terminal_obj`/`one` fields; the accessors are `initial_obj`/`zero`.
5. `Theory/Recursion.v` — `cata` (the unbundled mediator `zero` of
   `@Initial (FAlg F)`), `cata_commutes`, `cata_unique`, `cata_fusion`; dually
   `ana`, `ana_unique`, `ana_fusion` (op one-liners + accessor restatements).
6. `Construction/Chain.v` — the omega-chain:

   ```coq
   Section Chain.
   Context {C : Category} `{@Initial C} (F : C ⟶ C).
   Fixpoint chain_obj (n : nat) : C :=
     match n with O => @initial_obj C _ | S k => F (chain_obj k) end.
   Fixpoint chain_step (n : nat) : chain_obj n ~> chain_obj (S n) :=
     match n with O => zero | S k => fmap[F] (chain_step k) end.
   Definition chain_hom {m n} (p : le_t m n) : chain_obj m ~> chain_obj n. (* by recursion on p *)
   Program Definition Chain : Omega ⟶ C := {| fobj := chain_obj; fmap := @chain_hom |}.
   End Chain.   (* MUST close before any Colimit (Chain F) statement — rule 2.4.11 *)
   ```

   plus `Cochain` by duality.
7. `Theory/Adamek.v` —

   ```coq
   Theorem adamek {C : Category} `{@Initial C} (F : C ⟶ C)
     (L : Colimit (Chain F))
     (pres : PreservesColimit (Chain F) F) :
     @Initial (FAlg F).
   ```

   Proof plan: `pres` exhibits `F L` as colimit of `F ◯ Chain F`; the successor-
   shifted cocone of `Chain F` over the same vertex `L` gives a comparison both ways
   (Lambek-style structure iso); initiality: legs `chain_obj n ~> a` into any algebra
   `(a, α)` by nat-recursion, cocone property by `le_t`-induction, mediate, uniqueness
   by colimit uniqueness. FALLBACK (named): if the shift-reindexing plumbing exceeds
   budget, introduce `Record AdamekData` packaging the comparison data
   (`IsALimit ((F ◯ Chain F)^op) (F L)` together with the canonical cocone-agreement
   equations) and prove `adamek` from `AdamekData`; the discharge
   `PreservesColimit → AdamekData` then lands in file 10 or as a fast-follow on this
   branch (ledger entry 17). The theorem statement itself is never weakened silently.
8. `Instance/Coq/Lists.v` — `ListF a := fun X => option (a * X)` as a `Coq`
   endofunctor (defined directly; no dependence on sum-type instances); `list a` is
   the initial `ListF a`-algebra: `cata` is the evident fixpoint, uniqueness by list
   induction under pointwise `=`. Assumptions closed (no funext).
9. `Instance/Sets/Streams.v` — `StreamF (A : SetoidObject) := (A × −)` on `Sets`
   via `Sets_Cartesian`; carrier `Stream A` (CoInductive) with **bisimilarity** as
   the setoid equivalence; final coalgebra: `ana` by cofix, uniqueness by coinduction
   up to bisimilarity. Streams live in `Sets`, not `Coq`: uniqueness up to pointwise
   `=` of coinductives is not provable without axioms, and the setoid carrier is the
   honest home.
10. `Theory/Adamek/Corollaries.v` — routine: the `Cocomplete`-driven corollary
    (`Cocomplete C → @Initial C → PreservesColimit (Chain F) F → @Initial (FAlg F)`),
    the `NatF := option` note over `Coq` (initial algebra = `nat`), and — if file 7
    took the fallback — the `AdamekData` discharge.

**Completion checklist.**

| Deliverable | File |
|---|---|
| `le_t`, `Omega` (explicit `@{o h p}`) | Instance/Omega.v |
| `FAlg`, `FAlg_Forget` | Construction/FAlg.v |
| `FCoalg`, `FCoalg_Forget` | Construction/FCoalg.v |
| `lambek`, `lambek_final` | Theory/Lambek.v |
| `cata`, `cata_unique`, `cata_fusion`, `ana`, `ana_unique` | Theory/Recursion.v |
| `chain_obj`, `Chain`, `Cochain` | Construction/Chain.v |
| `adamek` (and `AdamekData` only if the fallback fired) | Theory/Adamek.v |
| `ListF`, list initial-algebra witness | Instance/Coq/Lists.v |
| `StreamF`, stream final-coalgebra witness (bisimilarity setoid) | Instance/Sets/Streams.v |
| `Cocomplete` corollary | Theory/Adamek/Corollaries.v |

`Print Assumptions` closed for `lambek`, `adamek`, the list and stream witnesses.

**Risks and fallbacks.** (a) Adamek shift-comparison plumbing — the `AdamekData`
fallback above; destination named; nothing dropped. (b) Coinductive guardedness in
file 9 — keep bisimilarity a plain coinductive relation and prove `Equivalence` by
cofix (well-trodden). (c) Portability: `le_t` avoids stdlib `le` lemmas entirely by
design; do not reintroduce them.

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
