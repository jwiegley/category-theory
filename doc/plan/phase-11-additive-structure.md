# Phase 11 work order — additive structure

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
2. **Branch.** `git checkout -b johnw/ct-phase11` off the tip of the branch
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

### Phase 11 — Additive structure

**Item 10 complete.** Branch `johnw/ct-phase11`. Depends on: Phase 8 (OFS packaging
for the abelian corollary; `IsCoequalizer` pattern for the equalizer sibling). Est.
10 files / ~3400 lines.

**Goal.** Zero objects and zero morphisms, biproducts, preadditive
(commutative-monoid-enriched at the setoid level), the semiadditivity theorems
(closing the discussion at `Structure/Bicartesian.v:18`), additive categories,
kernels/cokernels, abelian categories with epi-mono factorization, and the CMon
concrete semiadditive witness.

**Files.**

1. `Structure/ZeroObject.v` — setoid-honest (iso coincidence, not object equality):

   ```coq
   Class ZeroObject (C : Category) := {
     zero_terminal : @Terminal C;
     zero_initial  : @Initial C;           (* = @Terminal (C^op) — notation *)
     zero_coincide : @initial_obj C zero_initial ≅ @terminal_obj C zero_terminal
   }.
   Definition zero_mor `{ZeroObject C} {x y : C} : x ~> y :=
     zero ∘ from zero_coincide ∘ one.
   Lemma zero_mor_left  {x y z} (f : y ~> z) : f ∘ @zero_mor _ _ x y ≈ zero_mor.
   Lemma zero_mor_right ...
   ```

2. `Structure/Biproduct.v` — UMP-form record in `ZeroObject` context: object with
   `bi_inl`/`bi_inr`/`bi_exl`/`bi_exr`, the four identity/annihilation laws against
   `zero_mor`, and BOTH universal properties (`bi_is_product`, `bi_is_coproduct` via
   `∃!`); `Class HasBiproducts`.
3. `Structure/Preadditive.v` — CMon-enrichment at the setoid level, plus a dedicated
   notation scope (`f + g`, `0` in a morphism scope):

   ```coq
   Class Preadditive (C : Category) := {
     padd {x y} : (x ~> y) → (x ~> y) → (x ~> y);
     pzero {x y} : x ~> y;
     padd_respects {x y} : Proper (equiv ==> equiv ==> equiv) (@padd x y);
     padd_assoc ...; padd_comm ...; padd_zero_left ...;
     compose_padd_left  {x y z} (h : y ~> z) (f g : x ~> y) :
       h ∘ padd f g ≈ padd (h ∘ f) (h ∘ g);
     compose_padd_right ...; compose_pzero_left ...; compose_pzero_right ...
   }.
   ```

   Compatibility lemma: with a `ZeroObject`, `pzero ≈ zero_mor`.
4. `Structure/Semiadditive.v` — the two canonical theorems: (i) in a preadditive
   category with biproducts, `padd f g ≈ codiag ∘ (f ⊕ g) ∘ diag` and products are
   biproducts; (ii) from `Cartesian + Cocartesian + ZeroObject` plus the canonical
   product-coproduct comparison being iso, DERIVE `Preadditive` (the convolution
   addition) — this is the semiadditivity `Structure/Bicartesian.v:18` discusses;
   add a pointer comment there in the same commit.
5. `Structure/Additive.v` — `Class Additive`: Preadditive + `pneg` (group
   enrichment) + `HasBiproducts` (+ ZeroObject); consequence pack
   (`padd f (pneg f) ≈ pzero`, cancellation).
6. `Structure/Equalizer/Fork.v` — the equalizer-side elementary API (sibling of
   Phase 8's `Structure/Coequalizer.v`): `IsEqualizer f g q e`, conversions with
   `Equalizer (APair f g)`, `HasEqualizers`. Consumed by file 7 and Phase 14.
7. `Structure/Kernel.v` — `Kernel f := ` equalizer of `f` and `zero_mor` (via
   `APair f zero_mor` / `IsEqualizer` accessors); `Cokernel` by op with covariant
   accessors; `HasKernels`/`HasCokernels`; normal monos/epis (`is a kernel/cokernel
   of something`).
8. `Structure/Abelian.v` — `Class Abelian`: Additive + HasKernels + HasCokernels +
   every `Monic` is a kernel (of its cokernel) + every `Epic` is a cokernel (the
   real Theory/Morphisms.v classes). THEOREM: epi-mono factorization
   `f ≈ im ∘ coim` with `im := kernel (cokernel f)` monic, `coim` epic, and the
   comparison an iso; COROLLARY: this is an `OFS EpiClass MonoClass` instance
   (Phase 8 payoff, name `Abelian_OFS`).
9. `Instance/CMon.v` — commutative monoid objects in Sets as a concrete category:
   carrier setoid + `mappend`/`mempty` + laws up to `≈`; morphisms = monoid homs;
   homset pointwise. RIDE-OR-BUILD (decided: build standalone). The in-tree
   alternative is `Theory/Algebra/CommutativeMonoid.v` (commutative monoid
   OBJECTS in a symmetric monoidal category, instantiable at
   `Sets_Product_Monoidal`) with the hom-category pattern of
   `Theory/Algebra/Monoid/Hom.v` (the `Mon` category + forgetful functor,
   Section 2.5). It is deliberately NOT taken: file 10's biproduct/Preadditive
   proofs want direct carrier-level `mappend`/`mempty` without the
   monoidal-object indirection. Cite both files in the header, and pick
   non-clashing names (`CMon`, `CMonHom` — nothing named `Mon` or clashing with
   `Theory/Algebra/*`'s `Monoid`/`MonoidHom` vocabulary).
10. `Instance/CMon/Biproduct.v` — `ZeroObject CMon` (trivial monoid),
    `HasBiproducts CMon` (direct product is simultaneously product and coproduct),
    hence `Preadditive CMon` via file 4 — the semiadditive witness item 10 requests.
    (A genuine abelian instance needs groups; ledger entry 12.)

**Completion checklist.**

| Deliverable | File |
|---|---|
| `ZeroObject`, `zero_mor`, side lemmas | Structure/ZeroObject.v |
| `Biproduct`, `HasBiproducts` | Structure/Biproduct.v |
| `Preadditive`, notation scope | Structure/Preadditive.v |
| `biproduct_addition`, `bicartesian_preadditive`; Bicartesian.v:18 pointer | Structure/Semiadditive.v |
| `Additive` + consequences | Structure/Additive.v |
| `IsEqualizer`, `HasEqualizers` | Structure/Equalizer/Fork.v |
| `Kernel`, `Cokernel`, `normal_mono`, `normal_epi` | Structure/Kernel.v |
| `Abelian`, `abelian_epi_mono_factorization`, `Abelian_OFS` | Structure/Abelian.v |
| `CMon` category | Instance/CMon.v |
| `CMon_Biproducts`, `CMon_Preadditive` | Instance/CMon/Biproduct.v |

`Print Assumptions` closed for `abelian_epi_mono_factorization`, `Abelian_OFS`,
`CMon_Preadditive`.

**Risks and fallbacks.** The abelian factorization theorem is the quarantined proof
(kernel/cokernel exactness juggling). FALLBACK (named): first prove it under an
explicit image-existence hypothesis (a named record, still a theorem), with the full
derivation from the `Abelian` fields as the file's final lemma; if the final
derivation slips, the hypothesis-form lands and the derivation is tracked per
Section 6.4 (ledger entry 17). Doing this phase AFTER Phase 8 is deliberate:
`Orthogonal`-based uniqueness arguments replace repeated UMP unfolding in the
factorization chase.

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
