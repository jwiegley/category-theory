# Phase 16 work order — lawvere operads

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
2. **Branch.** `git checkout -b johnw/ct-phase16` off the tip of the branch
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

### Phase 16 — Lawvere theories; multicategories and operads

**Items 16 and 17 complete.** Branch `johnw/ct-phase16`. Depends on: Phase 5
(`EssentiallySurjective` unused here — no Phase 5 dependency in the committed core);
Phase 9 (CODE dependency in file 5: `EM_Comparison` and `crude_monadicity` are used
in actual statements, a Require-level dependency); Phase 11 (`Instance/CMon.v`,
consumed by file 12's Comm example); Phase 14 cited only (GAFT named in file 5's
header as the classical source of the left-adjoint hypothesis — no Require). Est.
12 files / ~3800 lines.

**Goal.** Finite-product theories on the skeletal-FinSet base mirroring the in-tree
PROP class shape; models in cartesian categories via the in-tree `CartesianFunctor`;
the model category; the finitary-monad connection at comparison level; the
PROP-spine bridge. Then symmetric multicategories with single-slot composition (the
design that avoids heterogeneous-list telescopes), representable multicategories,
operads, the endomorphism operad, and operad algebras.

**Files.**

1. `Theory/Lawvere.v` — the class, mirroring `Construction/PROP.v`'s relaxed shape
   (including its documented propositional-equality friction; FinSet's
   computes-by-`eq_refl` design discharges the equations on closed inputs):

   ```coq
   Class LawvereTheory : Type := {
     law_cat : Category;
     law_terminal : @Terminal law_cat;
     law_cartesian : @Cartesian law_cat;
     law_of_nat : nat → law_cat;
     law_zero_terminal : law_of_nat 0%nat = @terminal_obj _ law_terminal;
     law_plus_product : ∀ m n,
       (law_of_nat m × law_of_nat n)%object = law_of_nat (m + n)%nat
   }.
   Coercion law_cat : LawvereTheory >-> Category.
   ```

2. `Instance/FinSet/Lawvere.v` — the base theory: `law_cat := FinSet^op`. KEY FACT:
   `Cocartesian C` is literally notation for `@Cartesian (C^op)`
   (`Structure/Cocartesian.v:30`), so `FinSet_Cocartesian` IS the needed
   `@Cartesian (FinSet^op)`; terminal is FinSet's initial `0`. The `=` fields
   compute by `eq_refl` on closed nats (`fin_split`/`fin_join` design). This is the
   theory of equality (no operations) — the base every presented theory maps out
   of.
3. `Theory/Lawvere/Model.v` — models via the REAL in-tree class
   (`Functor/Structure/Cartesian.v:49`):

   ```coq
   Record Model (T : LawvereTheory) (C : Category)
          `{@Cartesian C} `{@Terminal C} := {
     model_fun : law_cat T ⟶ C;
     model_cartesian : @CartesianFunctor _ _ _ _ model_fun;
     model_terminal : (* preserves the terminal — the sibling class in
                         Functor/Structure/Terminal.v *)
   }.
   ```

   plus the model category `Models T C` as the full subcategory of `[law_cat T, C]`
   on the model predicate (via `Construction/Subcategory.v`; morphisms = all
   natural transformations; `Full` by construction).
4. `Theory/Lawvere/Sets.v` — `Models T Sets`; the underlying-set functor
   `ev1 : Models T Sets ⟶ Sets` (evaluate at `law_of_nat 1%nat`); `Faithful ev1`
   (products separate points).
5. `Theory/Lawvere/Monad.v` — the finitary-monad connection, hypothesis-scoped
   (honest reading in the header; full equivalence is ledger entry 2): given a left
   adjoint to `ev1` (data; GAFT — `Adjunction/GAFT.v` — is the classical source),
   the induced monad via the in-tree `Adjunction_Monad` and the comparison functor
   `Models T Sets ⟶ EilenbergMoore (...)` (Phase 9's `EM_Comparison`); corollary:
   monadicity of `ev1` under `crude_monadicity`'s hypotheses when supplied.
6. `Theory/Lawvere/PROP.v` — the PROP-spine bridge: every Lawvere theory carries a
   symmetric monoidal structure (cartesian monoidal); a signature interpretation
   into `law_cat` induces `FreePROP Σ ⟶ law_cat` via `Construction/PROP/Interp.v`'s
   universal property; pointer note connecting cartesian-vs-copy/discard to Fox's
   theorem (`Structure/Monoidal/Markov/Fox.v`) — no new proof, discharge
   `Instance/FinSet.v`'s header remark at the theory level.
7. `Theory/Multicategory.v` — symmetric multicategories, zipper-position
   single-slot composition (BINDING DESIGN: `∘ᵢ` avoids the heterogeneous-list
   telescopes that are this library's historical blowup zone; simultaneous
   composition is derived as a fold, lemma-level):

   ```coq
   Class Multicategory := {
     mobj : Type;
     mhom : list mobj → mobj → Type;
     mhomset (Γ : list mobj) (c : mobj) : Setoid (mhom Γ c);
     mid (a : mobj) : mhom [a] a;
     mcomp {Γ₁ Γ₂ Δ b c} :
       mhom (Γ₁ ++ b :: Γ₂) c → mhom Δ b → mhom (Γ₁ ++ Δ ++ Γ₂) c;
     mcomp_respects : ... Proper ... ;
     mcomp_id_left / mcomp_id_right : ... ;   (* unit laws, app-normalized *)
     mcomp_assoc_nested / mcomp_assoc_disjoint : ... ;
     msym {Γ Δ c} (p : Permutation Γ Δ) : mhom Γ c → mhom Δ c;
     msym_respects / msym_id / msym_compose : ... ;
     mcomp_equivariant : ...
   }.
   ```

   (`Permutation` is stdlib `List.Permutation` — version-portable and already used
   by the PROP stack. List-splice equalities are stated through `++`-associativity
   lemmas present in all supported versions, with local shims otherwise —
   Section 2.3.)
8. `Theory/Multicategory/Functor.v` — multifunctors (colour map + multimap map
   preserving `mid`/`mcomp`/`msym`), their setoid, identity/composition.
9. `Theory/Multicategory/Representable.v` — every symmetric monoidal category
   yields a multicategory: `mobj := C`, `mhom Γ c := tensor_list Γ ~> c` where
   `tensor_list` is the right fold of `⨂` over `I` (the `cprop_tensor_app`
   pattern); `mcomp` by tensor-splice; `msym` from the braiding. Instantiated for
   any `ColouredPROP` (the donor connection item 17 names).
10. `Theory/Multicategory/Endomorphism.v` — the endomorphism operad in a cartesian
    category: `pow X n` (right-nested product fold), `EndOperad X` with
    `mhom n := pow X n ~> X`, composition by `fork`-pasting, symmetry via product
    braiding.
11. `Theory/Multicategory/Operad.v` — operads as one-object multicategories:
    wrapper `Operad := Multicategory with mobj := poly_unit`, arity accessors
    `ohom n := mhom (repeat ttt n) ttt`, and the round-trip lemma between the
    one-object presentation and nat-indexed data with symmetric-group actions (at
    accessor level).
12. `Theory/Multicategory/Algebra.v` — algebras: `OperadAlgebra (O : Operad) {C}
    `{@Cartesian C} (X : C) := MultiFunctor O (EndOperad X)`; the category of
    O-algebras (first-projection homset idiom); the endomorphism-operad universal
    property as a definitional unfolding lemma; example: algebras of the terminal
    operad in Sets are commutative monoids (connect `Instance/CMon.v`, Phase 11).

**Completion checklist.**

| Deliverable | File |
|---|---|
| `LawvereTheory` | Theory/Lawvere.v |
| `FinSetOp_Lawvere` (computes by `eq_refl`) | Instance/FinSet/Lawvere.v |
| `Model`, `Models` | Theory/Lawvere/Model.v |
| `ev1`, `ev1_Faithful` | Theory/Lawvere/Sets.v |
| induced monad + comparison + scoped monadicity corollary | Theory/Lawvere/Monad.v |
| `Lawvere_PROP_interp`, Fox pointer | Theory/Lawvere/PROP.v |
| `Multicategory`, `mcomp`, `msym` + laws | Theory/Multicategory.v |
| `MultiFunctor` + setoid | Theory/Multicategory/Functor.v |
| `RepresentableMulticategory`, `tensor_list`, ColouredPROP instance | Theory/Multicategory/Representable.v |
| `pow`, `EndOperad` | Theory/Multicategory/Endomorphism.v |
| `Operad`, `ohom`, presentation round trip | Theory/Multicategory/Operad.v |
| `OperadAlgebra`, O-algebra category, Comm example | Theory/Multicategory/Algebra.v |

`Print Assumptions` closed for `FinSetOp_Lawvere`, `RepresentableMulticategory`,
`EndOperad`, `OperadAlgebra`.

**Risks and fallbacks.** (a) `mcomp` associativity splice arithmetic is the grind —
reuse the coloured-PROP list lemma stack wholesale; if index juggling balloons,
the zipper representation above IS the fallback already (do not switch to
position-as-nat). (b) If `msym` equivariance drags, FALLBACK (named): land the
planar (non-symmetric) core class first with `Symmetric` as a mixin class, keeping
item 17's "symmetric multicategories" as the mixin composite and unblocking
files 9-12 against the planar core; escalate the equivariance law per Section 6.4.
(c) Free operad: ledger entry 3 (the item itself marks it stretch).

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
