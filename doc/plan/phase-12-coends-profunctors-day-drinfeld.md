# Phase 12 work order — coends profunctors day drinfeld

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
2. **Branch.** `git checkout -b johnw/ct-phase12` off the tip of the branch
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

### Phase 12 — Coend calculus, profunctors, Day convolution; Drinfeld centre; star-autonomous

**Item 5 complete; both cross-cutting notions delivered.** Branch `johnw/ct-phase12`.
Depends on: in-tree only (Phase 5's `≃` used incidentally). Est. 12 files / ~4000
lines (envelope ceiling — staging is mandatory).

**Goal.** Covariant coend accessors; ends AND coends computed in Sets (the coend as
a funext-free setoid quotient in the `Instance/Sets/Pushout.v` style); Yoneda
reduction and Fubini for Sets-valued functors; profunctors as `C^op ∏ D ⟶ Sets`
with composition by coends; the bicategory-lite laws (unit + associativity up to
natural iso); representable profunctors vs adjunctions; Day convolution on
`[C, Sets]`; the Drinfeld centre (explicitly distinguished from the premonoidal
centre); star-autonomous categories at definition level.

**Files.**

1. `Structure/Coend.v` — covariant accessor layer over the in-tree
   `Coend F := @End (C^op) (D^op) (F^op)` (`Structure/End.v:58`), Pushout.v-pattern:
   `coend_obj`, `coend_inj {x} : F (x,x) ~> coend_obj`, the cowedge condition
   restated covariantly, `coend_ump`, and a `Build_Coend`-style smart constructor
   from cowedge data. No breaking change to End.v.
2. `Instance/Sets/End.v` — ends in Sets computed directly: carrier

   ```coq
   { s : ∀ x : C, F (x, x)
   & ∀ (x y : C) (f : x ~> y),
       fmap[F] (id[x], f) (s x) ≈ fmap[F] (op f, id[y]) (s y) }
   ```

   with pointwise setoid; `Sets_End : ∀ F, End F`. (Morphisms of `C^op ∏ C` are
   pairs whose first component is an op-morphism — follow `Theory/Dinatural.v`'s
   pairing conventions.)
3. `Instance/Sets/Coend.v` — coends in Sets by inductive equivalence closure
   (funext-free; the `pushout_eq` template):

   ```coq
   Inductive coend_sum (F : C^op ∏ C ⟶ Sets) : Type :=
     ci : ∀ (x : C), F (x, x) → coend_sum F.
   Inductive coend_eq (F) : coend_sum F → coend_sum F → Type :=
     | ce_refl ... | ce_sym ... | ce_trans ...
     | ce_point x (a b : F (x,x)) : a ≈ b → coend_eq (ci x a) (ci x b)
     | ce_glue {x y} (f : x ~> y) (a : F (y, x)) :
         coend_eq (ci x (fmap[F] (op f, id) a)) (ci y (fmap[F] (id, f) a)).
   Definition SetsCoend (F) : SetoidObject := {| carrier := coend_sum F |}.
   ```

   plus `coend_inj`, the cowedge law (one `ce_glue`), and the FULL UMP: the mediator
   out of the quotient by `coend_eq`-induction (the descent `Proper` is the one
   nontrivial obligation — rule 2.4.14 applies to the constructors). Header
   documents the smallness constraint (the indexing category's levels sit below
   Sets' carrier level). Yields `Coend`-instances for all `F : D^op ∏ D ⟶ Sets`.
4. `Theory/Coend/Yoneda.v` — ninja-Yoneda reduction in Sets, both variances:
   `SetsCoend (λ (x,y), C(x, c) × F y) ≊ F c` (mediate by `fmap[F]`; inverse
   `(c; (id, −))`; round trips are one `ce_glue` each) and the End form (hom into
   F) against file 2.
5. `Theory/Coend/Fubini.v` — Fubini for Sets coends over a product shape:
   `SetsCoend over (C ∏ D) ≊ iterated SetsCoend` by explicit quotient comparison
   both ways. (Abstract-target Fubini is descoped — ledger entry 6.)
6. `Theory/Profunctor.v` — `Definition Profunctor (C D : Category) :=
   C^op ∏ D ⟶ Sets`, notation `C ⇸ D`; identity profunctor `Hom C`
   (`Functor/Hom.v`); representables `Repr_left (F : C ⟶ D) : C ⇸ D` and
   `Repr_right (U : D ⟶ C)` via the hom bifunctor composites (the
   `Adjunction/Hom.v` shapes); `Prof_Setoid` inherited from `[C^op ∏ D, Sets]`.
7. `Construction/Profunctor/Compose.v` — composition by coends:
   `prof_compose (P : C ⇸ D) (Q : D ⇸ E) : C ⇸ E` at `(c, e)` is
   `SetsCoend (λ d, P (c, d) × Q (d, e))`; bifunctoriality in `(c, e)` via the
   coend UMP; `prof_id := Hom C`.
8. `Construction/Profunctor/Laws.v` — the bicategory-lite: unitor isos
   `prof_compose (Hom C) P ≅ P` / `prof_compose P (Hom D) ≅ P` (pointwise, by file
   4) and the associator (pointwise Fubini-style rebracketing by `coend_eq`
   induction both ways), packaged as isos in `[C^op ∏ D, Sets]` (2-cells come free
   from `Instance/Fun.v`). A `Bicategory`-class instance is NOT built here (the
   class completes in Phase 13; ledger entry 14 tracks the stretch instance).
9. `Theory/Profunctor/Adjunction.v` — representables vs adjunctions:
   `F ⊣ U ↔ Repr_left F ≅[Fun] Repr_right U` — a repackaging of
   `Adjunction/Hom.v`'s `hom_adj` through file 6's vocabulary, with the two
   conversions.
10. `Construction/Day.v` — Day convolution on `[C, Sets]` for monoidal C:
    `Day F G : C ⟶ Sets` at `c` is
    `SetsCoend over C ∏ C of (λ (a,b), C(a ⨂ b, c) × F a × G b)`; bifunctor
    `Day_Tensor : [C,Sets] ∏ [C,Sets] ⟶ [C,Sets]`; unit `Hom C (I, −)`
    (i.e. `[Hom I,─]`); unitor and associator isos via files 4-5, with naturality.
    STAGING (binding): pentagon/triangle and the bundled
    `Day_Monoidal : @Monoidal [C, Sets]` are the file's LAST lemmas; the named
    fallback ships Day at iso level and moves only the `Monoidal` bundling to the
    ledger (entry 5) — the isos themselves are committed.
11. `Structure/Monoidal/Drinfeld.v` — the Drinfeld centre. Header MUST distinguish
    it from the premonoidal centre (`Structure/Premonoidal/Centre.v` /
    `Structure/Binoidal/Central.v`) by name and cross-reference:

    ```coq
    Record HalfBraiding {C : Category} `{M : @Monoidal C} (z : C) := {
      half_braid (x : C) : z ⨂ x ≅ x ⨂ z;
      half_braid_natural {x y} (f : x ~> y) :
        to (half_braid y) ∘ bimap id f ≈ bimap f id ∘ to (half_braid x);
      half_braid_tensor {x y} :   (* hexagon against tensor_assoc *)
        to (half_braid (x ⨂ y))
          ≈ (associator conjugates of half_braid x and half_braid y)
    }.
    Program Definition Drinfeld (C : Category) `{@Monoidal C} : Category := {|
      obj := ∃ z : C, HalfBraiding z;
      hom := fun a b => { f : `1 a ~> `1 b &
        ∀ x, to (half_braid (`2 b) x) ∘ bimap f id ≈ bimap id f ∘ to (half_braid (`2 a) x) };
      homset := fun a b => {| equiv := fun f g => `1 f ≈ `1 g |} |}.
    Program Definition Drinfeld_Monoidal : @Monoidal (Drinfeld C).
    Program Definition Drinfeld_Braided : @BraidedMonoidal (Drinfeld C).
      (* braid at ((a,σ),(b,τ)) := σ b; hexagons from half_braid_tensor *)
    Program Definition Drinfeld_Forget : Drinfeld C ⟶ C.
    ```

    FALLBACK (named): if the braided hexagons overrun, `Drinfeld_Monoidal` +
    `Drinfeld_Forget` land and `Drinfeld_Braided` follows Section 6.4 (ledger 7).
12. `Structure/Monoidal/StarAutonomous.v` — definition level, over symmetric
    monoidal closed: the base class is `ClosedMonoidal` from
    `Structure/Monoidal/Closed.v` (which owns the `⇒` internal-hom infix) plus
    the `Structure/Monoidal/...` symmetric stack — NOT `Structure/Closed.v`,
    which is a stub (Section 2.5): dualizing object `dualizer : C`,
    `dual x := x ⇒ dualizer`,
    `Class StarAutonomous := { star_double_dual {x} : x ≅ dual (dual x);
    star_natural ...; star_transpose {x y} : (x ⨂ y ~> dualizer) ≊ (x ~> dual y) }`;
    basic lemmas (`dual` is a contravariant functor). Edges (⅋, linear
    distributivity, coherence beyond the above) are ledgered (entry 4).

**Completion checklist.**

| Deliverable | File |
|---|---|
| covariant `coend_obj`/`coend_inj`/`coend_ump` | Structure/Coend.v |
| `Sets_End` | Instance/Sets/End.v |
| `coend_sum`, `coend_eq`, `SetsCoend`, full UMP | Instance/Sets/Coend.v |
| `yoneda_reduction` (both variances) | Theory/Coend/Yoneda.v |
| `coend_fubini` | Theory/Coend/Fubini.v |
| `Profunctor`, `⇸`, `Repr_left/right` | Theory/Profunctor.v |
| `prof_compose`, `prof_id` | Construction/Profunctor/Compose.v |
| `prof_unit_left_iso`, `prof_unit_right_iso`, `prof_assoc_iso` | Construction/Profunctor/Laws.v |
| `representable_adjunction` (iff) | Theory/Profunctor/Adjunction.v |
| `Day`, `Day_Tensor`, unit/unitor/associator isos (+ `Day_Monoidal` or ledger 5) | Construction/Day.v |
| `HalfBraiding`, `Drinfeld`, `Drinfeld_Monoidal`, `Drinfeld_Braided`, `Drinfeld_Forget` | Structure/Monoidal/Drinfeld.v |
| `StarAutonomous`, `dual` functor, transpose iso | Structure/Monoidal/StarAutonomous.v |

`Print Assumptions` closed for `SetsCoend`'s UMP, `prof_assoc_iso`,
`yoneda_reduction`, `Day`'s associator, `Drinfeld_Monoidal`.

**Risks and fallbacks.** (a) Day pentagon — staged, fallback named in file 10.
(b) `coend_eq` induction bookkeeping in the associator — budget ~500 lines; build a
`srewrite`-friendly congruence-lemma pack for `coend_eq` first (the
`Construction/Quotient.v` precedent). (c) The universe side is benign: composition
and triple composites only accumulate `o_shape ≤ carrier(Sets)` constraints.

**Universe note (item 5).** All coends stay Sets-valued. The bicategory-lite is
delivered as LEMMAS in per-pair functor categories `[C^op ∏ D, Sets]` — never form
a single "category of all profunctors between all categories" object; that is the
universe bump this design dodges.

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
