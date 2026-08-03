# Phase 10 work order — displayed fibrations grothendieck

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
2. **Branch.** `git checkout -b johnw/ct-phase10` off the tip of the branch
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

### Phase 10 — Displayed categories, fibrations, indexed categories, Grothendieck

**Item 4 complete.** Branch `johnw/ct-phase10`. Depends on: Phase 5 (equivalences for
the round trip), Phase 8 (pullback toolkit for the codomain example). Est. 10 files
/ ~3800 lines. Highest design-risk phase; read the honesty note first.

**HONESTY NOTE (binding design decision).** In this library a bare `Functor B Cat`
does NOT suffice for the Grothendieck construction: Cat's hom-equivalence is
`Functor_Setoid`, so `fmap_comp`/`fmap_id`/`fmap_respects` are *chosen natural isos
carrying no coherence between different applications* — an adversarial instance can
twist `fmap_comp` by a nontrivial central automorphism in a fibre, and the total
category's associativity becomes unprovable. `StrictCat`-valued functors shift the
problem to coherence of propositional object-equality proofs (no UIP in general).
The honest "pseudofunctor-lite" is therefore an explicit coherent-data record,
`IndexedCat`, with the cocycle and unit coherence as fields; constructors are
provided (a) from split cleavages (coherence trivial) and (b) from
`F : B ⟶ StrictCat` under fibrewise UIP (dischargeable via Hedberg from decidable
object equality, e.g. FinSet-like fibres). Displayed categories remain the primitive
Coq-friendly presentation, exactly as item 4 prescribes.

**Files.**

1. `Theory/Displayed.v` — the primitive. Displayed homs are indexed by base
   morphisms; heterogeneity across `≈` is mediated by a transport operation whose
   proof-irrelevance is an axiom of the structure (this is what makes downstream
   law-orientation harmless):

   ```coq
   Class Displayed (C : Category) := {
     dobj : C → Type;
     dhom {x y} : dobj x → dobj y → (x ~> y) → Type;
     dhomset {x y} (dx : dobj x) (dy : dobj y) (f : x ~> y) : Setoid (dhom dx dy f);
     dtransport {x y} {dx dy} {f g : x ~> y} (e : f ≈ g) :
       dhom dx dy f → dhom dx dy g;
     dtransport_respects {x y dx dy} {f g : x ~> y} (e : f ≈ g) :
       Proper (equiv ==> equiv) (@dtransport x y dx dy f g e);
     dtransport_id {x y} {dx : dobj x} {dy : dobj y} {f : x ~> y}
       (e : f ≈ f) (ff : dhom dx dy f) :
       dtransport e ff ≈ ff;                                (* proof irrelevance *)
     dtransport_trans {x y} {dx : dobj x} {dy : dobj y} {f g h : x ~> y}
       (e1 : f ≈ g) (e2 : g ≈ h) (ff : dhom dx dy f) :
       dtransport e2 (dtransport e1 ff)
         ≈ dtransport (Equivalence_Transitive _ _ _ e1 e2) ff;
     did {x} (dx : dobj x) : dhom dx dx id;
     dcomp {x y z} {dx dy dz} {f : y ~> z} {g : x ~> y} :
       dhom dy dz f → dhom dx dy g → dhom dx dz (f ∘ g);
     dcomp_respects : ... Proper ... ;
     did_left  {x y} {dx : dobj x} {dy : dobj y} {f : x ~> y}
       (ff : dhom dx dy f) :
       dcomp (did dy) ff ≈ dtransport (symmetry (id_left f)) ff;
     did_right : ... ;
     dcomp_assoc {w x y z}
       {dw : dobj w} {dx : dobj x} {dy : dobj y} {dz : dobj z}
       {f : y ~> z} {g : x ~> y} {h : w ~> x}
       (ff : dhom dy dz f) (gg : dhom dx dy g) (hh : dhom dw dx h) :
       dcomp ff (dcomp gg hh)
         ≈ dtransport (symmetry (comp_assoc f g h)) (dcomp (dcomp ff gg) hh)
   }.
   #[export] Existing Instance dhomset.   (* mirrors homset's registration *)
   ```

   Three shapes above are load-bearing (each verified by failing/passing
   spot-compiles): (a) the displayed-object binders must be ANNOTATED
   (`{dx : dobj x} {dy : dobj y}`, and `{dw ...}`-`{dz ...}` in `dcomp_assoc`) —
   flat unannotated groups like `{x y dx dy}` break elaboration with "Cannot infer
   the type of dx"; (b) `dtransport_trans`'s transported morphism must be annotated
   (`(ff : dhom dx dy f)`), else `dtransport`'s implicit `dx` is uninferable;
   (c) `#[export] Existing Instance dhomset.` immediately after the class is
   required so file 2's Total homset — whose `equiv` compares second projections
   through `dtransport` — can resolve the displayed setoid by typeclass search. With these, the full class
   — including the `Equivalence_Transitive _ _ _ e1 e2` and
   `dtransport (symmetry (id_left f))` forms — compiles as skeletoned.
   Also the derived transport lemma pack (`dtransport_flip`, groupoid laws) —
   budgeted here, since Total's associativity spends its time in it.
2. `Construction/Displayed/Total.v` — the total category and projection:

   ```coq
   Program Definition Total {C} (D : Displayed C) : Category := {|
     obj := ∃ x : C, dobj x;
     hom := fun x y => ∃ f : `1 x ~> `1 y, dhom (`2 x) (`2 y) f;
     homset := fun x y => {| equiv := fun f g =>
       { e : `1 f ≈ `1 g & dtransport e (`2 f) ≈ `2 g } |}
   |}.
   Program Definition Total_Proj {C} (D : Displayed C) : Total D ⟶ C.
   ```

   (Homset symmetry/transitivity from `dtransport_trans` + `dtransport_id`. Use
   `#[local] Obligation Tactic := program_simpl` — rule 2.4.7.)
3. `Theory/Fibration.v` — both presentations plus the bridge. Displayed level:

   ```coq
   Class DCartesian {C} {D : Displayed C} {x y} {f : x ~> y} {dx dy}
         (ff : dhom dx dy f) := {
     dcart_factor {z} {g : z ~> x} {dz} (hh : dhom dz dy (f ∘ g)) :
       ∃! gg : dhom dz dx g, dcomp ff gg ≈ hh
   }.
   Class Cleaving {C} (D : Displayed C) := {
     clift {x y} (f : x ~> y) (dy : dobj y) :
       { dx : dobj x & { ff : dhom dx dy f & DCartesian ff } } }.
   ```

   Functor level: `CartesianMorphism (P : E ⟶ C) (φ : e ~> e')` (the ≈-honest UMP
   with `fmap[P]`-fibred factorization), `ClovenFibration` (chosen lifts with strict
   fibre anchoring `P e' = x` — plain `=` on objects is legitimate here, transported
   via `iso_of_eq` where consumed), `SplitCleaving` (cleavage functorial on the
   nose). Bridges: a `Cleaving` on `D` makes `Total_Proj D` a cloven fibration;
   opfibrations by op (`Displayed_op` with `dhom_op dx dy f := dhom dy dx (op f)`).
4. `Construction/Indexed.v` — the coherent pseudofunctor-lite (see honesty note):

   ```coq
   Record IndexedCat (B : Category) := {
     idx_fib : B → Category;
     idx_map {x y : B} (f : x ~> y) : idx_fib x ⟶ idx_fib y;
     idx_resp {x y} {f g : x ~> y} (e : f ≈ g) (a : idx_fib x) :
       idx_map f a ≅[idx_fib y] idx_map g a;
     idx_resp_natural {x y f g} (e : f ≈ g) {a b} (k : a ~> b) :
       fmap[idx_map g] k ∘ to (idx_resp e a) ≈ to (idx_resp e b) ∘ fmap[idx_map f] k;
     idx_resp_id {x y} {f : x ~> y} (e : f ≈ f) a : to (idx_resp e a) ≈ id;
     idx_resp_trans {x y} {f g h : x ~> y} (e1 : f ≈ g) (e2 : g ≈ h) a :
       to (idx_resp e2 a) ∘ to (idx_resp e1 a)
         ≈ to (idx_resp (Equivalence_Transitive _ _ _ e1 e2) a);
     idx_id {x} (a : idx_fib x) : idx_map (@id B x) a ≅ a;
     idx_id_natural : ... ;
     idx_comp {x y z} (f : y ~> z) (g : x ~> y) (a : idx_fib x) :
       idx_map f (idx_map g a) ≅ idx_map (f ∘ g) a;
     idx_comp_natural : ... ;
     idx_unit_left {x y} (f : x ~> y) a :
       to (idx_resp (id_left f) a) ∘ to (idx_comp id f a)
         ≈ to (idx_id (idx_map f a));
     idx_unit_right {x y} (f : x ~> y) a :
       to (idx_resp (id_right f) a) ∘ to (idx_comp f id a)
         ≈ fmap[idx_map f] (to (idx_id a));
     idx_cocycle {w x y z} (f : y ~> z) (g : x ~> y) (h : w ~> x) a :
       to (idx_comp (f ∘ g) h a) ∘ to (idx_comp f g (idx_map h a))
         ≈ to (idx_resp (comp_assoc f g h) a)
             ∘ to (idx_comp f (g ∘ h) a) ∘ fmap[idx_map f] (to (idx_comp g h a))
   }.
   ```

   Header carries the honesty note verbatim (why a bare `B ⟶ Cat` does not
   suffice), with the twist-counterexample shape sketched in a comment.
5. `Construction/Grothendieck.v` — the Grothendieck construction as a Displayed
   instance plus its total category:

   ```coq
   Program Definition Grothendieck_Displayed {B} (A : IndexedCat B) : Displayed B := {|
     dobj := fun x => idx_fib A x;
     dhom := fun x y dx dy f => idx_map A f dx ~{idx_fib A y}~> dy;
     dtransport := fun _ _ _ _ f g e ff => ff ∘ from (idx_resp A e _);
     did := fun x dx => to (idx_id A dx);
     dcomp := fun x y z dx dy dz f g ff gg =>
       ff ∘ fmap[idx_map A f] gg ∘ from (idx_comp A f g dx)
   |}.
   Definition Grothendieck {B} (A : IndexedCat B) : Category :=
     Total (Grothendieck_Displayed A).
   Definition Grothendieck_Proj {B} (A : IndexedCat B) : Grothendieck A ⟶ B :=
     Total_Proj _.
   ```

   The `Displayed` laws are discharged FROM the coherence fields; this file is the
   payoff of file 4's design.
6. `Construction/Grothendieck/Fibration.v` — the projection is a split
   opfibration: cocartesian lifts `(f, id-on idx_map f dx)`; splitting from
   `idx_id`/`idx_comp` being chosen isos.
7. `Construction/Grothendieck/Fiber.v` — fibre categories of a displayed category
   (`Fiber D x`: objects `dobj x`, homs `dhom dx dy id`, composition via
   `dtransport (id_left id)`), and the committed round-trip half:
   `Fiber (Grothendieck_Displayed A) x` is `EquivalenceOfCategories`-equivalent to
   `idx_fib A x` (near-isomorphic: on objects it is the identity).
8. `Construction/Grothendieck/Strict.v` — constructor
   `IndexedCat_of_StrictFunctor : ∀ (F : B ⟶ StrictCat), (∀ b, UIP-on-objects (F b))
   → IndexedCat B` using the ToCat.v/StrictEq transport toolkit (`iso_of_eq`,
   `transport_trans`, `transport_functorial_dom/cod`); Hedberg corollary from
   fibrewise decidable object equality; plus the constant indexed category
   (all fibres a fixed D, reindexing Id — coherence trivial) with the sanity iso
   `Grothendieck (constant D) ≅[Cat] B ∏ D`.
9. `Construction/Grothendieck/RoundTrip.v` — the fibred-to-indexed direction at the
   split level: a `SplitCleaving` on `P : E ⟶ B` yields `IndexedCat B` (strict
   fibres, reindexing by lifts; split laws make `idx_comp`/`idx_id` identity-isos so
   coherence is trivial), and the comparison
   `Grothendieck (IndexedCat_of_SplitCleaving P) ⟶ E` over B is an
   `EquivalenceOfCategories`. Committed: the comparison functor + fully faithful;
   the equivalence conclusion is the phase's second-hardest proof — if it overruns,
   its two lemma pillars land and the conclusion follows the Section 6.4 discipline
   (ledger entry 17).
10. `Construction/Displayed/Codomain.v` — the codomain displayed category
    (`dobj x := ∃ d, d ~> x`; `dhom` = commuting triangles over f), its total
    category compared to the arrow-category flavour (`Construction/Slice.v`
    cross-referenced), and: cartesian lifts exist iff `HasPullbacks C` (consuming
    Phase 8's stability toolkit).

**Completion checklist.**

| Deliverable | File |
|---|---|
| `Displayed`, `dtransport`, `dtransport_id`, `dtransport_trans` | Theory/Displayed.v |
| `Total`, `Total_Proj` | Construction/Displayed/Total.v |
| `DCartesian`, `Cleaving`, `CartesianMorphism`, `ClovenFibration`, `SplitCleaving`, opfibration | Theory/Fibration.v |
| `IndexedCat` with `idx_cocycle`, `idx_unit_left/right` + honesty header | Construction/Indexed.v |
| `Grothendieck_Displayed`, `Grothendieck`, `Grothendieck_Proj` | Construction/Grothendieck.v |
| split opfibration structure | Construction/Grothendieck/Fibration.v |
| `Fiber`, fibre equivalence | Construction/Grothendieck/Fiber.v |
| `IndexedCat_of_StrictFunctor`, Hedberg corollary, constant example | Construction/Grothendieck/Strict.v |
| `IndexedCat_of_SplitCleaving`, round-trip comparison | Construction/Grothendieck/RoundTrip.v |
| codomain displayed + pullback-lifts | Construction/Displayed/Codomain.v |

`Print Assumptions` closed for `Grothendieck`, the fibre equivalence, and the
round-trip comparison.

**Risks and fallbacks.** (a) `dtransport` law-juggling in Total's associativity —
the derived-lemma pack in file 1 is budgeted for exactly this; do it first. (b) The
round-trip equivalence conclusion — staged as described in file 9. (c) If
`IndexedCat`'s obligation load in file 5 exceeds budget, the fallback is to weaken
NOTHING but reorder: prove each Displayed law as a standalone lemma about
`IndexedCat` (rule 2.4.6) before assembling.

**Universe note (item 4).** `IndexedCat B` stores a family of Categories, so
`Grothendieck A` lives at the join of B's object level and the fibres' levels — one
notch up, by necessity. Keep every construction here a fully polymorphic Definition;
never form "the category of displayed categories" (no consumer needs it); never
register `IndexedCat`-derived instances for resolution. `Print Universes` is part of
this phase's review.

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
