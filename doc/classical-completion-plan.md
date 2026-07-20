# Classical Category Theory Completion Plan (Phases 5-17)

> **Status: COMPLETED (historical record).** Every one of the seventeen
> developments planned below has since been delivered and merged; this file
> is retained as a record of the campaign, not as a list of outstanding work.
> The delivered artefacts are indexed in `CLAUDE.md` (see the "Key Files and
> Concepts" section) and enumerated in Section 4. Read the present tense
> throughout this document ("missing", "to add", "will") as describing the
> plan at the time it was written.

## 1. Purpose and how to use this document

This document is the complete, self-contained execution plan for adding the seventeen
missing classical developments to this repository (the `category-theory` Coq/Rocq
library, built with `-R . Category`). It continues the 2026-07 campaign whose phases
1-4 delivered the Markov / PROP / coloured-PROP / premonoidal stacks. It assumes the
executing agent has exactly two resources: this file and the repository. Every
convention, command, and interface fact needed to execute cold is spelled out below.

The seventeen items (each mapped to phases in Section 4):

1. Equivalence of categories (quasi-inverse class, adjoint equivalences, FF+ESO
   characterization, transport of structure)
2. Comonad theory (coKleisli, coalgebras, Store/Env/Traced, duality transfers)
3. F-algebras and F-coalgebras (Alg/Coalg, Lambek, Adamek, cata/ana, examples)
4. Fibrations and the Grothendieck construction (displayed categories primary)
5. Profunctors and the coend calculus (Sets coends, Fubini, Yoneda reduction,
   profunctor composition, representables vs adjunctions, Day convolution)
6. Monadicity (crude and precise Beck, adjoint lifting)
7. Adjoint functor theorems (RAPL prerequisite, GAFT, SAFT)
8. Factorization systems (orthogonality, OFS, strong epis, regular categories, images)
9. Reflective subcategories and localization (idempotent monads, orthogonal-subcategory
   localization)
10. Additive structure (zero objects, biproducts, preadditive, additive, kernels,
    abelian, CMon witness)
11. Topos theory (subobjects, classifier, elementary topos, FinSet witness, sheaf
    category)
12. Bicategory upgrade (coherence, pseudofunctors, lax transformations, modifications,
    adjunctions, mates, Cat instance)
13. Double categories (pseudo double categories, companions/conjoints, Sq, cospans)
14. Enriched upgrade (V-natural transformations, V-functor category, weighted limits,
    V=Sets and V=2 instances)
15. Karoubi envelope (idempotent completion, universal property, Cauchy completeness)
16. Lawvere theories (FinSet^op base, models, finitary-monad connection, PROP bridge)
17. Operads and multicategories (symmetric multicategories, operads, algebras,
    endomorphism operad)

Plus two cross-cutting notions: the Drinfeld centre of a monoidal category (delivered)
and star-autonomous categories (delivered at definition level; edges ledgered).

**How to execute:**

- Work one phase at a time, in order (Phase 5 through Phase 17). Do not start phase
  N+1 until phase N's definition of done holds. Phases 6-8 and 10-13 have limited
  mutual independence (noted per phase) and may be resequenced only if a quarantined
  proof needs decompression time; record any resequencing in the phase PR description.
- Re-read Section 2 (Conventions and Gates) at the start of every phase. It is binding.
- Each phase section gives: goal, dependency list, file list with skeletons for the
  load-bearing definitions, a completion checklist, risks with named fallbacks, and
  universe-hazard notes where relevant. The checklist is the definition of done,
  together with the global gate sequence in Section 2.2.
- Skeletons are written against the repository's actual interfaces (verified against
  the sources on branch `johnw/ct-phase4`, 2026-07). Field orientations (which way an
  iso points, which side a transport lands on) are fixed at implementation time; the
  skeleton commits the *data shape* and the *names*.
- If a checklist item resists proof, follow the escalation discipline in Section 6.4.
  Never delete a deliverable to make a phase green; never commit `Admitted`.

**Plan shape:** 13 phases, 135 planned `.v` deliverables (134 new files plus one
in-place upgrade of `Theory/Bicategory.v`), roughly 46,000 lines total at realistic
(post-blowup) estimates. Historical campaign phases ran 2-3x naive estimates; the
per-phase sizes below already include that factor. Thirteen phases (not twelve) is
forced by the hard per-phase envelope of 8-14 files / 2500-4000 lines: compressing to
twelve pushes two phases past the ceiling.

---

## 2. Conventions and Gates (binding for every phase)

### 2.1 Toolchain

- Default toolchain is Rocq 9.1, provided by the flake dev shell. Never hardcode nix
  store hashes; obtain the environment via `nix develop`.
- Compile a single file from the repository root:

  ```
  nix develop -c coqc -R . Category Theory/Equivalence.v
  ```

  (Alternatively, export `ROCQPATH` pointing at the Equations and rocq-stdlib
  user-contrib directories and `OCAMLPATH` at the Equations ocaml lib, read from the
  dev shell — but the `nix develop -c` form is the portable default.)
- Full build: `nix develop -c make -j8`.
- In-place text edits on the reference dev box: use `perl -pi -e`, not `sed -i ''`
  (the `sed` on PATH is GNU sed from nix; the BSD `-i ''` form silently misbehaves).
- Trailing whitespace is a hard gate: the flake's `checks` output includes a
  `format-check` derivation (flake.nix:191), so the Section 2.2 `nix flake check`
  step fails on any trailing whitespace in `.v` files. `make format-check` works
  and is the quick local probe (fixed in commit a87bdc6 — any older note claiming
  it "always fails" or "has a broken pipeline ending in head" is stale).

### 2.2 Verification sequence (the per-phase gate)

Run this sequence before opening the phase PR. All steps must pass.

1. **Hole scan** (on every file touched in the phase; expect no output):

   ```
   grep -nE 'Admitted|admit\.|admit;|Axiom |Axioms |Parameter |Parameters |Conjecture |Unset .*Checking' <files>
   ```

2. **Todo scan**: `make todo` must be silent on the new files. This also enforces the
   comment-vocabulary rule (Section 2.4, rule 10).
3. **Full build**: `nix develop -c make -j8` green.
4. **Assumptions gate**: every principal artifact named in the phase checklist passes
   `Print Assumptions` with output `Closed under the global context`. Run it after the
   build, e.g.:

   ```
   echo 'Require Import Category.Theory.Equivalence.FullFaithful.
         Print Assumptions FF_ESO_Equivalence.' \
     | nix develop -c coqtop -R . Category -quiet
   ```

   Rule: the `Require Import` path must be the module that *defines* the artifact
   (here `FF_ESO_Equivalence` lives in `Theory/Equivalence/FullFaithful.v`, i.e.
   module `Category.Theory.Equivalence.FullFaithful` — importing
   `Category.Theory.Equivalence` alone yields "reference not found").
   (Exception: artifacts in `Instance/Coq/` may report the pre-existing
   `functional_extensionality` only where `Instance/Coq.v` itself already does; the
   plan marks Coq-instance files where this is acceptable. Nothing else may appear.)
5. **Portability gate**: the 8.19/8.20 procedure in Section 2.3.
6. **Nix gate** (once per phase, before push):

   ```
   nix build && nix flake check
   ```

   (`nix build` builds the flake's default package, `category-theory_9_1`. The
   flake has NO bare `category-theory` attribute — its packages are
   `category-theory_8_19`/`_8_20`/`_9_0`/`_9_1` and `default` — so CLAUDE.md's
   `nix build .#category-theory` is stale and errors; do not use it.)

7. **Checklist audit**: run each checklist row's grep and confirm the hit. Where a
   checklist table has no Grep column (Phases 6-17), the command for each row is
   `grep -n "<Deliverable name>" <File>`, one grep per named deliverable in the
   row.
8. **Adversarial per-file review** (Section 6.5).

### 2.3 Portability gate: Coq 8.19 / 8.20

CI also builds Docker `coqorg/coq:8.19` and `8.20`. Stdlib names differ across
versions (examples: `length_app` is the 8.20+/9.x name, `app_length` the 8.19 name;
`Fin.case_L_R'` is 9.x-only). Any stdlib-dependent code must either use names present
in ALL supported versions or introduce a local shim lemma next to its use site.

Before pushing each phase, harvest incompatibilities with keep-going builds in
detached worktrees using the flake *packages* `category-theory_8_19` and
`category-theory_8_20` (they are packages, not devShells — the flake defines only a
`default` devShell; `nix develop` falls back to entering a package's build
environment when no devShell of that name exists, so the commands below work as
written — do not add devShells for this):

```
git worktree add ../ct-819 --detach HEAD
( cd ../ct-819 && nix develop .#category-theory_8_19 -c make -k -j8 ) |& tee /tmp/ct819.log
grep -nB2 'Error' /tmp/ct819.log        # harvest; add shims in the main tree; re-run
git worktree remove ../ct-819 --force
# repeat with category-theory_8_20 and /tmp/ct820.log
```

Phases 7, 16, and 17 are the likely shim producers (nat/le arithmetic, `List`/
`Permutation` lemmas, `Fin` codecs). Prefer designs that avoid version-fragile lemmas
entirely (e.g. the Type-valued `le_t` in Phase 7 avoids `le_unique`).

### 2.4 Proof-engineering rules

1. Hom-equality is `≈` (the homset setoid), never `=`. Object-level `=` is acceptable
   only where the repository already uses it deliberately (skeletal FinSet, the PROP
   class equations, StrictCat, `Morphism_equality` homsets).
2. Use explicit `Build_*` constructor applications for parameterized record instances;
   `{| |}` literals infer the wrong category in nested contexts.
3. Write class-typed binders in `@`-form (`Context {C : Category}`,
   `` `{@Full C D F} ``, `@Monad C M`), so instance arguments are pinned.
4. `Set Default Proof Using "Type"` is global (Lib.v). Any proof inside a `Section`
   whose *statement* does not mention a `Context` variable but whose *body* does must
   declare it: `Proof using C D E F.` — otherwise `Qed` is rejected.
5. Inductives close their section before lemmas about them are stated (the section
   parameters must be discharged so the induction principles generalize).
6. Heavy instances follow the standalone-lemma-then-explicit-record pattern: prove
   each law as a named lemma, then assemble the record with `Build_*` referencing the
   lemmas. This keeps obligation alignment and review tractable.
7. The GLOBAL Program obligation tactic is `cat_simpl` (Lib/Tactics.v:206). It
   silently discharges easy obligations, so `Next Obligation` blocks shift. For files
   with dependent records (sigma objects, displayed structures), set
   `#[local] Obligation Tactic := program_simpl.` (the `Monad/Kleisli.v` precedent)
   or `:= idtac.` (the `Construction/Comma.v` precedent) for predictable alignment.
8. `Set Default Goal Selector "!"` is global: every tactic line addresses exactly one
   focused goal — use bullets (`-`, `+`, `*`) everywhere.
9. `Set Uniform Inductive Parameters` is global: inside an inductive's body, refer to
   the partially-applied inductive (write `le_t m → le_t (S m)`, not
   `le_t n m → le_t n (S m)`). Also: the numeral `0` has no pattern interpretation
   under the library's scope stack — match on `O` / `S k`.
10. Comments must avoid the `make todo` trigger words: fail/fails/failure/abort/
    admit/admits/undefined/jww (case-insensitive). Use breakdown, obstruction,
    supports, carries, resists instead.
11. Shape categories (finite/ordinal diagram shapes) are declared fully
    universe-polymorphic with explicit binders in the `Instance/One.v` style —
    `Program Definition Omega@{o h p} : Category@{o h p}` with
    `homset := Morphism_equality` — so their levels unify with any target category
    when `Limit`/`Colimit` elaborates. Diagram functors (e.g. the omega-chain) must
    close their defining section before any `Colimit` statement is formed.
12. New dual notions are one-line `C^op` definitions plus an ergonomic accessor layer
    (the `Structure/Pushout.v` pattern), never hand-dualized. Use the `Build_*'` smart
    constructors (`Build_Category'`, `Build_Transform'`) that derive symmetric law
    fields.
13. Do not globally register instances that could hijack resolution. Structure
    transports (`Monoidal_op` precedent) and constructions with free universe levels
    are `Definition`s, not `Instance`s. Never make quasi-inverses, cleavages, or
    comonoid supplies inferable.
14. When `now apply <constructor>` of a universe-polymorphic inductive cannot solve a
    goal it plainly matches, supply the explicit term (`exact (ce_sym H)`).
15. Setoid-normalizing tactics `sapply`, `srewrite`, `srewrite_r` (Lib/Tactics.v) are
    the tools for rewriting under bundled-iso equivalences; `cat`, `proper`,
    `equivalence`, `construct` are the standard closers.

### 2.5 Load-bearing repository facts

These facts about the current sources are relied on throughout; do not rediscover
them. Paths are repo-relative. All were verified 2026-07 on `johnw/ct-phase4`.

**Core.**
- `Theory/Category.v:37` — `Class Category@{o h p | h <= p}` with setoid homsets
  (`homset : ∀ X Y, Setoid (X ~> Y)`), primitive `comp_assoc` AND `comp_assoc_sym`
  (so `C^op^op = C` by reflexivity). Coercion `obj : Category >-> Sortclass`.
  `Morphism_equality` (strict-equality homset marker) also lives here.
- `Lib/Setoid.v` — `equiv` is a Type-valued `crelation`; `Unique` (notation `∃!`) is
  a proof-relevant record with accessors `unique_obj`, `unique_property`,
  `uniqueness`. Mediators are *extracted*, never chosen. `injective`/`surjective`
  classes are up-to-`≈`; `surjective` is split (choice-carrying).
- `Theory/Isomorphism.v` — bundled `Isomorphism x y` (notation `x ≅ y`, `≅[C]`,
  `iso⁻¹`) AND the predicate `Class IsIsomorphism {x y} (f : x ~> y)` (line 55) with
  converter `IsIsoToIso`. Instances `iso_from_monic`, `iso_to_epic` exist (lines
  197, 208). In Sets: `x ≊ y` is iso of setoid objects.

**Functors and their equality.**
- `Theory/Functor.v` — `Functor` with `fobj`/`fmap`/`fmap_respects`/`fmap_id`/
  `fmap_comp`. TWO setoids on `C ⟶ D`: `Functor_Setoid` (the default `≈`, line 76)
  is *bundled natural isomorphism* (sigma of pointwise isos + conjugation coherence;
  access `` `1 e``/`` ``e`` for the iso family, `` `2 e`` for coherence; helpers
  `fun_equiv_to_fmap`, `fun_equiv_fmap_from`); and `Functor_StrictEq_Setoid` (line
  436) — propositional object equality plus transported morphism coherence, with a
  transport toolkit (`transport_trans`, `transport_functorial_dom/cod`, ...).
- CRITICAL CONSEQUENCE: a `Functor` into `Cat` carries `fmap_id`/`fmap_comp` only as
  *chosen natural isos with no coherence between different applications*. It is
  pseudofunctor data WITHOUT the cocycle/unit coherence. Phase 10 addresses this
  honestly (see the `IndexedCat` record).
- `Full` (line 259) is a *chosen section* `prefmap` with `fmap_sur` (no functoriality
  demanded of `prefmap` — issue #118); `Faithful` is `fmap_inj`. `FullyFaithful` is a
  Lemma (iso reflection), not a class. `FAlgebra F a := F a ~> a` and `FCoalgebra`
  are defined here (line ~308).
- `Theory/Natural/Transformation.v` — `Transform` with primitive `naturality` AND
  `naturality_sym`; `Build_Transform'` derives the latter. `nat_id`'s component is
  `fmap[F] id`, NOT bare `id` — a standing rewriting trap. Whiskering `N ⊲ F`,
  `F ⊳ N`; `nat_compose` (`∙`), `nat_hcompose`.
- `Instance/Fun.v` — `[C, D]` functor category; `[[[C, D]]](F, G)` hom-setoid
  packaging; `Theorem Functor_Setoid_Nat_Iso : F ≅[Fun] G ↔ F ≈ G` (line 178) with
  standalone `iso_equiv`/`equiv_iso`; unitor/associator isos `nat_λ`, `nat_ρ`
  (NOTE: their naming is reversed relative to the monoidal convention — flagged in a
  comment there), `nat_α`, plus coherence lemmas `nat_α_whisker_*`, `nat_α_nat_α`,
  whisker interchange `whisker_left_right`.
- `Instance/Cat.v` — Cat's homset is `Functor_Setoid`, so `≅[Cat]` IS equivalence of
  categories (Cat is Ho(Cat)). `Cat_Iso_to_Faithful`/`Cat_Iso_from_Faithful` proved;
  `Cat_Iso_to_Full`/`_from_Full` conditional. `Instance/StrictCat.v` is the strict
  variant; `Instance/StrictCat/ToCat.v` has `iso_of_eq`, `transport_cod_to_iso`,
  `strict_equiv_implies_fun_equiv`.

**Adjunctions and monads.**
- `Theory/Adjunction.v` — primary presentation is the hom-setoid iso `adj` with
  naturality fields; context is `F : D ⟶ C`, `U : C ⟶ D`, **F left adjoint**
  (`F ⊣ U`). Transposes `⌊f⌋`/`⌈f⌉`; derived `unit`, `counit`,
  `counit_fmap_unit`, `fmap_counit_unit`, `to_adj_unit`, `from_adj_counit`;
  uniqueness `right_adjoint_iso`/`left_adjoint_iso`. The end-of-file comment says
  adjoint (co)continuity is NOT formalized — Phase 5 closes this.
- Other presentations: `Adjunction/Natural/Transformation.v` (`F ∹ U`, unit/counit),
  `Adjunction/Hom.v` (single natural iso of hom-bifunctors, `hom_adj`), with
  conversions; `Adjunction/Opposite.v` dualizes. There is NO adjunction-composition
  file — Phase 5 adds one.
- `Theory/Monad.v` — `Monad` fields `ret`, `join`, `fmap_ret`, `join_fmap_join`,
  `join_fmap_ret`, `join_ret`, `join_fmap_fmap` (naturality is explicit fields, not
  Transforms). `Comonad := @Monad (C^op) (M^op)` (line 80).
- `Monad/Kleisli.v` — Kleisli category (`hom x y := x ~> M y`,
  `compose f g := join ∘ fmap[M] f ∘ g`), notations `<=<`, `>=>`. Uses
  `#[local] Obligation Tactic := program_simpl`.
- `Monad/Eilenberg/Moore.v` — the EM *category only* (objects `∃ a, TAlgebra T a`,
  homs `TAlgebraHom` compared on `t_alg_hom`); its header PROMISES the free/forgetful
  adjunction but does not build it — Phase 6 does. `Monad/Algebra.v` has `TAlgebra`
  (`t_alg`, `t_id`, `t_action`) and `TAlgebraHom` (`t_alg_hom_commutes`).
  LANDMINE (verified): `obj := ∃ a : C, TAlgebra T a` leaves `TAlgebra`'s implicit
  `@Monad C T` argument to Program, which seals it as the Qed-OPAQUE constant
  `EilenbergMoore_obligation_1 C T H` (body `λ C T H, H`, but opaque) — terms built
  against the ambient instance (e.g. `{| t_alg := join |}`) then do not unify with
  EM objects, and the sealed instance's monad laws are unusable. Phase 6 file 5's
  pre-step repairs this before anything constructs EM objects (Phases 6 and 9).
- `Monad/Adjunction.v` — `Adjunction_Monad : F ⊣ U → @Monad D (U ◯ F)` and the `∹`
  variant, both proved. The converse resolutions are NOT formalized (Phase 6).

**Limits and shapes.**
- `Structure/Cone.v` — `ACone` (apex-fixed) and `Cone` (bundled, coercion
  `vertex_obj`), `AConeEquiv`.
- `Structure/Limit.v` — `Limit` (bundled terminal cone + `ump_limits` via `∃!`),
  `IsALimit F c` (apex-pinned), `LimitSetoid`, `Colimit F := Limit (F^op)` (line 84).
- `Structure/Complete.v` — `Complete C := ∀ D F, Limit F` and `Cocomplete`: bare
  Definitions; smallness carried implicitly by universe polymorphism.
- `Structure/Equalizer.v` — `Equalizer F := Limit F` and `Coequalizer F := Colimit F`
  over the shape `Parallel` (`Instance/Parallel.v`; `APair f g : Parallel ⟶ C`
  builds the diagram). No unbundled fork/cofork accessors exist — Phases 8/11 add
  them.
- `Structure/Pullback.v` — `Pullback f g` is a standalone Record (NOT a
  Limit-of-shape) with `Pull`, `pullback_fst/snd`, `pullback_commutes`,
  `ump_pullbacks`; `HasPullbacks`; `pullback_unique`; `WeakPullback`. No pasting
  lemmas exist — Phase 8 adds them. `Structure/Pushout.v` is the op-dual with
  accessors and `HasPushouts`.
- `Structure/Terminal.v` — `Terminal` (`terminal_obj`, `one`, `one_unique`).
  `Structure/Initial.v` — **Initial is a Notation**:
  `Notation "'Initial' C" := (@Terminal (C^op))`, with projections `initial_obj`,
  `zero`, `zero_unique`. Consequence: instances of `@Initial X` are written as
  `Program Instance ... : @Initial X := {| terminal_obj := ...; one := ... |}`.
- `Structure/Cocartesian.v:30` — **Cocartesian is a Notation**:
  `Notation "'Cocartesian' C" := (@Cartesian (C^op))`. So `FinSet_Cocartesian`
  literally IS `@Cartesian (FinSet^op)` — Phase 16 exploits this.
- `Structure/Discrete.v` — a PREDICATE `Discrete (C : Category)` ("only identity
  morphisms"), not a construction. Phase 14's `Instance/Discrete.v` builds
  `DiscreteCat (A : Type)` and relates the two.
- Shapes in-tree: `Instance/Zero.v` (`_0`), `Instance/One.v` (`_1`, `Erase`),
  `Instance/Two.v` (`_2` the walking arrow, `TwoObj`/`TwoHom`), `Instance/Parallel.v`,
  `Instance/Roof.v`.

**Sets, Coq, FinSet.**
- `Instance/Sets.v` — `SetoidObject` (`carrier`, `is_setoid`), `SetoidMorphism`
  (`morphism`, `proper_morphism`), pointwise hom equiv. Has Terminal (poly_unit),
  Initial (False), `Sets_Product_Monoidal`; `injectivity_is_monic` (iff, proved),
  `bijective_is_iso`; `surjectivity_is_epic` is Aborted (universe obstruction, line
  ~352-399); line 348 notes Set's subobject classifier lives a universe up. Satellite
  `Instance/Sets/Pushout.v` computes pushouts via an inductive equivalence closure
  `pushout_eq` (funext-free quotient) — the TEMPLATE for all Phase 12 coend
  quotients. `Instance/Sets/Cartesian.v`, `.../Cocartesian.v` exist. No general
  completeness.
- `Instance/Coq.v` — objects are Types, homs functions, `≈` is pointwise `=`
  (`∀ x, f x = g x`). `Coq_Terminal`, `Coq_Cartesian`, `Coq_Cocartesian`,
  `Coq_Monoidal` exist. Core is axiom-free; only the Closed structure uses
  functional_extensionality.
- `Instance/FinSet.v` — skeletal FinSet (`obj := nat`,
  `hom m n := Fin.t m → Fin.t n`), `FinSet_Cocartesian` computing by `eq_refl` on
  closed inputs via `fin_split`/`fin_join`; `FinSet_HomEqProp`, `FinSet_ObjDecEq`;
  Initial 0, Terminal 1. No products/exponentials yet (Phase 17 adds them).

**Subcategories, comma, universal arrows, ends.**
- `Construction/Subcategory.v` — `Subcategory` record (`sobj`, `shom`, `scomp`,
  `sid`); `Sub S : Category` whose homsets compare FIRST projections only (witnesses
  are proof-irrelevant for `≈` — exploited by Centre, Det; exploit it again for
  Karoubi/Drinfeld/FAlg-style categories); `Incl`; `Full`, `Replete`, `Wide`
  predicates; `Full_Implies_Full_Functor`.
- `Construction/Comma.v` — `S ↓ T` with sigma objects/homs, projections
  `comma_proj`, `comma_proj1/2`; `Construction/Comma/Adjunction.v` exists.
- `Theory/Universal/Arrow.v` — `UniversalArrow c F` via `@Initial (=(c) ↓ F)`
  (`=(c)` is the constant functor from `Functor/Diagonal.v`);
  `ump_universal_arrows`; and PROVED assembly
  `LeftAdjointFunctorFromUniversalArrows` + `AdjunctionFromUniversalArrows` — the
  engine GAFT concludes with.
- `Structure/Wedge.v` — `Wedge F` (`wedge_obj`, `wedge_map`, condition
  `ump_wedges`); `Cowedge F := @Wedge (C^op) (D^op) (F^op)`.
- `Structure/End.v` — `End F` (wedge + `ump_ends`); `Coend F := @End (C^op) (D^op)
  (F^op)` (line 58) with NO covariant accessors — Phase 12 adds them.
- `Theory/Dinatural.v` — `Dinatural` with the hexagon; no composition (deliberate).
- `Theory/Kan/Extension.v` — `RightKan`/`LeftKan` (global, via `Induced := (− ◯ F)`
  adjunctions), `LocalRightKan`/`LocalLeftKan` (proved restriction instances);
  `left_adjoint_impl` proved; `left_adjoints_preserve` is **Aborted** (open).
- `Functor/Hom.v` — hom bifunctor `Hom C : C^op ∏ C ⟶ Sets`, curried `[Hom c,─]`,
  `[Hom ─,c]`, plus `Yoneda_Embedding'` (line 109; the primed hom-iso-reflects-iso
  corollary consumed by `Structure/UniversalProperty.v` — it is NOT in the Yoneda
  file). `Functor/Hom/Yoneda.v` has `Yoneda_Lemma`, `Covariant_Yoneda_Lemma`, and
  the unprimed `Yoneda_Embedding` / `Covariant_Yoneda_Embedding`.
- `Functor/Structure/Cartesian.v:49` — `Class CartesianFunctor` (finite-product-
  preserving functor) with an op-reused cocartesian dual. Phase 16 reuses it.
- `Structure/UniversalProperty.v` — `IsUniversalProperty` via representability;
  `univ_property_unique_up_to_unique_iso` proved.

**Morphism classes and misc.**
- `Theory/Morphisms.v` — `Idempotent`, `Involutive`, `Section f` (f split MONO;
  field `section` is the retraction — mind the naming), `Retraction` (split epi),
  `SplitIdempotent`, `Epic`, `Monic`, with composition/flip lemmas. No orthogonality.
- `Instance/Fact.v` — per-morphism factorization category `Fact f` with
  `Fact_Proj`; initial/terminal factorizations mentioned in comments only.
- `Theory/Bicategory.v` — data-only class (196 lines): `bi0cell`, `bicat x y`
  definitional hom-categories, `hcompose : bicat y z ∏ bicat x y ⟶ bicat x z`; NO
  unitors/associator/coherence (2018 TODO). Only comment-level consumers
  (`Construction/Span/Category.v`, `Construction/Cospan/Category.v`) — verified, so
  Phase 13 may refactor in place.
- `Construction/Enriched.v` — `Enriched K` (V-categories: `eobj`, `ehom`, `eid`,
  `ecompose`, laws via the typed-equality notation `f << A ~~> B >> g`),
  `EnrichedFunctor`, and proved `Category_is_Enriched_over_Set`,
  `Functor_is_Enriched_over_Set`. Nothing else enriched exists.
- `Theory/Sheaf.v` — `Presheaf`, `Presheaves`; `Site` carries ONE covering family
  per object (weaker than a coverage — acknowledged in its comment); `Sheaf` with a
  gluing field. No category of sheaves (Phase 17), no sheafification (ledgered).
- `Construction/Opposite/Monoidal.v` — `Monoidal_op`, `Braided_op`, `Symmetric_op`
  as Definitions (NOT instances). Caveat documented there:
  `Monoidal_op (Monoidal_op M)` is NOT definitionally `M` (Qed-opaque fields).
- CLOSED-STRUCTURE TRAP: `Structure/Closed.v` is a stub — its `Class Closed` has
  been commented out since a 2018 jww TODO; only the `Curry`/`Flip` helper functors
  are live, and its own header redirects onward. (CLAUDE.md's "Structure/Closed.v:
  Exponentials and internal hom" entry is stale.) The LIVE classes are:
  `Structure/Cartesian/Closed.v` — `Class Closed` sectioned over
  `` `{@Cartesian C} `` with `exponent_obj`, `y ^ x` notation,
  `exp_iso`/`curry`/`eval` (what `@Closed C _` and `Pow a := Ω ^ a` need, cf.
  `Coq_Closed : @Closed Coq _` in `Instance/Coq.v`); and
  `Structure/Monoidal/Closed.v` — `Class ClosedMonoidal` with infix `⇒`
  (where `x ⇒ dualizer` lives). Cite the class you mean, never `Structure/Closed.v`.
- `Structure/Premonoidal/Centre.v` — the premonoidal centre Z(C) (a monoidal wide
  subcategory via `Sub`). This is NOT the Drinfeld centre; Phase 12's
  `Structure/Monoidal/Drinfeld.v` must cross-reference and distinguish.
- `Theory/Algebra/Monoid/Hom.v`, `.../Comonoid/Hom.v` — `Mon`/`Comon` categories
  with forgetful functors; comonoid machinery feeds Phase 16's terminal-operad
  example.
- The conjunction used inside `∃!` bodies follows `Structure/Pullback.v`'s
  `ump_pullbacks` precedent (`... ≈ q1 ∧ ... ≈ q2`) — use the same form.

**Known in-tree gaps this plan closes or touches** (acknowledged in source comments):
RAPL/LAPC (Phase 5); EM free/forgetful adjunction (Phase 6); left-adjoints-preserve-
Kan Abort (Phase 5 stretch); pullback-as-product+equalizer direction needed by the
topos class (Phase 17 carries finite limits explicitly instead); FinSet
monoidal/products (Phases 16-17); Sets epis-are-surjections Abort (NOT needed —
Phase 8's image factorization avoids it); Bicategory coherence (Phase 13).

### 2.6 Duality leverage

- `Comonad := @Monad (C^op) (M^op)`; `Colimit F := Limit (F^op)`;
  `Coend := End (F^op)`; `Initial C := Terminal (C^op)` (notation);
  `Cocartesian C := @Cartesian (C^op)` (notation);
  `IsPushout := @Pullback (C^op)`; `Cocomma`; `Cowedge` — all definitional.
- New dual developments RIDE these: define the dual as a one-liner on `C^op`, then
  provide a covariant accessor file (the `Structure/Pushout.v` pattern: named
  accessors + converters). Phase 6's coKleisli/co-EM, Phase 7's `FCoalg`, Phase 11's
  Cokernel, and Phase 14's Coreflective all follow it.
- `Construction/Opposite/Monoidal.v` transports monoidal structure to `C^op` for
  costrength (Phase 6). Remember the double-op caveat: transfers compose up to `≈`,
  not definitionally.
- Symmetric law fields (`comp_assoc_sym`, `naturality_sym`, `from_adj_nat_*`) exist
  to make duality free — always populate them via the `Build_*'` smart constructors.

### 2.7 Delivery conventions

- One branch per phase, stacked on the previous: `johnw/ct-phase5` ...
  `johnw/ct-phase17`. Phase 5 stacks on the latest landed campaign branch (or
  `master` if phase 4 has merged).
- One atomic commit per file, INCLUDING its `_CoqProject` line in the same commit.
  `_CoqProject` is an explicit alphabetized list (no globs) — insert each new path in
  alphabetical order.
- Conventional-commit style: `feat(Equivalence): ...`, `feat(Karoubi): ...`,
  `docs(CLAUDE): ...`. Scope is the principal module name.
- Commit with `LEFTHOOK_EXCLUDE=nix-build,nix-check git commit ...` (the pre-commit
  nix builds are too slow per-commit); run `nix build` and `nix flake check` once
  per phase before pushing (Section 2.2 step 6 — no `.#category-theory` attribute
  exists).
- Each phase ends with a `docs(CLAUDE)` commit adding a Key Files entry for the
  phase's development to `CLAUDE.md` (follow the style of the existing
  Premonoidal/PROP entries).
- Full mechanics, PR stacking, and the escalation discipline: Section 6.

---

## 3. Phase plan

Sizing note: "est." lines are realistic (post-blowup) totals. Every phase must stay
within 8-14 files / 2500-4000 estimated lines; if implementation reveals a phase
breaching 4000, split at the file boundary noted in its risks section rather than
compressing proofs.

---

### Phase 5 — Equivalence of categories; preservation vocabulary; RAPL/LAPC; transport

**Item 1 complete; the RAPL half of item 7.** Branch `johnw/ct-phase5`.
Depends on: in-tree only. Est. 10 files / ~3200 lines.

**Goal.** The single most-consumed missing notion. The quasi-inverse class (whose
unit/counit ARE bundled natural isos, since `Functor_Setoid`'s `≈` is exactly that),
the Full+Faithful+essentially-surjective characterization in both directions, adjoint
equivalences (where the triangle-style laws live), RAPL/LAPC closing the documented
gap at the end of `Theory/Adjunction.v`, and transport of (co)limits, adjunctions,
and monoidal structure along equivalences. Consumers: Phases 8, 9, 10, 14, 16.

**Files.**

1. `Theory/Equivalence.v` — the core classes and Cat bridge:

   ```coq
   Class EssentiallySurjective {C D : Category} (F : C ⟶ D) := {
     eso_obj : D → C;                     (* split, choice-carrying: house style *)
     eso_iso (d : D) : F (eso_obj d) ≅ d
   }.

   Class EquivalenceOfCategories {C D : Category} (F : C ⟶ D) := {
     quasi_inverse : D ⟶ C;
     equivalence_counit : F ◯ quasi_inverse ≈ Id[D];  (* Functor_Setoid ≈ = nat iso *)
     equivalence_unit   : Id[C] ≈ quasi_inverse ◯ F
   }.
   ```

   plus `Equivalence_to_Cat_Iso : EquivalenceOfCategories F → C ≅[Cat] D` and its
   converse (definitional repacking — the quasi-inverse data IS a Cat-iso),
   round trips through `≅[Fun]` via `Functor_Setoid_Nat_Iso`, the identity
   equivalence, and symmetry (`quasi_inverse` carries an `EquivalenceOfCategories`
   back). Do NOT register any of this for instance resolution (rule 2.4.13).
2. `Theory/Equivalence/FullFaithful.v` — the characterization, both directions,
   naming the real classes:

   ```coq
   Program Definition ff_eso_inverse `(F : C ⟶ D)
     `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} : D ⟶ C := {|
     fobj := eso_obj;
     fmap := fun d d' g => prefmap (from (eso_iso d') ∘ g ∘ to (eso_iso d))
   |}.
   Theorem FF_ESO_Equivalence `(F : C ⟶ D)
     `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
     EquivalenceOfCategories F.
   Theorem Equivalence_Faithful `(E : @EquivalenceOfCategories C D F) : Faithful F.
   Theorem Equivalence_Full     `(E : @EquivalenceOfCategories C D F) : Full F.
   Theorem Equivalence_EssSurj  `(E : @EquivalenceOfCategories C D F) :
     EssentiallySurjective F.
   ```

   Proof notes (binding): `prefmap` carries no properness (issue #118) — recover it
   from `Faithful` (`fmap_inj` applied after `fmap_sur` rewrites); the counit is
   literally `eso_iso`; faithfulness of the quasi-inverse comes from the counit's
   conjugation coherence (`` `2 equivalence_counit ``) plus the in-tree
   `iso_to_epic`/`iso_from_monic` instances. Watch rule 2.4.4 (`Proof using`).
3. `Theory/Equivalence/Adjoint.v` — adjoint equivalences via the real
   `IsIsomorphism` predicate (Theory/Isomorphism.v:55):

   ```coq
   Class AdjointEquivalence {C D : Category} (F : C ⟶ D) (U : D ⟶ C) := {
     adj_equivalence : F ⊣ U;
     adj_equiv_unit_iso   (x : C) : IsIsomorphism (@unit   _ _ _ _ adj_equivalence x);
     adj_equiv_counit_iso (y : D) : IsIsomorphism (@counit _ _ _ _ adj_equivalence y)
   }.
   Theorem Equivalence_to_AdjointEquivalence `(E : @EquivalenceOfCategories C D F) :
     AdjointEquivalence F quasi_inverse.
   ```

   Proof route (binding): do NOT rectify the counit by the zig-zag argument. Extract
   Full/Faithful/ESO from E (file 2), then build the hom-setoid `⊣` DIRECTLY:
   `to f := prefmap (from (eso_iso d) ∘ f)`, `from g := to (eso_iso d) ∘ fmap[F] g`;
   naturality by `fmap_inj` + `fmap_sur`; the unit/counit are then iso by
   construction. Also: `AdjointEquivalence F U → EquivalenceOfCategories F` and the
   swapped adjunction `U ⊣ F`.
4. `Adjunction/Compose.v` — composition of adjunctions (verified absent in-tree):
   `Adjunction_Compose : F ⊣ U → F' ⊣ U' → (F' ◯ F) ⊣ (U ◯ U')` in the hom-setoid
   presentation (compose the two `adj` isos in Sets), plus identity adjunction
   `Id ⊣ Id`. Needed by file 8.
5. `Structure/Limit/Preservation.v` — reusable preservation vocabulary (consumed by
   Phases 7, 9, 14, 16):

   ```coq
   Class PreservesLimit `(G : J ⟶ C) `(F : C ⟶ D) := {
     preserves_limit (L : Limit G) : IsALimit (F ◯ G) (F L)
     (* F L, not F (limit_cone L): limit_cone is a class projection whose Limit
        argument is TC-resolved, so applying it to L is ill-formed. F L elaborates
        through the coercion chain Limit >-> Cone >-> vertex_obj (verified); the
        explicit form is @limit_cone _ _ _ L. *)
   }.
   Definition PreservesColimit `(G : J ⟶ C) `(F : C ⟶ D) := ...
     (* via op: PreservesLimit of G^op for F^op, plus covariant accessors *)
   Definition PreservesAllLimits {C D} (F : C ⟶ D) :=
     ∀ (J : Category) (G : J ⟶ C), PreservesLimit G F.
   Class ReflectsIsos {C D} (F : C ⟶ D) := {
     reflects_iso {x y} (f : x ~> y) : IsIsomorphism (fmap[F] f) → IsIsomorphism f }.
   ```

6. `Adjunction/Continuity.v` — **RAPL**, proved directly: given `A : F ⊣ U` and
   `L : Limit G`, build `IsALimit (U ◯ G) (U L)` with legs `fmap[U] (vertex_map j)`;
   mediate a competing cone by transposing its legs with `⌈−⌉` (cone coherence via
   `from_adj_nat_r`), mediating in C, transposing back with `⌊−⌋`; uniqueness via
   the `adj` iso. Corollary `right_adjoint_preserves_limits : PreservesAllLimits U`;
   **LAPC** by `Adjunction/Opposite.v`. Retire the "not formalized" comment at the
   end of `Theory/Adjunction.v`. Budgeted stretch: attempt the Aborted
   `left_adjoints_preserve` in `Theory/Kan/Extension.v` with this machinery; if it
   resists, update its comment to cite this file (comment-update is the fallback —
   the Abort is a pre-existing non-hole).
7. `Theory/Equivalence/Limit.v` — equivalences preserve, reflect, and CREATE limits:
   preserve = RAPL on the adjoint equivalence; reflect via fully-faithful
   (`prefmap`/`fmap_inj` on mediators); create = `Limit (F ◯ G) → Limit G` via the
   quasi-inverse plus iso-of-cones. Colimit versions by op.
8. `Theory/Equivalence/Adjunction.v` — transport of adjunctions: given `F ⊣ U`
   between C, D and equivalences `C ≃ C'`, `D ≃ D'`, the conjugated adjunction
   between C', D' (three-fold `Adjunction_Compose` with the adjoint equivalences
   from file 3).
9. `Theory/Equivalence/Monoidal.v` — transport of monoidal structure:
   `Transported_Monoidal (E : EquivalenceOfCategories F) : @Monoidal C → @Monoidal D`
   as a Definition (never an Instance — the `Monoidal_op` convention). Tensor
   `(d, d') ↦ F (quasi_inverse d ⨂ quasi_inverse d')`; unitors/associator assembled
   from unit/counit isos + `fobj_iso`. STAGING (binding): land the data + unitors +
   associator + naturality first as a named record `MonoidalTransportData`, then the
   pentagon/triangle proofs as the file's final lemmas; the named fallback moves
   only pentagon/triangle to a Phase 12 rider commit (ledger entry 17).
10. `Theory/Equivalence/Bundled.v` — routine: sigma bundle
    `C ≃ D := { F : C ⟶ D & EquivalenceOfCategories F }` with scope-guarded
    notation, plus reflexivity/symmetry/transitivity lemmas at the bundled level.

**Completion checklist (each row grep-checkable; all `Print Assumptions` closed).**

| Deliverable | File | Grep |
|---|---|---|
| `EssentiallySurjective`, `EquivalenceOfCategories`, `Equivalence_to_Cat_Iso` | Theory/Equivalence.v | `grep -n "Class EquivalenceOfCategories" Theory/Equivalence.v` |
| `ff_eso_inverse`, `FF_ESO_Equivalence`, `Equivalence_Full/Faithful/EssSurj` | Theory/Equivalence/FullFaithful.v | `grep -n "FF_ESO_Equivalence" Theory/Equivalence/FullFaithful.v` |
| `AdjointEquivalence`, `Equivalence_to_AdjointEquivalence` | Theory/Equivalence/Adjoint.v | `grep -n "AdjointEquivalence" Theory/Equivalence/Adjoint.v` |
| `Adjunction_Compose` | Adjunction/Compose.v | `grep -n "Adjunction_Compose" Adjunction/Compose.v` |
| `PreservesLimit`, `PreservesColimit`, `PreservesAllLimits`, `ReflectsIsos` | Structure/Limit/Preservation.v | `grep -n "Class PreservesLimit" Structure/Limit/Preservation.v` |
| `right_adjoint_preserves_limits`, `left_adjoint_preserves_colimits` | Adjunction/Continuity.v | `grep -n "right_adjoint_preserves_limits" Adjunction/Continuity.v` |
| RAPL comment retired (now cites Adjunction/Continuity.v) | Theory/Adjunction.v | `grep -n "Adjunction/Continuity" Theory/Adjunction.v` |
| `equivalence_preserves_limits`, `equivalence_reflects_limits`, `equivalence_creates_limits` | Theory/Equivalence/Limit.v | grep each name |
| `Transported_Adjunction` | Theory/Equivalence/Adjunction.v | grep name |
| `MonoidalTransportData`, `Transported_Monoidal` | Theory/Equivalence/Monoidal.v | grep names |
| Bundled `≃` + refl/sym/trans | Theory/Equivalence/Bundled.v | grep `Equivalence_refl` etc. |

**Risks and fallbacks.** (a) `Transported_Monoidal` pentagon blowup → staged fallback
above (data record lands; coherence rider tracked in ledger 17; nothing dropped).
(b) Setoid rewriting under bundled isos in file 2 — use `sapply`/`srewrite`; the
conjugation helpers `fun_equiv_to_fmap`/`fun_equiv_fmap_from` are the intended tools.
(c) Name hygiene: `Equivalence` clashes with the stdlib class — always
`EquivalenceOfCategories`; scope-guard the `≃` notation in `category_theory_scope`.

**Universe note (item 1).** All statements are per-functor between two fixed
categories; nothing quantifies over Cat's objects at a fixed level. The Cat-bridge
conversions touch `Cat@{o+1,...}` — keep them Definitions so universe constraints
stay local to use sites. Never make `EquivalenceOfCategories` resolvable.

**Definition of done.** Section 2.2 gate + every checklist row hits.

---

### Phase 6 — Comonad theory and monad resolutions

**Item 2 complete; closes the documented Eilenberg-Moore/Kleisli adjunction gap.**
Branch `johnw/ct-phase6`. Depends on: Phase 5 (only for review-order; no hard code
dependency). Est. 10 files / ~3000 lines.

**Goal.** A usable covariant comonad API over the one-line
`Comonad := @Monad (C^op) (M^op)`, coKleisli and co-Eilenberg-Moore by duality with
covariant accessors, Env/Store/Traced instances on `Coq`, costrength riding
`Construction/Opposite/Monoidal.v`, and — on the monad side — the Kleisli and
Eilenberg-Moore free/forgetful adjunctions promised by `Monad/Eilenberg/Moore.v`'s
header (Phase 9's monadicity needs them).

**Files.**

1. `Comonad/Core.v` — covariant accessors and laws, all definitional op-reads:

   ```coq
   Section ComonadAPI.
   Context {C : Category} {W : C ⟶ C} (H : @Comonad C W).
   Definition extract   {x} : W x ~> x       := @ret  (C^op) (W^op) H x.
   Definition duplicate {x} : W x ~> W (W x) := @join (C^op) (W^op) H x.
   Definition extend {x y} (f : W x ~> y) : W x ~> W y := fmap[W] f ∘ duplicate.
   Lemma extract_duplicate      {x} : extract ∘ duplicate ≈ id[W x].
   Lemma fmap_extract_duplicate {x} : fmap[W] extract ∘ duplicate ≈ id[W x].
   Lemma duplicate_duplicate    {x} :
     duplicate ∘ duplicate ≈ fmap[W] duplicate ∘ duplicate.  (* orientation per op-read *)
   ```

2. `Comonad/CoKleisli.v` — `Definition CoKleisli := (@Kleisli (C^op) (W^op) H)^op`,
   with the hom-unfolding lemma `cokleisli_hom : (x ~{CoKleisli}~> y) = (W x ~{C}~> y)`
   (holds by `reflexivity`; requires `Require Import Category.Functor.Opposite` for
   `W^op`), agreement lemma `f =>= g ≈ f ∘ extend g`, and `=>=`/`=<=` notations.
3. `Comonad/Coalgebra.v` — covariant `WCoalgebra` (`w_coalg : a ~> W a`,
   `w_counit_law`, `w_coaction`) and `WCoalgebraHom`;
   `CoEilenbergMoore := (@EilenbergMoore (C^op) (W^op) H)^op`; the category of
   covariant coalgebras and its isomorphism (in Cat) with `CoEilenbergMoore`.
4. `Monad/Kleisli/Adjunction.v` — `Kleisli_Free : C ⟶ Kleisli`
   (`fobj := id-on-objects`, `fmap f := ret ∘ f`), `Kleisli_Forget : Kleisli ⟶ C`
   (`fmap f := join ∘ fmap[M] f`), `Kleisli_Adjunction : Kleisli_Free ⊣ Kleisli_Forget`
   (the hom iso is the identity on `x ~> M y`), and agreement
   `Kleisli_Monad_agrees : Kleisli_Forget ◯ Kleisli_Free ≈ M` with a `join`-agreement
   lemma. Note `Monad/Kleisli.v` sets `#[local] Obligation Tactic := program_simpl` —
   do the same here.
5. `Monad/Eilenberg/Moore/Adjunction.v` — closes the Moore.v header promise.
   PRE-STEP (binding, same commit as the Moore.v header update): repair
   `Monad/Eilenberg/Moore.v` before building against it. Its
   `obj := ∃ a : C, TAlgebra T a` elaborates `TAlgebra`'s implicit `@Monad C T`
   argument into the Qed-opaque `EilenbergMoore_obligation_1` (see the Section 2.5
   Moore.v landmine): the `EM_Free` skeleton below then breaks against the current
   file with "Unable to unify EilenbergMoore_obligation_1 C T H with H", and the
   algebra-law obligations cannot be discharged. Fix: name the instance binder
   (`H : @Monad C T`) and write `obj := ∃ a : C, @TAlgebra C T H a` (alternative:
   `#[local] Set Transparent Obligations.` before the definition). Verified: with
   the explicit-`@` obj, `EM_Free`'s object part compiles and its obligations
   discharge with `join_ret`/`join_fmap_join` exactly as sketched.

   ```coq
   Program Definition EM_Forget (T : C ⟶ C) `{@Monad C T} : EilenbergMoore T ⟶ C :=
     {| fobj := fun a => `1 a; fmap := fun _ _ f => t_alg_hom[f] |}.
   Program Definition EM_Free (T : C ⟶ C) `{@Monad C T} : C ⟶ EilenbergMoore T :=
     {| fobj := fun a => (T a; {| t_alg := @join C T _ a |}) |}.
     (* algebra laws: join_ret, join_fmap_join *)
   Theorem EM_Adjunction : EM_Free T ⊣ EM_Forget T.
     (* ⌊f⌋ := t_alg_hom[f] ∘ ret ; ⌈g⌉ := the algebra hom  t_alg ∘ fmap[T] g *)
   Theorem EM_Monad_agrees : EM_Forget T ◯ EM_Free T ≈ T.
   ```

   Update the Moore.v header comment to point here (comment edit in the same commit
   as the pre-step repair and this file).
6. `Comonad/Duality.v` — the transfer package: `Comonad_of_op_Monad` /
   `op_Monad_of_Comonad` (definitional round trips); `Adjunction_Comonad :
   F ⊣ U → @Comonad C (F ◯ U)` by dualizing `Adjunction_Monad` through
   `Adjunction/Opposite.v` (no hand-dualization); `CoKleisli_Adjunction` and
   `CoEM_Adjunction` obtained from files 4-5 by op (each under ~20 lines).
7. `Comonad/Strong.v` — costrength: `CostrongComonad` defined as the in-tree
   `StrongMonad` (Monad/Strong.v) over `(C^op, Monoidal_op M)`, unfolded to covariant
   fields; transfer lemmas both ways. Definitions, not Instances; cite the
   `Monoidal_op (Monoidal_op M) ≉ M`-definitionally caveat where round trips are
   stated up to `≈`.
8. `Instance/Coq/Comonad/Env.v` — `EnvF e := (e * −)` on `Coq`;
   `@Comonad Coq (EnvF e)` built as `@Monad (Coq^op) ((EnvF e)^op)` with
   `extract := snd`, `duplicate '(e0,x) := (e0,(e0,x))`. `Coq`'s `≈` is pointwise
   `=`, so laws are by destructuring `match` — no funext (assumptions gate must stay
   fully closed for this file).
9. `Instance/Coq/Comonad/Store.v` — `StoreF s x := ((s → x) * s)`;
   `extract '(f,s0) := f s0`; `duplicate '(f,s0) := ((fun s => (f,s)), s0)`.
   Pointwise `=`; closed assumptions.
10. `Instance/Coq/Comonad/Traced.v` — `TracedF m x := m → x` over a section-context
    monoid `(m, mempty, mappend, laws)`; comonad laws pointwise. If a law needs
    eta-for-functions beyond pointwise reasoning, restate the offending equality
    pointwise (the homset already is pointwise) — do NOT import funext.

**Completion checklist.**

| Deliverable | File |
|---|---|
| `extract`, `duplicate`, `extend`, three laws | Comonad/Core.v |
| `CoKleisli`, `cokleisli_hom`, `=>=` | Comonad/CoKleisli.v |
| `WCoalgebra`, `CoEilenbergMoore`, iso of categories | Comonad/Coalgebra.v |
| `Kleisli_Free`, `Kleisli_Forget`, `Kleisli_Adjunction`, `Kleisli_Monad_agrees` | Monad/Kleisli/Adjunction.v |
| `EM_Free`, `EM_Forget`, `EM_Adjunction`, `EM_Monad_agrees`; Moore.v header updated | Monad/Eilenberg/Moore/Adjunction.v |
| `Adjunction_Comonad`, `CoKleisli_Adjunction`, `CoEM_Adjunction` | Comonad/Duality.v |
| `CostrongComonad` + transfers | Comonad/Strong.v |
| `EnvF` comonad | Instance/Coq/Comonad/Env.v |
| `StoreF` comonad | Instance/Coq/Comonad/Store.v |
| `TracedF` comonad | Instance/Coq/Comonad/Traced.v |

`Print Assumptions` closed for `EM_Adjunction`, `Kleisli_Adjunction`,
`Adjunction_Comonad`, and all three `Instance/Coq` comonads.

**Risks and fallbacks.** Env/Store eta-for-pairs friction under pointwise `=` →
destructuring `match` bindings resolve it; if a corner genuinely resists, move that
single instance to `Sets` (setoid homs make the law `proper`-trivial) and record the
move in the phase PR — the deliverable is the comonad witness, not its host category.
No other notable risk: the duality one-liners are mechanical given
`Functor/Opposite`.

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

### Phase 9 — Monadicity

**Item 6 complete.** Branch `johnw/ct-phase9`. Depends on: Phase 5 (equivalences,
`ReflectsIsos`), Phase 6 (EM adjunction, including its Moore.v `@TAlgebra`
pre-step repair — files 3-6 here construct EM objects and need it), Phase 8
(`IsCoequalizer` API). Est. 8 files / ~3400 lines.

**Goal.** Split and reflexive coequalizers in the setoid setting, the Eilenberg-Moore
comparison functor, crude monadicity FULLY proven, Beck's precise monadicity theorem
(both directions), and adjoint lifting in the crude case.

**Files.**

1. `Structure/Coequalizer/Split.v` —

   ```coq
   Record SplitCoequalizer {C : Category} {x y : C} (f g : x ~> y) := {
     scoeq_obj : C;
     scoeq_e : y ~> scoeq_obj;  scoeq_s : scoeq_obj ~> y;  scoeq_t : y ~> x;
     scoeq_law1 : scoeq_e ∘ f ≈ scoeq_e ∘ g;
     scoeq_law2 : scoeq_e ∘ scoeq_s ≈ id;
     scoeq_law3 : f ∘ scoeq_t ≈ id;
     scoeq_law4 : g ∘ scoeq_t ≈ scoeq_s ∘ scoeq_e
   }.
   Theorem split_coequalizer_is_coequalizer :
     ∀ (S : SplitCoequalizer f g), IsCoequalizer f g (scoeq_obj S) (scoeq_e S).
   Theorem functor_preserves_split `(F : C ⟶ D) :
     SplitCoequalizer f g → SplitCoequalizer (fmap[F] f) (fmap[F] g).  (* absoluteness *)
   ```

2. `Structure/Coequalizer/Reflexive.v` — reflexive pairs (common section
   `s` with `f ∘ s ≈ id ∧ g ∘ s ≈ id`), `Class HasReflexiveCoequalizers`.
3. `Monad/Comparison.v` — for `F : D ⟶ C`, `U : C ⟶ D`, `A : F ⊣ U` (mind the
   orientation: F is the LEFT adjoint; the monad `U ◯ F` lives on D):

   ```coq
   Program Definition EM_Comparison {C D} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
     C ⟶ EilenbergMoore (U ◯ F) := {|
     fobj := fun c => (U c; {| t_alg := fmap[U] (@counit _ _ _ _ A c) |})
   |}.
   Theorem EM_Comparison_Forget : EM_Forget (U ◯ F) ◯ EM_Comparison A ≈ U.
   Theorem EM_Comparison_Free   : EM_Comparison A ◯ F ≈ EM_Free (U ◯ F).
   Definition Monadic {C D} (U : C ⟶ D) :=
     ∃ (F : D ⟶ C) (A : F ⊣ U), EquivalenceOfCategories (EM_Comparison A).
   ```

4. `Monad/Monadicity/BeckObjects.v` — the engine room: for an algebra `(a, α)` the
   canonical reflexive pair `(F α, counit (F a)) : F (U F a) ⇉ F a`, the split
   coequalizer of its U-image, and the two shared pillars: `EM_Forget` reflects isos,
   and `EM_Forget` CREATES coequalizers of U-split pairs (stated concretely: given a
   pair whose image under `EM_Forget` has a `SplitCoequalizer`, there is a chosen
   algebra structure on the split coequalizer object making it a coequalizer in
   `EilenbergMoore`, uniquely).
5. `Monad/Monadicity/Crude.v` — the crude monadicity theorem, fully proven:

   ```coq
   Theorem crude_monadicity {C D} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
     `{@HasReflexiveCoequalizers C}
     (pres : ∀ ..., PreservesColimit ... U)   (* U preserves reflexive coequalizers *)
     (refl : ReflectsIsos U) :
     EquivalenceOfCategories (EM_Comparison A).
   ```

   Quasi-inverse: an algebra maps to the coequalizer of its canonical pair; the
   unit/counit natural isos come from `ReflectsIsos` + split absoluteness (file 1).
6. `Monad/Monadicity/Beck.v` — the precise theorem:

   ```coq
   Class CreatesUSplitCoequalizers {C D} (U : C ⟶ D) := {
     create_coeq {x y} (f g : x ~> y)
       (S : SplitCoequalizer (fmap[U] f) (fmap[U] g)) :
       { q : C & { e : y ~> q & IsCoequalizer f g q e
           ∧ (* U-image matches S up to the canonical iso *) ... } };
     create_coeq_unique : ...
   }.
   Theorem beck_monadicity : F ⊣ U → CreatesUSplitCoequalizers U →
     EquivalenceOfCategories (EM_Comparison A).
   Theorem monadic_creates : (* converse: EM_Forget creates U-split coequalizers,
     transported along any equivalence over D *) ...
   ```

7. `Monad/Lifting.v` — adjoint lifting along monadic functors, crude case: given
   monadic `U : C ⟶ D`, a functor between the bases with a left adjoint, and
   reflexive coequalizers upstairs, lift the left adjoint to the EM/monadic side.
   Scoped to the crude hypotheses (what applications use).
8. `Monad/Monadicity/Examples.v` — routine sanity: the identity monad's comparison
   is an equivalence; cross-reference note that Moore.v's header promises are now
   fully discharged (comment update commit).

**Completion checklist.**

| Deliverable | File |
|---|---|
| `SplitCoequalizer`, `split_coequalizer_is_coequalizer`, `functor_preserves_split` | Structure/Coequalizer/Split.v |
| reflexive pairs, `HasReflexiveCoequalizers` | Structure/Coequalizer/Reflexive.v |
| `EM_Comparison`, both triangle theorems, `Monadic` | Monad/Comparison.v |
| `EM_Forget` reflects isos; creates U-split coequalizers | Monad/Monadicity/BeckObjects.v |
| `crude_monadicity` | Monad/Monadicity/Crude.v |
| `CreatesUSplitCoequalizers`, `beck_monadicity`, `monadic_creates` | Monad/Monadicity/Beck.v |
| `adjoint_lifting` | Monad/Lifting.v |
| identity-monad witness | Monad/Monadicity/Examples.v |

`Print Assumptions` closed for `crude_monadicity`, `beck_monadicity`,
`adjoint_lifting`.

**Risks and fallbacks.** Beck-precise final assembly (transport of algebra structure
along created coequalizers) is among the campaign's longest proofs. QUARANTINE
(binding): land files 1-5 and 7-8 first; attempt `Beck.v` last. If it overruns the
phase budget, `Beck.v` moves WHOLE (statement + creation class + partial lemma
stack, all compiling, no holes — simply not yet concluding the top theorem, which is
then withheld from the commit) to a fast-follow on this branch or the head of the
Phase 10 branch, tracked as a MISSING escalation (Section 6.4) and ledger entry 17.
Crude monadicity and adjoint lifting are non-negotiable in-phase.

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

## 4. Coverage matrix

Every one of the seventeen items maps to at least one phase; no item is dropped.
Edge trims are in Section 5 only.

| # | Item | Phase(s) |
|---|------|----------|
| 1 | Equivalence of categories + transport | **Phase 5** |
| 2 | Comonad theory | **Phase 6** |
| 3 | F-(co)algebras, Lambek, Adamek | **Phase 7** |
| 4 | Fibrations and Grothendieck | **Phase 10** |
| 5 | Profunctors and coend calculus | **Phase 12** (Prof-as-Bicategory stretch: Phase 13, ledger 14) |
| 6 | Monadicity | **Phase 9** (EM/Kleisli adjunction prerequisites: Phase 6) |
| 7 | Adjoint functor theorems | **Phase 5** (RAPL/LAPC) + **Phase 14** (GAFT, SAFT) |
| 8 | Factorization systems, regular categories | **Phase 8** |
| 9 | Reflective subcategories and localization | **Phase 14** |
| 10 | Additive structure | **Phase 11** |
| 11 | Topos theory | **Phase 17** |
| 12 | Bicategory upgrade | **Phase 13** |
| 13 | Double categories | **Phase 15** |
| 14 | Enriched upgrade | **Phase 15** |
| 15 | Karoubi envelope | **Phase 8** |
| 16 | Lawvere theories | **Phase 16** |
| 17 | Operads and multicategories | **Phase 16** |
| — | Drinfeld centre (cross-cutting) | **Phase 12** (`Structure/Monoidal/Drinfeld.v`, distinguished from the premonoidal centre) |
| — | Star-autonomous (cross-cutting) | **Phase 12** (definition level; edges ledgered) |

Dependency spine: P5 → {P7, P8, P9, P10, P14, P16-corollaries}; P6 → P9; P8 →
{P9, P10-example, P11, P14, P15-cospans, P17}; P9 → P16 (file 5's comparison and
monadicity corollary); P11 → {P14, P16 (file 12's Comm example)}; P12 → (P13
stretch only); beyond the arrows listed, P13, P15, and P16 attach freely. Phases
6-8 are mutually reorderable, as are 11-13; the written order is the default.

## 5. Descope ledger

Justified trims at the EDGES of items; every item's core is delivered in full.
Fallbacks convert to ledger entries only through the Section 6.4 discipline — never
through `Admitted`.

1. **Sheafification** (item 11 edge). Requires the plus-construction (twice) over a
   genuine coverage; the in-tree `Site` carries one covering family per object and
   is acknowledged in its own comment as weaker than a coverage. Delivered instead:
   the category of sheaves with full/faithful inclusion and repleteness (Phase 17).
   Revisit only after a `Site` upgrade, which is its own campaign.
2. **Full finitary-monad ⇄ Lawvere equivalence** (item 16 edge; the item text marks
   it optional). Requires filtered colimits and a finitariness theory absent from
   the library. Delivered: induced monad, comparison functor, faithfulness of the
   underlying functor, and a monadicity corollary under supplied hypotheses, with
   the GAFT route named (Phase 16).
3. **Free operad** (item 17 edge; the item text marks it stretch). A rooted-tree
   term inductive with symmetric quotient — a phase of its own with no downstream
   consumer among the seventeen. Donor path named: the coloured-PROP term machinery
   (`Construction/ColouredPROP/*`) is the template when it is attempted.
4. **Star-autonomous beyond the definition** (cross-cutting). Delivered: the class,
   the contravariant dual functor, the transpose iso (Phase 12). Out: ⅋, linear
   distributivity, coherence theory — no consumer in-plan, and the axiomatics
   deserve their own design round.
5. **Day `Monoidal` bundling / pentagon** (item 5 edge, conditional). Day
   convolution with bifunctor, unit, unitors, associator, and naturality is
   committed; the pentagon and the bundled `@Monoidal [C, Sets]` instance are the
   staged tail of Phase 12 file 10 and move here only if the staging fallback
   fires.
6. **Abstract-target Fubini** (item 5 edge). Proved for Sets-valued functors, where
   (co)ends are computed; the abstract-D version has no in-plan consumer.
7. **Braiding on the Drinfeld centre** (conditional). `Drinfeld_Braided` is
   committed with a named fallback; ledgered only if the hexagons overrun Phase 12.
8. **Cospan double category coherence** (item 13 edge, conditional). Data, unit
   squares, and unitality committed; the pushout-associator pentagon is the
   quarantined proof (Phase 15 file 11).
9. **Monoidal double categories** (item 13 edge; the item text says "scoped as a
   note"). Header note in `Construction/Cospan/Double.v`.
10. **Mates beyond the bijection** (item 12 edge). The bijection and round trips
    are committed (Phase 13); the double category of adjunctions and pasting
    functoriality of mates is follow-on (and would slot into Phase 15's framework).
11. **V-enriched functor-category hom-objects and full V-weighted limits** (item 14
    edge). Needs ends in the base V plus underlying-category machinery. Delivered:
    the ordinary category of V-functors and V-natural transformations, V=Sets
    recovery at all three levels, V=2, and Sets-weighted limits with the conical
    recovery theorem — which is the item's named deliverable.
12. **A genuine abelian concrete instance** (item 10 edge). `CMon` semiadditive
    witness satisfies the item's parenthetical; abelian groups on setoids with
    quotient cokernels is a natural follow-on with no in-plan consumer.
13. **Sets as a one-level elementary topos** (item 11). Impossible at a single
    universe level in this library (`Instance/Sets.v:348`); replaced by the
    cross-universe theorem file plus the FinSet witness. A correctness stance, not
    a trim.
14. **Prof as a `Bicategory` instance** (items 5 x 12 junction). All ingredients
    land (Phase 12 laws + Phase 13 class); the instance itself is a stretch commit
    on Phase 13.
15. **Calculus of fractions** (item 9 edge; the item text permits the
    orthogonal-subcategory form). Delivered: orthogonal-subcategory localization
    with the universal property (Phase 14). Zig-zag fractions deferred.
16. **Sets `Regular` instance** (item 8 adjacency). Sets images land in Phase 8;
    Sets coequalizers arrive with Phase 12's quotient machinery; assembling
    `Regular Sets` is a cheap fast-follow after Phase 12, noted here so it is not
    forgotten.
17. **Conditional-stage register** (so nothing silently vanishes). Each staged
    fallback has a named artifact and destination: Phase 5 monoidal-transport
    coherence → Phase 12 rider commit; Phase 7 `AdamekData` discharge → Phase 7
    file 10 or fast-follow; Phase 8 stability-lemma routing; Phase 9 `Beck.v` →
    fast-follow or head of Phase 10 branch; Phase 10 round-trip conclusion; Phase
    11 abelian-factorization hypothesis-form; Phase 12 Day/Drinfeld tails; Phase 13
    general mates; Phase 14 `Comma_Complete`; Phase 15 cospan coherence; Phase 16
    symmetric mixin; Phase 17 FinSet `Closed`/`Topos` fast-follow. The no-holes
    rule applies to every fallback form: whatever lands compiles with zero
    admits/axioms; what does not land is withheld and escalated, never stubbed.

## 6. Execution mechanics

### 6.1 Branching and stacking

- One branch per phase: `johnw/ct-phase5` ... `johnw/ct-phase17`, each stacked on
  the previous phase's branch (Phase 5 stacks on the latest landed campaign branch,
  or `master` if the previous campaign has merged).
- Never rebase a phase branch after its PR is open except to restack on the updated
  parent; force-push only the branch being restacked.

### 6.2 Commit style

One atomic commit per file, with its `_CoqProject` line in the same commit
(alphabetical insertion). Conventional-commit subject, scope = principal module.
Example:

```
git add Theory/Equivalence.v _CoqProject
LEFTHOOK_EXCLUDE=nix-build,nix-check git commit -m 'feat(Equivalence): equivalence of categories via quasi-inverse

Adds EssentiallySurjective (split) and EquivalenceOfCategories over
Functor_Setoid, with conversions to/from ≅[Cat] and ≅[Fun], identity and
symmetry. No instance registration: quasi-inverses are never inferred.'
```

Comment-edit commits that retire in-tree promissory notes (Moore.v header,
Bicartesian.v:18, Adjunction.v RAPL note, Sets.v:348) ride WITH the commit that
delivers the artifact, in the same commit.

Each phase closes with `docs(CLAUDE): index the <topic> development` adding the
phase's Key Files entry to `CLAUDE.md`, following the existing Premonoidal/PROP
entry style.

Before pushing a phase: the full Section 2.2 gate, including
`nix build && nix flake check` and both Docker-version worktree builds
(Section 2.3).

### 6.3 PR stacking

- One PR per phase, targeting the previous phase's branch (or master for the first).
- PR description: the phase's checklist as a task list with each row's grep output
  pasted; any resequencing decisions; any Section 6.4 escalations in a dedicated
  `## MISSING` section.
- Do not merge out of order. After a parent merges, restack the children.

### 6.4 When a checklist item resists proof (delete-nothing / MISSING escalation)

Binding discipline, in order:

1. **Attempt honestly**, including the phase's named fallback for that item. The
   fallback is pre-authorized by this plan; executing it needs no further sign-off,
   only a note in the PR description and, where the plan says so, a ledger-entry-17
   update to this document (commit the doc change in the phase branch).
2. **Never** commit `Admitted`, `admit`, `Axiom`, `Parameter`, `Conjecture`, or
   `Unset ... Checking` — under any circumstances, including fallback forms. Never
   weaken a statement silently (changing a theorem's meaning requires a visible
   note in both the file header and the PR).
3. If the item still resists: **withhold the file (or the unproven tail of it) from
   the phase's commits** — everything committed compiles hole-free — and record the
   escalation in the PR description under `## MISSING`, one line per item, format:

   ```
   MISSING: beck_monadicity — obstruction: transport of algebra structure along
   created coequalizers exceeds phase budget after N attempts — destination:
   fast-follow on johnw/ct-phase9 — plan updated: ledger entry 17.
   ```

4. Update Section 5 entry 17 of this document with the same line (dated), so the
   plan remains the single source of truth for what is outstanding.
5. **Delete nothing**: the deliverable stays in this plan and in the checklist
   (marked MISSING in the PR, not removed), and the retry destination is named. A
   phase may merge with MISSING items only if every committed file passes the full
   gate and the maintainer accepts the PR with the MISSING section visible.

### 6.5 Adversarial per-file review

Before opening the phase PR, re-review every new file against this hunt list:

- Vacuous content: instances satisfied trivially because a hypothesis is
  unsatisfiable or a statement quantifies over an empty type; universal properties
  stated with the mediator on the wrong side; `∃!` whose predicate ignores its
  argument.
- Variance and orientation: op-category components, `to`/`from` of isos, left vs
  right adjoint conventions (`F : D ⟶ C` is the LEFT adjoint in `F ⊣ U`).
- Setoid discipline: any `=` on morphisms; missing `Proper` instances; `Prop`
  where proof-relevant `Type` is required (e.g. `le` vs `le_t`).
- Universe hygiene: `Print Universes` on the phase's flagged files; no accidental
  `Instance` registration of transports/constructions.
- Comment vocabulary (rule 2.4.10) and `Proof using` correctness (rule 2.4.4).
- Checklist audit: run every grep in the phase's checklist table and the
  `Print Assumptions` command for every principal artifact, pasting outputs into
  the PR.

Findings are fixed before the PR opens; anything that cannot be fixed follows
Section 6.4.
