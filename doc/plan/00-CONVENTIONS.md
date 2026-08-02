# Conventions and Gates — binding for every phase (7–17)

> **AI executor: read this file in full before starting any phase.** It is the
> shared, binding preamble. Each `phase-NN-*.md` work order assumes these rules
> and does not repeat them. Extracted verbatim from the master plan
> `doc/classical-completion-plan.md` (§2 conventions, §6 execution mechanics, §4
> coverage matrix, §5 descope ledger). Phases 5 and 6 were executed against these
> rules and are DONE (PRs #195, #196); the concrete lessons from that execution
> are in `00-INDEX.md` under "Execution lessons".

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

---

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

